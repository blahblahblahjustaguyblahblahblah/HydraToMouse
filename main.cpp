// Hydra-Mouse: замена sixense.dll, эмулирующая Sixense-контроллеры мышью и клавиатурой
// вместо Razer Hydra / SteamVR. Основано на CrossVR/Hydra-OpenVR (main.cpp),
// GetDeviceToAbsoluteTrackingPose заменён на MouseThreadFunc.

#define NOMINMAX
#include <sixense.h>
#include <sixense_math.hpp>
#include <windows.h>
#include <hidusage.h>
#include <algorithm>
#include <deque>
#include <thread>
#include <mutex>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdio>

#define SIXENSE_MAX_HISTORY 50

// ------------------------------------------------------------------
// Совместимость со старой/новой структурой (как в оригинале)
// ------------------------------------------------------------------
typedef struct _sixenseControllerDataOld {
    float pos[3];
    float rot_mat[3][3];
    unsigned char joystick_x;
    unsigned char joystick_y;
    unsigned char trigger;
    unsigned int buttons;
    unsigned char sequence_number;
    float rot_quat[4];
    unsigned short firmware_revision;
    unsigned short hardware_revision;
    unsigned short packet_type;
    unsigned short magnetic_frequency;
    int enabled;
    int controller_index;
    unsigned char is_docked;
    unsigned char which_hand;
} sixenseControllerDataOld;

typedef struct _sixenseAllControllerDataOld {
    sixenseControllerDataOld controllers[4];
} sixenseAllControllerDataOld;

#ifdef SIXENSE_LEGACY
typedef sixenseAllControllerDataOld compatAllControllerData;
typedef sixenseControllerDataOld compatControllerData;
#else
typedef sixenseAllControllerData compatAllControllerData;
typedef sixenseControllerData compatControllerData;
#endif

// ------------------------------------------------------------------
// Глобальное состояние эмуляции мышью
// ------------------------------------------------------------------
static std::atomic<bool> g_emulationActive{ false };   // toggle по Q
static std::atomic<bool> g_running{ false };
static std::atomic<long long> g_enableEpochMs{ 0 };    // время последнего включения (мс, steady_clock)
static std::atomic<bool> g_enterKeyDown{ false };      // Enter зажат прямо сейчас (для анлок+калибровка перед Start)
static std::atomic<bool> g_pendingDisable{ false };    // Q нажали на выключение — ждём, пока доиграет импульс SIXENSE_BUTTON_1

// ------------------------------------------------------------------
// Диагностическое логирование в консоль. Печатаем только первые
// LOG_WINDOW_MS миллисекунд после каждого включения Q — чтобы поймать
// момент, когда начинается самопроизвольная ходьба/телекинез.
// ------------------------------------------------------------------
static const long long LOG_WINDOW_MS = 5000;

static long long NowMs()
{
    return std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now().time_since_epoch()).count();
}

static bool InLogWindow()
{
    long long epoch = g_enableEpochMs.load();
    if (epoch == 0) return false;
    long long dt = NowMs() - epoch;
    return dt >= 0 && dt <= LOG_WINDOW_MS;
}


// Позиция/поворот виртуального контроллера (индекс 0 — "активная рука")
static std::mutex g_input_mutex;
static float g_pos[3]      = { 0.0f, 0.0f, 0.0f };   // мм, локальные смещения от нейтральной точки
static float g_yaw         = 0.0f;                    // вращение колесом (радианы) — используется как "roll" реального контроллера
static float g_trigger     = 0.0f;                    // 0..1, ЛКМ = grab/drag
static unsigned int g_buttons = 0;
static float g_moveX       = 0.0f;                    // -1..1, A/D — стик контроллера (стрейф)
static float g_moveY       = 0.0f;                    // -1..1, W/S — стик контроллера (вперёд/назад)
static bool g_keyW = false, g_keyA = false, g_keyS = false, g_keyD = false;

// Настройки чувствительности — подгоняются опытным путём
static const float kMouseToMm   = 1.2f;   // пикселей -> мм смещения по X/Y
static const float kWheelToMm   = 15.0f;  // один "щелчок" колеса -> мм по Z (push/pull)
static const float kWheelToRad  = 0.12f;  // один "щелчок" колеса -> радианы поворота (если зажат Shift)
static const float kPosLimit    = 250.0f; // ограничение смещения по каждой оси, мм

// ------------------------------------------------------------------
// Низкоуровневый хук мыши/клавиатуры
// ------------------------------------------------------------------
static HHOOK g_mouseHook = nullptr;
static HHOOK g_keyboardHook = nullptr;

static void SimulateEKey()
{
    // Небольшая задержка нужна некоторым играм:
    // они игнорируют искусственный E прямо в момент закрытия режима.
    std::this_thread::sleep_for(std::chrono::milliseconds(30));

    INPUT input[2] = {};

    input[0].type = INPUT_KEYBOARD;
    input[0].ki.wScan = MapVirtualKeyA('E', MAPVK_VK_TO_VSC);
    input[0].ki.dwFlags = KEYEVENTF_SCANCODE;

    input[1].type = INPUT_KEYBOARD;
    input[1].ki.wScan = MapVirtualKeyA('E', MAPVK_VK_TO_VSC);
    input[1].ki.dwFlags = KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP;

    UINT result = SendInput(2, input, sizeof(INPUT));

    printf("[HydraMouse] Simulate E SendInput result=%u\\n", result);
    fflush(stdout);
}


static void ClampPos()
{
    for (int i = 0; i < 3; i++)
        g_pos[i] = std::max(-kPosLimit, std::min(kPosLimit, g_pos[i]));
}

static LRESULT CALLBACK LowLevelMouseProc(int nCode, WPARAM wParam, LPARAM lParam)
{
    if (nCode == HC_ACTION && g_emulationActive.load())
    {
        MSLLHOOKSTRUCT* info = (MSLLHOOKSTRUCT*)lParam;

        switch (wParam)
        {
        case WM_MOUSEMOVE:
        {
            // Позицию больше не считаем здесь по абсолютным координатам курсора —
            // это раньше требовало SetCursorPos-рецентровки и вызывало накопление
            // мелкой систематической ошибки округления координат каждый кадр,
            // из-за чего g_pos незаметно "уползал" за 1-2 секунды до упора
            // (kPosLimit) даже без движения мыши — игра трактовала это как
            // полностью вытянутую вперёд руку и включала ходьбу/телекинез.
            // Реальные относительные дельты мыши теперь читаются через Raw Input
            // (см. RawInputWndProc) — они приходят напрямую от драйвера и не
            // зависят от абсолютной позиции курсора вообще.
            return 1; // съедаем исходное событие (камера в игре не должна вращаться)
        }
        case WM_MOUSEWHEEL:
        {
            short delta = GET_WHEEL_DELTA_WPARAM(info->mouseData);
            float clicks = delta / (float)WHEEL_DELTA;

            std::lock_guard<std::mutex> lk(g_input_mutex);
            bool rotateMode = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;
            if (rotateMode)
                g_yaw += clicks * kWheelToRad;
            else
            {
                g_pos[2] -= clicks * kWheelToMm; // инвертированное колесо: вверх/вниз поменяны местами
                ClampPos();
            }
            return 1;
        }
        case WM_LBUTTONDOWN:
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);
            g_trigger = 0.0f; // Q больше не держит trigger зажатым, чтобы не стрелял портал
            g_buttons |= SIXENSE_BUTTON_BUMPER; // используем как "grab" — уточняется опытным путём
            return 1;
        }
        case WM_LBUTTONUP:
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);
            g_trigger = 0.0f;
            g_buttons &= ~SIXENSE_BUTTON_BUMPER;
            return 1;
        }
        default:
            break;
        }
    }
    return CallNextHookEx(g_mouseHook, nCode, wParam, lParam);
}

static LRESULT CALLBACK LowLevelKeyboardProc(int nCode, WPARAM wParam, LPARAM lParam)
{
    static bool qHeld = false; // общий для KEYDOWN/KEYUP, а не локальный в одном блоке

    if (nCode == HC_ACTION)
    {
        KBDLLHOOKSTRUCT* info = (KBDLLHOOKSTRUCT*)lParam;
        if (info->vkCode == 'Q' && wParam == WM_KEYDOWN && !(info->flags & LLKHF_INJECTED))
        {
            if (!qHeld)
            {
                qHeld = true;

                if (!g_emulationActive.load())
                {
                    // Включаем — как и раньше, мгновенно.
                    g_emulationActive.store(true);
                    g_enableEpochMs.store(NowMs());
                    printf("[HydraMouse] Q: ENABLED at t=0ms, starting 5s diagnostic log\n");
                    fflush(stdout);

                    {
                        std::lock_guard<std::mutex> lk(g_input_mutex);
                        g_pos[0] = g_pos[1] = g_pos[2] = 0.0f;
                        g_keyW = g_keyA = g_keyS = g_keyD = false;
                        g_moveX = g_moveY = 0.0f;
                        g_buttons = 0;
                        g_trigger = 0.0f;
                    }
                    ShowCursor(FALSE);
                }
                else if (!g_pendingDisable.load())
                {
                    // Выключаем — НЕ сразу. Просим поток данных сыграть полный
                    // импульс SIXENSE_BUTTON_1 (кнопка отпускания захвата) и
                    // только когда он ПОЛНОСТЬЮ доиграет — тогда уже реально
                    // выключить g_emulationActive, сбросить состояние и вернуть
                    // курсор. Раньше g_emulationActive гасился мгновенно по
                    // нажатию Q, из-за чего импульс мог не успеть/не долететь
                    // до игры вовремя. Если Q уже ждёт отключения — повторные
                    // нажатия игнорируем, пока импульс не доиграет.
                    g_pendingDisable.store(true);
                    printf("[HydraMouse] Q: DISABLE REQUESTED, playing SIXENSE_BUTTON_1 release pulse first\n");
                    fflush(stdout);
                }
            }
            return 1; // не даём Q дойти до игры, если это конфликтует с другими биндами
        }
        if (info->vkCode == 'Q' && wParam == WM_KEYUP)
        {
            qHeld = false; // отпустили — следующее нажатие снова сработает
            return 1;
        }


        // E во время Q: выключаем режим Q и повторяем E в игру
        if (info->vkCode == 'E' &&
            wParam == WM_KEYDOWN &&
            !(info->flags & LLKHF_INJECTED))
        {
            if (g_emulationActive.load())
            {
                printf("[HydraMouse] E pressed during Q: disabling Q and replaying E\n");
                fflush(stdout);

                g_emulationActive.store(false);
                g_pendingDisable.store(false);

                {
                    std::lock_guard<std::mutex> lk(g_input_mutex);
                    g_pos[0] = g_pos[1] = g_pos[2] = 0.0f;
                    g_keyW = g_keyA = g_keyS = g_keyD = false;
                    g_moveX = g_moveY = 0.0f;
                    g_buttons = 0;
                    g_trigger = 0.0f;
                }

                ShowCursor(TRUE);

                SimulateEKey();

                return 1;
            }
        }

        // WASD/Space/Ctrl -> стик и кнопки контроллера. В motion-режиме Portal 2
        // читает перемещение из джойстика контроллера, а не из клавиатуры напрямую,
        // поэтому одной прокачки клавиш до игры недостаточно — нужно ещё и наполнить
        // joystick_x/joystick_y и кнопки прыжка/приседа. Событие НЕ съедаем (не return 1),
        // чтобы клавиши всё равно доходили до игры как обычно, если она их тоже слушает.
        //
        // ВАЖНО: состояние клавиш отслеживаем ВСЕГДА, а не только пока g_emulationActive
        // истинно. Иначе если клавиша отпускается уже после выключения режима (или была
        // зажата ещё до включения), KEYUP/KEYDOWN для неё не долетает до этого блока —
        // и в g_keyA/g_keyS остаётся "протухшее" true с прошлой сессии, из-за чего при
        // следующем включении Q персонаж внезапно "едет" сам по себе (будто зажаты A/S).
        // В джойстик/кнопки контроллера это состояние всё равно попадает только когда
        // g_emulationActive реально включён — см. sixenseThreadFunc.
        if (!(info->flags & LLKHF_INJECTED))
        {
            bool isDown = (wParam == WM_KEYDOWN || wParam == WM_SYSKEYDOWN);
            bool isUp   = (wParam == WM_KEYUP || wParam == WM_SYSKEYUP);
            if (isDown || isUp)
            {
                bool handled = true;
                std::lock_guard<std::mutex> lk(g_input_mutex);
                switch (info->vkCode)
                {
                case 'W': g_keyW = isDown; break;
                case 'A': g_keyA = isDown; break;
                case 'S': g_keyS = isDown; break;
                case 'D': g_keyD = isDown; break;
                case VK_SPACE:
                    if (isDown) g_buttons |= SIXENSE_BUTTON_JOYSTICK; // прыжок — клик стика (уточнить опытным путём)
                    else        g_buttons &= ~SIXENSE_BUTTON_JOYSTICK;
                    break;
                case VK_CONTROL: case VK_LCONTROL: case VK_RCONTROL:
                    if (isDown) g_buttons |= SIXENSE_BUTTON_2; // присед — запасная кнопка (уточнить опытным путём)
                    else        g_buttons &= ~SIXENSE_BUTTON_2;
                    break;
                case VK_RETURN:
                    if (isDown) g_buttons |= SIXENSE_BUTTON_START; // Enter -> Start
                    else        g_buttons &= ~SIXENSE_BUTTON_START;
                    g_enterKeyDown.store(isDown); // отдельный флаг для анлок+калибровка-перед-Start в sixenseThreadFunc
                    break;
                default: handled = false; break;
                }
                if (handled)
                {
                    g_moveX = (g_keyD ? 1.0f : 0.0f) - (g_keyA ? 1.0f : 0.0f);
                    g_moveY = (g_keyW ? 1.0f : 0.0f) - (g_keyS ? 1.0f : 0.0f);
                }
            }
        }
    }
    return CallNextHookEx(g_keyboardHook, nCode, wParam, lParam);
}

static std::thread g_hookThread;
static HWND g_rawInputWnd = nullptr;

// ------------------------------------------------------------------
// Raw Input: относительные дельты мыши напрямую от драйвера, без
// какой-либо зависимости от абсолютной позиции системного курсора.
// Это устраняет фидбек-петлю, которая была в старом подходе
// (SetCursorPos + чтение позиции из низкоуровневого хука): там из-за
// округления координат каждый кадр набегала мелкая систематическая
// ошибка, которая за 1-2 секунды "уводила" g_pos в упор даже без
// движения мыши — и игра воспринимала это как полностью вытянутую
// вперёд руку (ходьба + телекинез сами по себе).
// ------------------------------------------------------------------
static LRESULT CALLBACK RawInputWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    if (msg == WM_INPUT)
    {
        UINT size = 0;
        GetRawInputData((HRAWINPUT)lParam, RID_INPUT, nullptr, &size, sizeof(RAWINPUTHEADER));
        if (size > 0 && size <= 256)
        {
            BYTE buffer[256];
            if (GetRawInputData((HRAWINPUT)lParam, RID_INPUT, buffer, &size, sizeof(RAWINPUTHEADER)) == size)
            {
                RAWINPUT* raw = (RAWINPUT*)buffer;
                if (raw->header.dwType == RIM_TYPEMOUSE &&
                    !(raw->data.mouse.usFlags & MOUSE_MOVE_ABSOLUTE) &&
                    g_emulationActive.load())
                {
                    LONG dx = raw->data.mouse.lLastX;
                    LONG dy = raw->data.mouse.lLastY;
                    if (dx != 0 || dy != 0)
                    {
                        std::lock_guard<std::mutex> lk(g_input_mutex);
                        g_pos[0] += dx * kMouseToMm;
                        g_pos[1] -= dy * kMouseToMm; // экранный Y растёт вниз, мировой "вверх" — наоборот
                        ClampPos();
                    }
                }
            }
        }
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

static bool InitRawInput(HINSTANCE hInst)
{
    static const wchar_t* kClassName = L"HydraMouseRawInputWnd";

    WNDCLASSEXW wc = {};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = RawInputWndProc;
    wc.hInstance = hInst;
    wc.lpszClassName = kClassName;
    RegisterClassExW(&wc); // если уже зарегистрирован — не страшно, просто игнорируем ошибку

    g_rawInputWnd = CreateWindowExW(0, kClassName, L"", 0, 0, 0, 0, 0,
                                     HWND_MESSAGE, nullptr, hInst, nullptr);
    if (!g_rawInputWnd)
        return false;

    RAWINPUTDEVICE rid = {};
    rid.usUsagePage = HID_USAGE_PAGE_GENERIC;
    rid.usUsage = HID_USAGE_GENERIC_MOUSE;
    rid.dwFlags = RIDEV_INPUTSINK; // получать данные, даже когда окно не в фокусе
    rid.hwndTarget = g_rawInputWnd;

    return RegisterRawInputDevices(&rid, 1, sizeof(rid)) == TRUE;
}

static void HookThreadFunc()
{
    HINSTANCE hInst = GetModuleHandle(nullptr);
    g_mouseHook = SetWindowsHookExW(WH_MOUSE_LL, LowLevelMouseProc, hInst, 0);
    g_keyboardHook = SetWindowsHookExW(WH_KEYBOARD_LL, LowLevelKeyboardProc, hInst, 0);
    InitRawInput(hInst);

    MSG msg;
    while (g_running.load())
    {
        if (PeekMessage(&msg, nullptr, 0, 0, PM_REMOVE))
        {
            TranslateMessage(&msg);
            DispatchMessage(&msg);
        }
        else
        {
            std::this_thread::sleep_for(std::chrono::milliseconds(2));
        }
    }

    if (g_mouseHook) UnhookWindowsHookEx(g_mouseHook);
    if (g_keyboardHook) UnhookWindowsHookEx(g_keyboardHook);
    if (g_rawInputWnd) DestroyWindow(g_rawInputWnd);
    g_mouseHook = nullptr;
    g_keyboardHook = nullptr;
    g_rawInputWnd = nullptr;
}

// ------------------------------------------------------------------
// Данные контроллеров (60 Hz, как ожидает игра)
// ------------------------------------------------------------------
static std::thread g_dataThread;
static std::mutex g_data_mutex;
static std::deque<compatAllControllerData> g_controller_data;

// sixense_utils::controller_manager ждёт СОБЫТИЕ "контроллер был в базе и выехал из неё"
// (is_docked: 1 -> 0), иначе показывает "Dock your controllers to start" вечно.
// Эмулируем: первые DOCK_FRAMES кадров считаем контроллеры лежащими в базе,
// затем один раз "вынимаем" их — менеджер ловит переход и снимает оверлей.
static const int DOCK_FRAMES = 90; // ~1.5 сек при 60 "кадрах"/сек

// После докинга менеджер ещё просит откалибровать полусферу: "наведите контроллер
// на базу и нажмите триггер". Реального железа нет — просто держим виртуальный
// триггер "нажатым" некоторое время сразу после докинга, чтобы калибровка
// прошла сама, без участия пользователя.
static const int CALIBRATE_FRAMES = 60;

// Мягкая калибровка: короткий импульс trigger вместо постоянного удержания
static const unsigned long SOFT_TRIGGER_PULSE_FRAMES = 3; // ~1 сек держим триггер "нажатым"

static void sixenseThreadFunc()
{
    auto interval = std::chrono::milliseconds(16); // "60 FPS" как у настоящего SDK
    unsigned long frames_since_enable = 0;
    unsigned long frames_since_start = 0; // НЕ зависит от Q — только для одноразовых докинга+калибровки контроллера 0
    bool wasEnabled = false;

    // --- Enter без включённого Q: сначала имитируем "анлок+калибровку" обоих
    // контроллеров (не трогая настоящее состояние докинга ниже), затем даём
    // пройти Start (он и так проходит через маску SIXENSE_BUTTON_START, пока
    // Q выключен), а как только последовательность отыграна — просто перестаём
    // её форсировать, и is_docked обоих контроллеров сам возвращается к тому,
    // что диктуют обычные формулы (currently_docked_c0/c1) — то есть "как было
    // до" Enter, без ручного сохранения/восстановления состояния.
    bool enterSeqActive = false;
    unsigned long enterSeqFrame = 0;
    static const unsigned long ENTER_CALIB_FRAMES = 60; // ~1с анлок + держим триггер калибровки
    static const unsigned long ENTER_HOLD_FRAMES  = 20; // ~0.3с держим анлок, пока Start долетает до игры
    static const unsigned long ENTER_TOTAL_FRAMES = ENTER_CALIB_FRAMES + ENTER_HOLD_FRAMES;

    // --- Отложенное выключение Q: сначала полностью доигрываем импульс
    // SIXENSE_BUTTON_1 (кнопка отпускания захвата), и только потом реально
    // гасим g_emulationActive. Пока импульс идёт, Q фактически ещё "включён".
    bool disablingInProgress = false;
    unsigned long disableFrame = 0;
    static const unsigned long RELEASE_PULSE_FRAMES = 20; // ~0.3с держим SIXENSE_BUTTON_1

    for (uint8_t sequence = 0; g_running.load(); sequence++)
    {
        bool enabledNow = g_emulationActive.load();
        if (enabledNow && !wasEnabled) frames_since_enable = 0; // включили — отыгрываем докинг+калибровку заново
        wasEnabled = enabledNow;

        // Докинг-пантомима (задержка DOCK_FRAMES + калибровочный триггер) для
        // контроллера 1 привязана к Q — это ожидаемый цикл "наведите левый
        // контроллер на базу". Контроллер 0 (реальная активная рука на мыши,
        // which_hand=2 — правая) — его докинг+калибровка тоже РОВНО ОДИН РАЗ
        // за весь процесс и больше никогда не повторяются, сколько бы раз ни
        // переключали Q, НО отсчёт окна запускается от МОМЕНТА ПЕРВОГО
        // ВКЛЮЧЕНИЯ Q, а не от старта программы — раньше окно было жёстко
        // привязано к frames_since_start и почти всегда успевало закрыться
        // ещё до того, как игра реально начинала слушать триггер (~1.3с
        // после Q), из-за чего появлялся запрос "нажмите trigger" на правом
        // контроллере.
        static bool c0_seq_started = false;
        static unsigned long frames_since_c0_start = 0;
        if (enabledNow && !c0_seq_started)
        {
            c0_seq_started = true;
            frames_since_c0_start = 0;
        }
        if (c0_seq_started) frames_since_c0_start++;

        unsigned char currently_docked_c1 =
            (!enabledNow) ? 1 :
            (frames_since_enable < DOCK_FRAMES ? 1 : 0);
        unsigned char currently_docked_c0 =
            (!c0_seq_started) ? 1 :
            (frames_since_c0_start < DOCK_FRAMES ? 1 : 0);
        bool autoCalibrateTrigger_c0 = false; // отключено: не нажимаем trigger автоматически
        // Контроллер 0 держим "включённым" на уровне протокола ВСЕГДА (как и
        // контроллер 1 ниже) — иначе игра игнорирует его data.buttons целиком,
        // и Enter/Start не работает, пока не нажат Q. Само же движение мышью/
        // клавишами по-прежнему применяется только пока enabledNow истинно —
        // см. обнуление pos/moveX/moveY/trigger чуть ниже.
        unsigned char currently_enabled = 1;
        // Триггер контроллера 1 нигде в геймплее не используется (это просто
        // "вторая рука"), НО удержание его "нажатым" постоянно (пока Q
        // включён) непреднамеренно совпадало с "зажатым триггером = grab/
        // телекинез" в игре — поэтому, как и для c0, держим его нажатым
        // только короткое окно CALIBRATE_FRAMES сразу после докинга, а потом
        // отпускаем.
        bool autoCalibrateTrigger = false; // отключено: Portal 2 не должен стрелять при калибровке
        if (enabledNow) frames_since_enable++;
        frames_since_start++;

        // --- Последовательность "Enter без Q": анлок+калибровка -> Start -> откат ---
        if (enabledNow)
        {
            // Q включили — это уже нормальный поток докинга/калибровки выше,
            // наша ручная последовательность больше не нужна и не должна мешать.
            enterSeqActive = false;
            enterSeqFrame = 0;
        }
        else if (g_enterKeyDown.load() && !enterSeqActive)
        {
            enterSeqActive = true;
            enterSeqFrame = 0;
            printf("[HydraMouse] Enter (Q выкл): анлок+калибровка обоих контроллеров перед Start\n");
            fflush(stdout);
        }

        if (enterSeqActive)
        {
            if (enterSeqFrame < ENTER_CALIB_FRAMES)
            {
                // Фаза 1: "выехали из базы" + держим виртуальный триггер калибровки
                currently_docked_c0 = 0;
                currently_docked_c1 = 0;
                autoCalibrateTrigger_c0 = false; // отключено: не зажимаем trigger во время Q-калибровки
                autoCalibrateTrigger = false; // отключено: не зажимаем trigger во время Q-калибровки
            }
            else if (enterSeqFrame < ENTER_TOTAL_FRAMES)
            {
                // Фаза 2: калибровка отпущена, но контроллеры ещё вне базы —
                // именно в эту фазу до игры и должен долететь Start (Enter).
                currently_docked_c0 = 0;
                currently_docked_c1 = 0;
            }
            else
            {
                // Готово: перестаём форсировать is_docked — дальше он снова
                // считается обычными формулами (для C1 это докинг обратно,
                // раз Q по-прежнему выключен; для C0 — как и было, "выехал").
                enterSeqActive = false;
                enterSeqFrame = 0;
                printf("[HydraMouse] Enter-последовательность завершена, состояние докинга возвращено к обычному\n");
                fflush(stdout);
            }
            if (enterSeqActive) enterSeqFrame++;
        }

        compatAllControllerData all_data = {};

        float pos[3], yaw, trigger, moveX, moveY;
        unsigned int buttons;
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);
            pos[0] = g_pos[0]; pos[1] = g_pos[1]; pos[2] = g_pos[2];
            yaw = g_yaw;
            trigger = g_trigger;
            buttons = g_buttons;
            moveX = g_moveX;
            moveY = g_moveY;
        }

        if (!enabledNow)
        {
            // Пока режим выключен, контроллер 0 репортится "включённым" (см. выше —
            // это нужно только чтобы Enter/Start доходил до игры), но мышь/WASD/
            // триггер не должны влиять на игру, пока Q не нажат — обнуляем всё,
            // кроме кнопки Start.
            pos[0] = pos[1] = pos[2] = 0.0f;
            yaw = 0.0f;
            trigger = 0.0f;
            moveX = moveY = 0.0f;
            buttons &= SIXENSE_BUTTON_START;
        }
        else
        {
            // Пока режим Q включён, ходьба с WASD полностью игнорируется —
            // перемещение теперь идёт только через мышь/контроллер, клавиши
            // W/A/S/D на джойстик контроллера больше не транслируются.
            moveX = moveY = 0.0f;
            // Телекинез (захват кубов) должен быть активен СРАЗУ при включении
            // Q, без необходимости жать ЛКМ — поэтому триггер c0 держим
            // постоянно "нажатым" (1.0) всё время, пока Q включён, а не только
            // пока реально зажат ЛКМ. Это не портит калибровку: калибровочное
            // окно (autoCalibrateTrigger_c0) — лишь разовая проверка "был ли
            // триггер нажат" в первые ~1.5с, и раз он теперь нажат ВСЁ время
            // Q, окно калибровки застаёт его нажатым точно так же, как и
            // раньше — просто без отпускания после.
            trigger = 0.0f; // никогда не держим trigger зажатым автоматически
        }

        // --- Отложенное выключение Q: пока идёт импульс SIXENSE_BUTTON_1,
        // g_emulationActive НЕ трогаем (он всё ещё true — enabledNow видит
        // это как "Q включён", реальные мышь/ЛКМ продолжают работать как
        // обычно), мы только форсируем SIXENSE_BUTTON_1 поверх этого. Как
        // только импульс полностью доиграет RELEASE_PULSE_FRAMES кадров —
        // ВОТ ТОГДА уже по-настоящему гасим Q: g_emulationActive=false,
        // сбрасываем состояние, возвращаем курсор. Это устраняет саму гонку,
        // из-за которой раньше SIXENSE_BUTTON_1 мог не долетать до игры —
        // Q больше не выключается раньше, чем импульс завершится.
        if (!disablingInProgress && g_pendingDisable.load() && enabledNow)
        {
            disablingInProgress = true;
            disableFrame = 0;
        }
        else if (!disablingInProgress && g_pendingDisable.load() && !enabledNow)
        {
            // Защита от гонки: если запрос на выключение пришёл, а режим на
            // самом деле не был включён — просто сбрасываем флаг, кнопку 1
            // не трогаем и никакого импульса не играем.
            g_pendingDisable.store(false);
        }
        if (disablingInProgress)
        {
           // buttons |= SIXENSE_BUTTON_1;
            disableFrame++;
            if (disableFrame >= RELEASE_PULSE_FRAMES)
            {
                disablingInProgress = false;
                disableFrame = 0;
                g_emulationActive.store(false);
                g_pendingDisable.store(false);
                {
                    std::lock_guard<std::mutex> lk(g_input_mutex);
                    g_pos[0] = g_pos[1] = g_pos[2] = 0.0f;
                    g_keyW = g_keyA = g_keyS = g_keyD = false;
                    g_moveX = g_moveY = 0.0f;
                    g_buttons = 0;
                    g_trigger = 0.0f;
                }
                ShowCursor(TRUE);
                printf("[HydraMouse] Q: DISABLED (после завершения импульса SIXENSE_BUTTON_1)\n");
                fflush(stdout);
            }
        }
        // ВАЖНО: калибровочный "нажатый триггер" для контроллера 1 привязан к Q
        // (frames_since_enable), а для контроллера 0 — к моменту ПЕРВОГО
        // включения Q (frames_since_c0_start, см. autoCalibrateTrigger_c0 выше) —
        // раньше он по ошибке подмешивался в общую переменную trigger, которая
        // идёт и в контроллер 0 (активная рука, управляемая реальным ЛКМ).
        // Из-за этого через ~1.5-2.5 сек после включения Q персонаж внезапно
        // "шёл"/что-то хватал, хотя ЛКМ не нажимался.
        // Здесь НЕ трогаем trigger — используем autoCalibrateTrigger/
        // autoCalibrateTrigger_c0 отдельно, каждый при заполнении своего data.

        // --- Принудительно гасим SIXENSE_BUTTON_1 первые FORCE_NO_BUTTON1_FRAMES
        // кадров (~2с) после включения Q. Это last-resort защита: аналогично
        // тому, как стик контроллера 1 принудительно держится в центре (127/127
        // для legacy) независимо от реального состояния — здесь так же жёстко
        // зануляем именно этот бит в buttons перед записью в data, чтобы игра
        // ни при каких обстоятельствах не могла прочитать кнопку 1 нажатой
        // сразу после включения — откуда бы фантомное нажатие ни бралось.
        static const unsigned long FORCE_NO_BUTTON1_FRAMES = 125; // ~2с при 60 FPS
        if (enabledNow && frames_since_enable < FORCE_NO_BUTTON1_FRAMES)
        {
            buttons &= ~SIXENSE_BUTTON_1;
        }

        sixenseMath::Vector3 axis(0.0f, 0.0f, 1.0f);
        sixenseMath::Matrix3 mat = sixenseMath::Matrix3::rotation(yaw, axis);

        // --- Контроллер 0: "активная рука", управляется мышью ---
        {
            compatControllerData& data = all_data.controllers[0];

            data.pos[0] = pos[0];
            data.pos[1] = pos[1];
            data.pos[2] = pos[2];

            for (int row = 0; row < 3; row++)
                for (int col = 0; col < 3; col++)
                    data.rot_mat[col][row] = mat[col][row];

#ifdef SIXENSE_LEGACY
            data.joystick_x = (uint8_t)(127 + moveX * 127.0f);
            data.joystick_y = (uint8_t)(127 + moveY * 127.0f);
            data.trigger = autoCalibrateTrigger_c0 ? (uint8_t)255 : (uint8_t)(trigger * 255.0f);
#else
            data.joystick_x = moveX;
            data.joystick_y = moveY;
            data.trigger = autoCalibrateTrigger_c0 ? 1.0f : trigger;
#endif
            data.buttons = buttons;
            data.sequence_number = sequence;

            sixenseMath::Quat quat(mat);
            data.rot_quat[0] = quat[0];
            data.rot_quat[1] = quat[1];
            data.rot_quat[2] = quat[2];
            data.rot_quat[3] = quat[3];

            data.firmware_revision = 0;
            data.hardware_revision = 0;
            data.packet_type = 1;
            data.magnetic_frequency = 0;
            data.enabled = currently_enabled;
            data.controller_index = 0;
            data.is_docked = currently_docked_c0;
            data.which_hand = 2; // правая — уточнить, если игра ждёт другую руку
#ifndef SIXENSE_LEGACY
            data.hemi_tracking_enabled = 1;
#endif
        }

        // --- Контроллер 1: нейтральная "вторая рука", всегда включён,
        //     чтобы карты не считали оборудование неполным ---
        {
            compatControllerData& data = all_data.controllers[1];
            data.pos[0] = data.pos[1] = data.pos[2] = 0.0f;
            data.rot_mat[0][0] = data.rot_mat[1][1] = data.rot_mat[2][2] = 1.0f;
            data.rot_quat[3] = 1.0f;
            data.enabled = currently_enabled;
            data.controller_index = 1;
            data.which_hand = 1;
            data.sequence_number = sequence;
            data.packet_type = 1;
            data.is_docked = currently_docked_c1;
#ifdef SIXENSE_LEGACY
            // ВАЖНО: joystick_x/joystick_y — unsigned char, нейтраль = 127, а НЕ 0!
            // all_data = {} зануляет структуру, и без явной установки здесь стик
            // "второй руки" читался как 0/0 — то есть как полностью отклонённый
            // в угол, а не как отпущенный. Ровно через DOCK_FRAMES+CALIBRATE_FRAMES
            // кадров после включения Q контроллер 1 "раскалибровывался" и игра
            // начинала это читать — отсюда самопроизвольная безостановочная
            // ходьба вправо-назад через несколько секунд после Q, даже когда
            // WASD никто не трогал.
            data.joystick_x = 127;
            data.joystick_y = 127;
            data.trigger = autoCalibrateTrigger ? (uint8_t)255 : (uint8_t)0;
#else
            // В float-протоколе 0.0f и так является центром стика — здесь баг
            // не проявлялся, но выставляем явно для симметрии и ясности.
            data.joystick_x = 0.0f;
            data.joystick_y = 0.0f;
            data.trigger = autoCalibrateTrigger ? 1.0f : 0.0f;
            data.hemi_tracking_enabled = 1;
#endif
        }

        {
            std::lock_guard<std::mutex> lk(g_data_mutex);
            g_controller_data.push_front(all_data);
            g_controller_data.pop_back();
        }

        if (InLogWindow() && (frames_since_enable % 4 == 0)) // ~15 логов/сек
        {
            const compatControllerData& c0 = all_data.controllers[0];
            const compatControllerData& c1 = all_data.controllers[1];
            printf("[HydraMouse][GEN] t=%lldms frame=%lu | C0: pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d | C1: trig=%.2f dock=%d calib=%d\n",
                NowMs() - g_enableEpochMs.load(), frames_since_enable,
                pos[0], pos[1], pos[2], trigger, buttons, (int)currently_enabled, (int)currently_docked_c0,
                (double)c1.trigger, (int)currently_docked_c1, (int)autoCalibrateTrigger);
            fflush(stdout);
        }

        std::this_thread::sleep_for(interval);
    }
}

// ------------------------------------------------------------------
// Экспорты Sixense SDK
// ------------------------------------------------------------------
SIXENSE_EXPORT int sixenseInit(void)
{
    for (int i = 0; i < SIXENSE_MAX_HISTORY; i++)
    {
        compatAllControllerData all_data = {};
        g_controller_data.push_back(all_data);
    }

    g_running = true;
    g_dataThread = std::thread(sixenseThreadFunc);
    g_hookThread = std::thread(HookThreadFunc);

    return SIXENSE_SUCCESS; // всегда успех — карта не должна отказываться грузиться
}

SIXENSE_EXPORT int sixenseExit(void)
{
    g_running = false;
    if (g_dataThread.joinable()) g_dataThread.join();
    if (g_hookThread.joinable()) g_hookThread.join();
    g_controller_data.clear();
    return SIXENSE_SUCCESS;
}

SIXENSE_EXPORT int sixenseGetMaxBases() { return 1; }
SIXENSE_EXPORT int sixenseSetActiveBase(int i) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseIsBaseConnected(int i)
{
    // База — отдельный физический слой, она не должна "пропадать" при Q,
    // иначе controller_manager считает это отключением и снова просит докинг.
    // Курсор/motion-режим регулируем ниже через IsControllerEnabled и data.enabled.
    if (InLogWindow())
    {
        static std::atomic<long> callCount{ 0 };
        if ((callCount.fetch_add(1) % 30) == 0)
        {
            printf("[HydraMouse][CALL] t=%lldms sixenseIsBaseConnected(%d) -> 1\n", NowMs() - g_enableEpochMs.load(), i);
            fflush(stdout);
        }
    }
    return 1;
}
SIXENSE_EXPORT int sixenseGetMaxControllers(void) { return SIXENSE_MAX_CONTROLLERS; }

SIXENSE_EXPORT int sixenseIsControllerEnabled(int which)
{
    // ВАЖНО: держим "присутствие" контроллеров стабильным всегда, независимо от Q.
    // Если репортить сюда 0 при выключении, движок/SteamVR может воспринять это
    // как физическое отключение устройства и зависнуть в ожидании переподключения.
    // Переключение поведения (motion vs обычная мышь) регулируем через data.enabled
    // в потоке данных ниже — это движок обычно просто читает, не блокируясь.
    int result = (which < 2) ? 1 : 0;
    if (InLogWindow())
    {
        static std::atomic<long> callCount{ 0 };
        if ((callCount.fetch_add(1) % 30) == 0)
        {
            printf("[HydraMouse][CALL] t=%lldms sixenseIsControllerEnabled(%d) -> %d\n", NowMs() - g_enableEpochMs.load(), which, result);
            fflush(stdout);
        }
    }
    return result;
}

SIXENSE_EXPORT int sixenseGetNumActiveControllers() { return 2; }
SIXENSE_EXPORT int sixenseGetHistorySize() { return SIXENSE_MAX_HISTORY; }

SIXENSE_EXPORT int sixenseGetData(int which, int index_back, sixenseControllerData* data)
{
    if (!data || index_back >= SIXENSE_MAX_HISTORY)
        return SIXENSE_FAILURE;
    std::lock_guard<std::mutex> lk(g_data_mutex);
    *(compatControllerData*)data = g_controller_data[index_back].controllers[which];
    // Всегда SUCCESS: "включён/выключен" сообщается через data.enabled и
    // IsControllerEnabled/NumActiveControllers, а не через отказ чтения —
    // иначе движок, крутящийся в ожидании SUCCESS, зависает намертво при Q=off.
    if (InLogWindow())
    {
        static std::atomic<long> callCount{ 0 };
        if ((callCount.fetch_add(1) % 10) == 0)
        {
            printf("[HydraMouse][CALL] t=%lldms sixenseGetData(which=%d) pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d\n",
                NowMs() - g_enableEpochMs.load(), which, data->pos[0], data->pos[1], data->pos[2],
                (double)data->trigger, data->buttons, data->enabled, data->is_docked);
            fflush(stdout);
        }
    }
    return SIXENSE_SUCCESS;
}

SIXENSE_EXPORT int sixenseGetAllData(int index_back, sixenseAllControllerData* data)
{
    if (!data || index_back >= SIXENSE_MAX_HISTORY)
        return SIXENSE_FAILURE;
    std::lock_guard<std::mutex> lk(g_data_mutex);
    *(compatAllControllerData*)data = g_controller_data[index_back];
    return SIXENSE_SUCCESS;
}

SIXENSE_EXPORT int sixenseGetNewestData(int which, sixenseControllerData* data)
{
    if (!data)
        return SIXENSE_FAILURE;
    std::lock_guard<std::mutex> lk(g_data_mutex);
    *(compatControllerData*)data = g_controller_data[0].controllers[which];
    if (InLogWindow())
    {
        static std::atomic<long> callCount{ 0 };
        if ((callCount.fetch_add(1) % 10) == 0)
        {
            printf("[HydraMouse][CALL] t=%lldms sixenseGetNewestData(which=%d) pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d\n",
                NowMs() - g_enableEpochMs.load(), which, data->pos[0], data->pos[1], data->pos[2],
                (double)data->trigger, data->buttons, data->enabled, data->is_docked);
            fflush(stdout);
        }
    }
    return SIXENSE_SUCCESS;
}

SIXENSE_EXPORT int sixenseGetAllNewestData(sixenseAllControllerData* data)
{
    if (!data)
        return SIXENSE_FAILURE;
    std::lock_guard<std::mutex> lk(g_data_mutex);
    *(compatAllControllerData*)data = g_controller_data[0];
    if (InLogWindow())
    {
        static std::atomic<long> callCount{ 0 };
        if ((callCount.fetch_add(1) % 10) == 0)
        {
            const compatControllerData& c0 = *(compatControllerData*)&data->controllers[0];
            const compatControllerData& c1 = *(compatControllerData*)&data->controllers[1];
            printf("[HydraMouse][CALL] t=%lldms sixenseGetAllNewestData C0: pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d | C1: trig=%.2f en=%d dock=%d\n",
                NowMs() - g_enableEpochMs.load(),
                c0.pos[0], c0.pos[1], c0.pos[2], (double)c0.trigger, c0.buttons, c0.enabled, c0.is_docked,
                (double)c1.trigger, c1.enabled, c1.is_docked);
            fflush(stdout);
        }
    }
    return SIXENSE_SUCCESS;
}

SIXENSE_EXPORT int sixenseSetHemisphereTrackingMode(int which_controller, int state) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseGetHemisphereTrackingMode(int which_controller, int* state) { if (state) *state = 1; return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseAutoEnableHemisphereTracking(int which_controller) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseSetHighPriorityBindingEnabled(int on_or_off) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseGetHighPriorityBindingEnabled(int* on_or_off) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseTriggerVibration(int controller_id, int duration_100ms, int pattern_id) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseSetFilterEnabled(int on_or_off) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseGetFilterEnabled(int* on_or_off) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseSetFilterParams(float near_range, float near_val, float far_range, float far_val) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseGetFilterParams(float* near_range, float* near_val, float* far_range, float* far_val) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseSetBaseColor(unsigned char red, unsigned char green, unsigned char blue) { return SIXENSE_SUCCESS; }
SIXENSE_EXPORT int sixenseGetBaseColor(unsigned char* red, unsigned char* green, unsigned char* blue) { return SIXENSE_SUCCESS; }

extern "C"
{
    SIXENSE_EXPORT int sixenseSetDebugParam() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetDebugParam() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseSetCalibrationEnabled() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetCalibrationEnabled() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseSetHemisphereVector() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetHemisphereVector() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetRawData() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetRawDataSingle() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetSignalMatrix() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetSignalQuality() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseSetTestMode() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseGetTestMode() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixensePlaybackLogFile() { return SIXENSE_SUCCESS; }
    SIXENSE_EXPORT int sixenseSendTestCommand() { return SIXENSE_SUCCESS; }
}