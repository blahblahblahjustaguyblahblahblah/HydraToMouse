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
#include <cwchar>
#include <cstdarg>
#include <cstring>
#include <ctime>
#include <string>
#include <cctype>

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
static std::atomic<bool> g_pendingDisable{ false };    // Q нажали на выключение (или отпустили ЛКМ/ПКМ) — ждём, пока доиграет пауза выключения

// Отпускание ЛКМ/ПКМ (grab-hold триггер) больше НЕ обнуляет g_trigger/
// g_triggerLeft/heldYaw/dirX/dirY и т.п. отдельным коротким импульсом.
// Вместо этого отпускание любой из кнопок мыши запрашивает ПОЛНОЕ выключение
// режима Q — тот же путь, что и повторное нажатие клавиши Q (g_pendingDisable,
// см. sixenseThreadFunc). Реальный сброс всех данных контроллера, включая
// триггеры, происходит только после того, как это выключение полностью
// доиграет (RELEASE_PULSE_FRAMES кадров) — до этого момента триггер
// продолжает репортиться игре нажатым, как и раньше.

// ------------------------------------------------------------------
// Фокус окна игры. Хуки WH_KEYBOARD_LL/WH_MOUSE_LL глобальные и видят
// ВСЕ клавиши/мышь в системе, даже когда игра свёрнута/не в фокусе.
// Поэтому явно проверяем, что foreground-окно принадлежит нашему же
// процессу (игре), и не обрабатываем ввод, если это не так.
// ------------------------------------------------------------------
static std::atomic<bool> g_gameFocused{ true };
static std::atomic<bool> g_cursorHiddenByUs{ false }; // чтобы не разбалансировать счётчик ShowCursor

static bool IsGameWindowForeground()
{
    HWND fg = GetForegroundWindow();
    if (!fg) return false;
    DWORD fgPid = 0;
    GetWindowThreadProcessId(fg, &fgPid);
    return fgPid == GetCurrentProcessId();
}

// Прячем курсор, только если окно игры реально в фокусе прямо сейчас.
static void HideCursorIfFocused()
{
    if (g_gameFocused.load() && !g_cursorHiddenByUs.exchange(true))
        ShowCursor(FALSE);
}

// Возвращаем курсор — безопасно вызывать в любой момент, даже если он уже виден.
static void RestoreCursor()
{
    if (g_cursorHiddenByUs.exchange(false))
        ShowCursor(TRUE);
}

// ------------------------------------------------------------------
// Конфигурация из HydraMouse.cfg (лежит рядом с DLL). Формат — простые
// строки "Ключ = значение" (true/false), как в присланном примере:
//   DebugConsole = false
//   Debug3DView = false
//   Log = false
// Если файла нет — считаем все флаги false (поведение по умолчанию,
// без консоли/3D-окна/лог-файла — тихая работа).
// ------------------------------------------------------------------
static std::atomic<bool> g_cfgDebugConsole{ false };
static std::atomic<bool> g_cfgDebug3DView{ false };
static std::atomic<bool> g_cfgLog{ false };

static std::mutex g_logFileMutex;
static FILE* g_logFile = nullptr;

// Путь к каталогу, где лежит EXE игры (GetModuleFileName(NULL, ...) —
// nullptr-хендл всегда означает главный исполняемый модуль процесса,
// т.е. сам .exe игры, а не эту DLL).
// Функция названа GetGameExeDirectory (а не GetDllDirectory), потому что
// GetDllDirectory — это имя настоящей WinAPI-функции (GetDllDirectoryA/W
// в windows.h), и совпадение имён ломает компиляцию (C2660/C2440/E0299).
static std::string GetGameExeDirectory()
{
    char path[MAX_PATH] = {};
    GetModuleFileNameA(nullptr, path, MAX_PATH);

    std::string full(path);
    size_t pos = full.find_last_of("\\/");
    if (pos == std::string::npos)
        return std::string();
    return full.substr(0, pos + 1);
}

static std::string Trim(const std::string& s)
{
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == std::string::npos) return std::string();
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
}

static bool ParseBool(const std::string& v)
{
    std::string lower;
    for (char c : v) lower += (char)std::tolower((unsigned char)c);
    return lower == "true" || lower == "1" || lower == "yes" || lower == "on";
}

// Читает HydraMouse.cfg рядом с DLL. Если файла нет — все флаги остаются
// false (значения по умолчанию, заданные при объявлении атомиков выше).
static void LoadConfig()
{
    std::string cfgPath = GetGameExeDirectory() + "HydraMouse.cfg";
    FILE* fp = nullptr;
    fopen_s(&fp, cfgPath.c_str(), "r");
    if (!fp)
        return; // файла нет — всё остаётся false

    char lineBuf[512];
    while (fgets(lineBuf, sizeof(lineBuf), fp))
    {
        std::string line(lineBuf);
        size_t commentPos = line.find_first_of(";#");
        if (commentPos != std::string::npos)
            line = line.substr(0, commentPos);

        size_t eq = line.find('=');
        if (eq == std::string::npos)
            continue;

        std::string key = Trim(line.substr(0, eq));
        std::string val = Trim(line.substr(eq + 1));
        if (key.empty())
            continue;

        if (_stricmp(key.c_str(), "DebugConsole") == 0)
            g_cfgDebugConsole.store(ParseBool(val));
        else if (_stricmp(key.c_str(), "Debug3DView") == 0)
            g_cfgDebug3DView.store(ParseBool(val));
        else if (_stricmp(key.c_str(), "Log") == 0)
            g_cfgLog.store(ParseBool(val));
    }
    fclose(fp);
}

// Открывает HydraMouse.log рядом с DLL в режиме перезаписи ("w") —
// каждая новая сессия (загрузка DLL) начинает файл с чистого листа.
// Пишем в бинарном режиме с BOM UTF-8 в начале, чтобы редакторы (в т.ч.
// Блокнот) корректно отображали кириллицу в логе.
static void OpenLogFile()
{
    if (!g_cfgLog.load())
        return;

    std::string logPath = GetGameExeDirectory() + "HydraMouse.log";
    std::lock_guard<std::mutex> lk(g_logFileMutex);
    fopen_s(&g_logFile, logPath.c_str(), "wb");
    if (g_logFile)
    {
        static const unsigned char utf8Bom[3] = { 0xEF, 0xBB, 0xBF };
        fwrite(utf8Bom, 1, 3, g_logFile);
        fflush(g_logFile);
    }
}

static void CloseLogFile()
{
    std::lock_guard<std::mutex> lk(g_logFileMutex);
    if (g_logFile)
    {
        fclose(g_logFile);
        g_logFile = nullptr;
    }
}

// Замена HydraLog() по всему файлу: печатает в консоль (если DebugConsole
// включён в cfg) и/или пишет в HydraMouse.log (если Log включён), каждая
// строка — с меткой времени. Если оба флага выключены — no-op, ничего
// не считается и не форматируется зря.
static void HydraLogV(const char* fmt, va_list args)
{
    bool toConsole = g_cfgDebugConsole.load();
    bool toFile = g_cfgLog.load();
    if (!toConsole && !toFile)
        return;

    char msg[2048];
    vsnprintf(msg, sizeof(msg), fmt, args);

    if (toConsole)
    {
        fputs(msg, stdout);
        fflush(stdout);
    }

    if (toFile)
    {
        std::lock_guard<std::mutex> lk(g_logFileMutex);
        if (g_logFile)
        {
            time_t t = time(nullptr);
            tm localTm;
            localtime_s(&localTm, &t);
            auto nowMs = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::system_clock::now().time_since_epoch()).count() % 1000;

            char stamp[64];
            snprintf(stamp, sizeof(stamp), "[%02d:%02d:%02d.%03lld] ",
                localTm.tm_hour, localTm.tm_min, localTm.tm_sec, (long long)nowMs);

            fputs(stamp, g_logFile);
            fputs(msg, g_logFile);
            fflush(g_logFile);
        }
    }
}

static void HydraLog(const char* fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    HydraLogV(fmt, args);
    va_end(args);
}

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
static float g_pos[3] = { 0.0f, 0.0f, 250.0f };   // мм, локальные смещения от нейтральной точки (idle Z = 250 мм)
static float g_yaw = 0.0f;                    // вращение колесом (радианы) — используется как "roll" реального контроллера
static float g_heldYaw = 0.0f;                // доп. вращение правого контроллера колесом, пока зажата ЛКМ или ПКМ; обнуляется при отпускании
// Пока зажата ЛКМ/ПКМ, позиция контроллера мышью больше НЕ трогается (см. RawInputWndProc) —
// только поворот, причём дискретно: g_dirX/g_dirY копят "сырое" направление движения мыши
// (-1..1, с плавным пружинным возвратом к 0 каждый кадр), а в sixenseThreadFunc из них
// выбирается ОДНО доминирующее направление (up/down/left/right) и контроллер довешивается
// ровно на фиксированный угол kHalfTurnRad в эту сторону — никаких промежуточных состояний.
static float g_dirX = 0.0f;                   // -1..1, сырое горизонтальное направление (право/лево)
static float g_dirY = 0.0f;                   // -1..1, сырое вертикальное направление (вверх/вниз)
static float g_mouseSpeed = 0.0f;             // пикселей/кадр, "сырая" скорость мыши прямо сейчас
// (пока зажата ЛКМ/ПКМ) — используется, чтобы решать, НАСКОЛЬКО БЫСТРО
// поворот контроллера подъезжает к выбранной стороне (см. kMinTurnRatePerSec/
// kSpeedToTurnRate в sixenseThreadFunc): резкий/быстрый взмах мышью — быстрый
// поворот, медленное шевеление — медленный, плавный.
static float g_curYaw = 0.0f;                 // текущий (сглаженный) поворот влево/вправо — то,
// что реально уходит в data; каждый кадр подъезжает к snappedYaw
static float g_curPitch = 0.0f;               // текущий (сглаженный) поворот вверх/вниз — аналогично, к snappedPitch
static float g_trigger = 0.0f;                    // 0..1, ЛКМ = триггер правого контроллера (C0)
static float g_triggerLeft = 0.0f;                // 0..1, ПКМ = триггер левого контроллера (C1)
static unsigned int g_buttons = 0;
static float g_moveX = 0.0f;                    // -1..1, A/D — стик контроллера (стрейф)
static float g_moveY = 0.0f;                    // -1..1, W/S — стик контроллера (вперёд/назад)
static bool g_keyW = false, g_keyA = false, g_keyS = false, g_keyD = false;
static bool g_gameKeyW = false, g_gameKeyA = false, g_gameKeyS = false, g_gameKeyD = false;

// Настройки чувствительности — подгоняются опытным путём
static const float kMouseToMm = 1.2f;   // пикселей -> мм смещения по X/Y (обычный Q)
static const float kMouseToDir = 0.01f; // пикселей -> единицы g_dirX/g_dirY (-1..1),
// пока зажата ЛКМ/ПКМ (см. RawInputWndProc); не затухают сами — держатся,
// пока явно не сброшены (отпускание кнопки/выключение Q)
static const float kDirDeadzone = 0.08f; // ниже этого порога по обеим осям считаем, что
// направление не выбрано вообще (нейтраль, без поворота)
static const float kHalfTurnRad = 0.7853981633974483f; // "наполовину" повёрнутый контроллер
// в выбранную сторону (45° = pi/4) — фиксированный угол, дискретный, без промежуточных значений
static const float kSnapTurnRad = 0.17453292519943295f; // 10° = pi/18 — БОЛЬШЕ НЕ ИСПОЛЬЗУЕТСЯ
// (угол теперь пропорционален смещению мыши, см. targetYaw/targetPitch, максимум kHalfTurnRad)
static const float kMouseSpeedReturnPerSec = 10.0f; // как быстро "сырая" g_mouseSpeed сама
// затухает к 0, если мышь перестала двигаться (чтобы скорость отражала
// именно ТЕКУЩЕЕ движение, а не старый рывок)
static const float kFixedTurnRatePerSec = 0.6f; // рад/с — фиксированная (не зависит от
// скорости мыши) скорость подъезда поворота к выбранной стороне. Раньше
// скорость мыши влияла на неё и получалось слишком резко/дёргано —
// теперь всегда одна и та же небольшая скорость.
static const float kWheelToMm = 15.0f;  // один "щелчок" колеса -> мм по Z (push/pull)
static const float kWheelToRad = 0.12f;  // один "щелчок" колеса -> радианы поворота (если зажат Shift)
static const float kPosLimit = 250.0f; // ограничение смещения по каждой оси, мм

// ------------------------------------------------------------------
// Низкоуровневый хук мыши/клавиатуры
// ------------------------------------------------------------------
static HHOOK g_mouseHook = nullptr;
static HHOOK g_keyboardHook = nullptr;

static void SimulateEKey()
{
    // Раньше тут была задержка 30мс перед отправкой — специально для игр,
    // которые игнорируют искусственный E ровно в момент закрытия режима.
    // Но за эти 30мс sixenseThreadFunc успевал отдать игре уже обнулённую
    // позицию контроллера (резкий скачок в 0,0,0 за один кадр), и физика
    // трактовала это как бросок/толчок предмета — куб получал импульс
    // раньше, чем E успевал долететь и "отпустить" его штатно. Теперь
    // отправляем E без задержки и ДО сброса позиции (см. вызов ниже),
    // чтобы E пришёл в игру первым, а не после толчка.

    INPUT input[2] = {};

    input[0].type = INPUT_KEYBOARD;
    input[0].ki.wScan = MapVirtualKeyA('E', MAPVK_VK_TO_VSC);
    input[0].ki.dwFlags = KEYEVENTF_SCANCODE;

    input[1].type = INPUT_KEYBOARD;
    input[1].ki.wScan = MapVirtualKeyA('E', MAPVK_VK_TO_VSC);
    input[1].ki.dwFlags = KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP;

    UINT result = SendInput(2, input, sizeof(INPUT));

    HydraLog("[HydraMouse] Simulate E SendInput result=%u\\n", result);
    fflush(stdout);
}


static void SimulateWASDKeyState(UINT vk, bool down)
{
    INPUT input = {};
    input.type = INPUT_KEYBOARD;
    input.ki.wVk = (WORD)vk;

    if (!down)
        input.ki.dwFlags = KEYEVENTF_KEYUP;

    UINT result = SendInput(1, &input, sizeof(INPUT));
    HydraLog("[HydraMouse] Sync keyboard vk=%u %s -> SendInput=%u\n",
        (unsigned)vk, down ? "DOWN" : "UP", result);
    fflush(stdout);
}

static void SyncGameWASDWithPhysical()
{
    bool pw, pa, ps, pd;
    {
        std::lock_guard<std::mutex> lk(g_input_mutex);
        pw = g_keyW; pa = g_keyA; ps = g_keyS; pd = g_keyD;
    }

    if (g_gameKeyW != pw) {
        SimulateWASDKeyState('W', pw);
        g_gameKeyW = pw;
    }
    if (g_gameKeyA != pa) {
        SimulateWASDKeyState('A', pa);
        g_gameKeyA = pa;
    }
    if (g_gameKeyS != ps) {
        SimulateWASDKeyState('S', ps);
        g_gameKeyS = ps;
    }
    if (g_gameKeyD != pd) {
        SimulateWASDKeyState('D', pd);
        g_gameKeyD = pd;
    }
}



static void ClampPos()
{
    for (int i = 0; i < 3; i++)
        g_pos[i] = std::max(-kPosLimit, std::min(kPosLimit, g_pos[i]));
}

static void ClampDir()
{
    g_dirX = std::max(-1.0f, std::min(1.0f, g_dirX));
    g_dirY = std::max(-1.0f, std::min(1.0f, g_dirY));
}

// Запрашивает полное отложенное выключение Q (см. g_pendingDisable в
// sixenseThreadFunc). Используется и для повторного нажатия Q, и теперь
// для отпускания ЛКМ/ПКМ — оба случая идут по одному и тому же пути.
// Повторные вызовы, пока выключение уже запрошено/идёт, ничего не делают.
static void RequestQDisable()
{
    if (g_emulationActive.load() && !g_pendingDisable.load())
    {
        g_pendingDisable.store(true);
        HydraLog("[HydraMouse] Q: DISABLE REQUESTED, waiting for release pause before reset\n");
        fflush(stdout);
    }
}

static LRESULT CALLBACK LowLevelMouseProc(int nCode, WPARAM wParam, LPARAM lParam)
{
    if (nCode == HC_ACTION && g_emulationActive.load() && g_gameFocused.load())
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
            bool grabHeld = (g_trigger > 0.0f) || (g_triggerLeft > 0.0f); // зажата ЛКМ или ПКМ
            if (grabHeld)
            {
                // Пока зажата ЛКМ или ПКМ, колесо вращает правый контроллер:
                // вперёд (клик > 0) — вправо, назад (клик < 0) — влево.
                // Мышь по-прежнему двигает позицию как при обычном Q (см. RawInputWndProc).
                g_heldYaw += clicks * kWheelToRad;
            }
            else
            {
                bool rotateMode = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;
                if (rotateMode)
                    g_yaw += clicks * kWheelToRad;
                else
                {
                    g_pos[2] -= clicks * kWheelToMm; // инвертированное колесо: вверх/вниз поменяны местами
                    ClampPos();
                }
            }
            return 1;
        }
        case WM_LBUTTONDOWN:
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);
            g_pendingDisable.store(false); // отменяем отложенное выключение Q, если оно ещё доигрывало
            g_trigger = 1.0f; // ЛКМ -> триггер правого контроллера (C0), пока зажата
            g_buttons |= SIXENSE_BUTTON_BUMPER; // используем как "grab" — уточняется опытным путём
            HydraLog("[HydraMouse] LMB DOWN: grab-hold mode ON (dirX/dirY active)\n");
            fflush(stdout);
            return 1;
        }
        case WM_LBUTTONUP:
        {
            // НЕ обнуляем g_trigger/heldYaw/dirX/dirY сразу — вместо этого
            // запрашиваем полное выключение Q (см. RequestQDisable). До того,
            // как оно доиграет, триггер по-прежнему репортится игре нажатым.
            // Реальный сброс всех данных контроллера делает sixenseThreadFunc.
            RequestQDisable();
            HydraLog("[HydraMouse] LMB UP: Q disable requested (trigger still held until reset)\n");
            fflush(stdout);
            return 1;
        }
        case WM_RBUTTONDOWN:
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);
            g_pendingDisable.store(false); // отменяем отложенное выключение Q, если оно ещё доигрывало
            g_triggerLeft = 1.0f; // ПКМ -> триггер левого контроллера (C1), пока зажата
            HydraLog("[HydraMouse] RMB DOWN: grab-hold mode ON (dirX/dirY active)\n");
            fflush(stdout);
            return 1;
        }
        case WM_RBUTTONUP:
        {
            // См. комментарий в WM_LBUTTONUP — тот же путь полного выключения Q.
            RequestQDisable();
            HydraLog("[HydraMouse] RMB UP: Q disable requested (trigger still held until reset)\n");
            fflush(stdout);
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

    if (nCode == HC_ACTION && !g_gameFocused.load())
    {
        // Окно игры не в фокусе (свёрнуто/alt-tab/пишем в другом окне) —
        // вообще не детектим наши биндинги (Q/E/WASD/Space/Ctrl/Enter),
        // чтобы они не перехватывались, пока человек печатает где-то ещё.
        return CallNextHookEx(g_keyboardHook, nCode, wParam, lParam);
    }

    if (nCode == HC_ACTION)
    {
        KBDLLHOOKSTRUCT* info = (KBDLLHOOKSTRUCT*)lParam;

        // Всегда отслеживаем физическое состояние WASD.
        // Когда Q выключен, эти же события получает игра, поэтому
        // сохраняем отдельное состояние того, что игра считает нажатым.
        if (!(info->flags & LLKHF_INJECTED))
        {
            bool wasdDown = (wParam == WM_KEYDOWN || wParam == WM_SYSKEYDOWN);
            bool wasdUp = (wParam == WM_KEYUP || wParam == WM_SYSKEYUP);

            if (wasdDown || wasdUp)
            {
                std::lock_guard<std::mutex> lk(g_input_mutex);

                switch (info->vkCode)
                {
                case 'W':
                    g_keyW = wasdDown;
                    if (!g_emulationActive.load() || wasdUp) g_gameKeyW = wasdDown;
                    break;
                case 'A':
                    g_keyA = wasdDown;
                    if (!g_emulationActive.load() || wasdUp) g_gameKeyA = wasdDown;
                    break;
                case 'S':
                    g_keyS = wasdDown;
                    if (!g_emulationActive.load() || wasdUp) g_gameKeyS = wasdDown;
                    break;
                case 'D':
                    g_keyD = wasdDown;
                    if (!g_emulationActive.load() || wasdUp) g_gameKeyD = wasdDown;
                    break;
                default:
                    break;
                }

                g_moveX = (g_keyD ? 1.0f : 0.0f) - (g_keyA ? 1.0f : 0.0f);
                g_moveY = (g_keyW ? 1.0f : 0.0f) - (g_keyS ? 1.0f : 0.0f);
            }
        }

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
                    HydraLog("[HydraMouse] Q: ENABLED at t=0ms, starting 5s diagnostic log\n");
                    fflush(stdout);

                    {
                        std::lock_guard<std::mutex> lk(g_input_mutex);
                        g_pos[0] = g_pos[1] = 0.0f; g_pos[2] = 250.0f; // idle Z = 250 мм
                        g_dirX = g_dirY = 0.0f; g_curYaw = g_curPitch = 0.0f; g_mouseSpeed = 0.0f;
                        // Не сбрасываем g_keyW/A/S/D: это физическое состояние клавиатуры.
                        g_moveX = g_moveY = 0.0f;
                        g_buttons = 0;
                        g_trigger = 0.0f;
                        g_triggerLeft = 0.0f;
                        g_heldYaw = 0.0f;
                    }
                    HideCursorIfFocused();
                }
                else if (!g_pendingDisable.load())
                {
                    // Выключаем — НЕ сразу, тем же путём, что и отпускание
                    // ЛКМ/ПКМ (см. RequestQDisable). Реальное выключение
                    // g_emulationActive, сброс состояния и возврат курсора
                    // происходят только после того, как пауза выключения
                    // полностью доиграет в sixenseThreadFunc.
                    RequestQDisable();
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
                HydraLog("[HydraMouse] E pressed during Q: disabling Q and replaying E\n");
                fflush(stdout);

                // Гасим режим и сразу шлём E — до сброса позиции/состояния,
                // чтобы игра получила E раньше, чем зафиксирует скачок
                // позиции контроллера в (0,0,0), который она может
                // истолковать как бросок предмета.
                g_emulationActive.store(false);
                g_pendingDisable.store(false);

                // Вернуть игре все пропущенные изменения WASD.
                SyncGameWASDWithPhysical();

                SimulateEKey();

                {
                    std::lock_guard<std::mutex> lk(g_input_mutex);
                    g_pos[0] = g_pos[1] = 0.0f; g_pos[2] = 250.0f; // idle Z = 250 мм
                    g_dirX = g_dirY = 0.0f; g_curYaw = g_curPitch = 0.0f; g_mouseSpeed = 0.0f;
                    g_keyW = g_keyA = g_keyS = g_keyD = false;
                    g_moveX = g_moveY = 0.0f;
                    g_buttons = 0;
                    g_trigger = 0.0f;
                    g_triggerLeft = 0.0f;
                    g_heldYaw = 0.0f;
                }

                RestoreCursor();

                return 1;
            }
        }

        // Во время Q WASD используются только внутренней логикой эмуляции.
        // ВАЖНО: KEYUP намеренно НЕ съедаем. Если W/A/S/D была нажата до Q,
        // Portal 2 уже получила KEYDOWN и должна получить настоящий KEYUP,
        // даже если режим Q сейчас активен. Именно это не даёт клавише залипать.
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
            bool isUp = (wParam == WM_KEYUP || wParam == WM_SYSKEYUP);
            if (isDown || isUp)
            {
                bool handled = true;
                bool eatWhileActive = false; // съедать эту клавишу, пока g_emulationActive == true
                std::lock_guard<std::mutex> lk(g_input_mutex);
                switch (info->vkCode)
                {
                case 'W':
                case 'A':
                case 'S':
                case 'D':
                    // Состояние уже обновлено выше, независимо от Q.
                    eatWhileActive = true;
                    break;
                case VK_SPACE:
                case VK_CONTROL:
                case VK_LCONTROL:
                case VK_RCONTROL:
                    // Space и Ctrl больше не обрабатываются эмуляцией контроллера.
                    // Передаём их игре как обычные клавиши.
                    handled = false;
                    eatWhileActive = false;
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
                if (eatWhileActive && g_emulationActive.load())
                {
                    // KEYDOWN во время Q скрываем от игры.
                    // KEYUP пропускаем дальше, чтобы отпустить клавишу, которую
                    // игра могла получить ещё до включения Q.
                    if (isDown)
                        return 1;
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
                    g_emulationActive.load() &&
                    g_gameFocused.load())
                {
                    LONG dx = raw->data.mouse.lLastX;
                    LONG dy = raw->data.mouse.lLastY;
                    if (dx != 0 || dy != 0)
                    {
                        std::lock_guard<std::mutex> lk(g_input_mutex);
                        bool grabHeld = (g_trigger > 0.0f) || (g_triggerLeft > 0.0f); // зажата ЛКМ или ПКМ

                        static std::atomic<long> rawLogCount{ 0 };
                        if ((rawLogCount.fetch_add(1) % 15) == 0)
                        {
                            HydraLog("[HydraMouse][RAW] dx=%ld dy=%ld grabHeld=%d trig=%.1f trigL=%.1f -> %s\n",
                                dx, dy, (int)grabHeld, (double)g_trigger, (double)g_triggerLeft,
                                grabHeld ? "dirX/dirY" : "pos");
                            fflush(stdout);
                        }

                        if (grabHeld)
                        {
                            // Пока зажата ЛКМ/ПКМ, позиция контроллера мышью НЕ трогается —
                            // только направление поворота. Копим "сырое" направление (-1..1,
                            // с плавным пружинным возвратом к 0 каждый кадр — см.
                            // sixenseThreadFunc), а из него там же выбирается ОДНО
                            // доминирующее направление (вверх/вниз/влево/вправо) и контроллер
                            // довешивается на фиксированный угол kHalfTurnRad ровно в эту
                            // сторону — промежуточных состояний нет. Скорость, с которой
                            // контроллер РЕАЛЬНО долетает до этого угла, зависит от скорости
                            // мыши (g_mouseSpeed) — см. интерполяцию в sixenseThreadFunc.
                            g_dirX += dx * kMouseToDir;
                            g_dirY -= dy * kMouseToDir; // экранный Y растёт вниз, "вверх" — наоборот
                            ClampDir();

                            // Мгновенная скорость мыши в этом raw-событии (пикселей за событие,
                            // примерно "за кадр" — события Raw Input приходят часто). Берём максимум
                            // с уже накопленным значением, чтобы за один кадр не потерять короткий
                            // резкий рывок между двумя чтениями в sixenseThreadFunc; сам g_mouseSpeed
                            // затухает там же каждый кадр (kMouseSpeedReturnPerSec).
                            float speedNow = std::sqrt((float)(dx * dx + dy * dy));
                            g_mouseSpeed = std::max(g_mouseSpeed, speedNow);
                        }
                        else
                        {
                            g_pos[0] += dx * kMouseToMm;
                            g_pos[1] -= dy * kMouseToMm; // экранный Y растёт вниз, мировой "вверх" — наоборот
                            ClampPos();
                        }
                    }
                }
            }
        }
        return 0;
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

// ------------------------------------------------------------------
// Дебаг-окно: 3D-визуализация поворота/позиции контроллеров в реальном
// времени + текст с цифрами сверху. Отдельное от консоли окно, создаётся
// на том же потоке, что и raw input (см. HookThreadFunc), рисуется через
// обычный GDI (без доп. зависимостей вроде D3D/OpenGL).
// ------------------------------------------------------------------
struct DebugControllerSnapshot
{
    float pos[3] = { 0.0f, 0.0f, 0.0f };
    float rotMat[3][3] = { {1,0,0}, {0,1,0}, {0,0,1} };
    float quat[4] = { 0.0f, 0.0f, 0.0f, 1.0f };
    float yawDeg = 0.0f;
    float pitchDeg = 0.0f;
    float snapYawDeg = 0.0f;
    float trigger = 0.0f;
    unsigned int buttons = 0;
    unsigned char enabled = 0;
    unsigned char is_docked = 0;
};

static std::mutex g_debug_mutex;
static DebugControllerSnapshot g_debugSnap[2];
static HWND g_debugWnd = nullptr;
static const wchar_t* kDebugClassName = L"HydraMouseDebugWnd";

// Оси rotMat[i] (i = 0..2) — это уже готовые повёрнутые направления X/Y/Z
// (см. заполнение g_debugSnap в sixenseThreadFunc, скопировано напрямую
// из data.rot_mat в том же порядке индексов, что и при заполнении data
// в основном потоке).
static void RotatedAxes(const float rotMat[3][3], float vx[3], float vy[3], float vz[3])
{
    for (int k = 0; k < 3; k++)
    {
        vx[k] = rotMat[0][k];
        vy[k] = rotMat[1][k];
        vz[k] = rotMat[2][k];
    }
}

// Простая псевдо-3D (изометрическая) проекция точки в экранные координаты —
// без камеры/матрицы вида, достаточно для наглядной диагностики.
static POINT Project3D(float x, float y, float z, int cx, int cy, float scale)
{
    POINT p;
    p.x = cx + (LONG)((x - z * 0.5f) * scale);
    p.y = cy - (LONG)((y - z * 0.35f) * scale);
    return p;
}

static void DrawControllerGizmo(HDC hdc, int cx, int cy, float scale,
    const DebugControllerSnapshot& snap, const wchar_t* label, COLORREF labelColor)
{
    float vx[3], vy[3], vz[3];
    RotatedAxes(snap.rotMat, vx, vy, vz);

    // Позицию контроллера тоже показываем — гизмо смещается вместе с ней
    // (сильно уменьшено по масштабу, чтобы влезать в окно).
    float ox = snap.pos[0] * 0.15f;
    float oy = snap.pos[1] * 0.15f;
    float oz = snap.pos[2] * 0.15f;

    POINT origin = Project3D(ox, oy, oz, cx, cy, scale);

    const float axisLen = 1.6f;
    POINT px = Project3D(ox + vx[0] * axisLen, oy + vx[1] * axisLen, oz + vx[2] * axisLen, cx, cy, scale);
    POINT py = Project3D(ox + vy[0] * axisLen, oy + vy[1] * axisLen, oz + vy[2] * axisLen, cx, cy, scale);
    POINT pz = Project3D(ox + vz[0] * axisLen, oy + vz[1] * axisLen, oz + vz[2] * axisLen, cx, cy, scale);

    // Оси: X — красная, Y — зелёная, Z — синяя (обычное соглашение)
    HPEN penX = CreatePen(PS_SOLID, 2, RGB(220, 40, 40));
    HPEN penY = CreatePen(PS_SOLID, 2, RGB(40, 200, 60));
    HPEN penZ = CreatePen(PS_SOLID, 2, RGB(50, 130, 230));
    HGDIOBJ oldPen = SelectObject(hdc, penX);
    MoveToEx(hdc, origin.x, origin.y, nullptr); LineTo(hdc, px.x, px.y);
    SelectObject(hdc, penY);
    MoveToEx(hdc, origin.x, origin.y, nullptr); LineTo(hdc, py.x, py.y);
    SelectObject(hdc, penZ);
    MoveToEx(hdc, origin.x, origin.y, nullptr); LineTo(hdc, pz.x, pz.y);
    SelectObject(hdc, oldPen);
    DeleteObject(penX); DeleteObject(penY); DeleteObject(penZ);

    // Проволочный кубик — условное "тело" контроллера, чтобы поворот был
    // виден нагляднее, чем по одним осям.
    const float s = 0.35f;
    POINT corners[8];
    int idx = 0;
    for (int sx = -1; sx <= 1; sx += 2)
        for (int sy = -1; sy <= 1; sy += 2)
            for (int sz = -1; sz <= 1; sz += 2)
            {
                float wx = ox + (vx[0] * sx + vy[0] * sy + vz[0] * sz) * s;
                float wy = oy + (vx[1] * sx + vy[1] * sy + vz[1] * sz) * s;
                float wz = oz + (vx[2] * sx + vy[2] * sy + vz[2] * sz) * s;
                corners[idx++] = Project3D(wx, wy, wz, cx, cy, scale);
            }
    // Порядок углов соответствует вложенным циклам выше: (sx,sy,sz) =
    // (-,-,-)(-,-,+)(-,+,-)(-,+,+)(+,-,-)(+,-,+)(+,+,-)(+,+,+)
    static const int edges[12][2] = {
        {0,1},{0,2},{0,4},{1,3},{1,5},{2,3},{2,6},{3,7},{4,5},{4,6},{5,7},{6,7}
    };
    HPEN penEdge = CreatePen(PS_SOLID, 1, RGB(150, 150, 160));
    oldPen = SelectObject(hdc, penEdge);
    for (int e = 0; e < 12; e++)
    {
        MoveToEx(hdc, corners[edges[e][0]].x, corners[edges[e][0]].y, nullptr);
        LineTo(hdc, corners[edges[e][1]].x, corners[edges[e][1]].y);
    }
    SelectObject(hdc, oldPen);
    DeleteObject(penEdge);

    SetTextColor(hdc, labelColor);
    SetBkMode(hdc, TRANSPARENT);
    TextOutW(hdc, cx - 60, cy + (int)(axisLen * scale) + 12, label, (int)wcslen(label));
}

static LRESULT CALLBACK DebugWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg)
    {
    case WM_TIMER:
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    case WM_CLOSE:
        // Диагностическое окно не закрываем по крестику насовсем — просто
        // прячем, чтобы случайный клик не убивал визуализацию до перезапуска.
        ShowWindow(hwnd, SW_HIDE);
        return 0;
    case WM_ERASEBKGND:
        return 1; // фон рисуем сами в WM_PAINT (двойная буферизация), чтобы не мигало
    case WM_PAINT:
    {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hwnd, &ps);

        RECT rc; GetClientRect(hwnd, &rc);
        int w = rc.right - rc.left;
        int h = rc.bottom - rc.top;
        if (w < 10) w = 10;
        if (h < 10) h = 10;

        HDC memDC = CreateCompatibleDC(hdc);
        HBITMAP memBmp = CreateCompatibleBitmap(hdc, w, h);
        HGDIOBJ oldBmp = SelectObject(memDC, memBmp);

        HBRUSH bg = CreateSolidBrush(RGB(24, 24, 28));
        FillRect(memDC, &rc, bg);
        DeleteObject(bg);

        DebugControllerSnapshot snap0, snap1;
        {
            std::lock_guard<std::mutex> lk(g_debug_mutex);
            snap0 = g_debugSnap[0];
            snap1 = g_debugSnap[1];
        }

        SetBkMode(memDC, TRANSPARENT);
        HFONT font = CreateFontW(16, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE,
            DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY,
            DEFAULT_PITCH | FF_DONTCARE, L"Consolas");
        HGDIOBJ oldFont = SelectObject(memDC, font);

        // Два гизмо рядом: C0 (правая/активная, мышь) и C1 (левая, нейтральная)
        int cx0 = w / 4, cx1 = (3 * w) / 4, cyGizmo = h / 2 + 30;
        float scale = (float)(std::min)(w, h) * 0.10f;
        DrawControllerGizmo(memDC, cx0, cyGizmo, scale, snap0, L"C0 (правая / мышь)", RGB(255, 210, 90));
        DrawControllerGizmo(memDC, cx1, cyGizmo, scale, snap1, L"C1 (левая)", RGB(150, 200, 255));

        // Текст с цифрами поворота/позиции сверху окна
        wchar_t buf[256];
        SetTextColor(memDC, RGB(230, 230, 235));
        swprintf_s(buf, L"C0 pos mm:  X=%7.1f  Y=%7.1f  Z=%7.1f", snap0.pos[0], snap0.pos[1], snap0.pos[2]);
        TextOutW(memDC, 10, 8, buf, (int)wcslen(buf));
        swprintf_s(buf, L"C0 rot deg: yaw=%7.1f  pitch=%7.1f  snapYaw=%6.1f", snap0.yawDeg, snap0.pitchDeg, snap0.snapYawDeg);
        TextOutW(memDC, 10, 28, buf, (int)wcslen(buf));
        swprintf_s(buf, L"C0 quat: (%.2f, %.2f, %.2f, %.2f)  trig=%.2f  btn=0x%03X  en=%d dock=%d",
            snap0.quat[0], snap0.quat[1], snap0.quat[2], snap0.quat[3],
            snap0.trigger, snap0.buttons, snap0.enabled, snap0.is_docked);
        TextOutW(memDC, 10, 48, buf, (int)wcslen(buf));

        swprintf_s(buf, L"C1 pos mm:  X=%7.1f  Y=%7.1f  Z=%7.1f", snap1.pos[0], snap1.pos[1], snap1.pos[2]);
        TextOutW(memDC, 10, 76, buf, (int)wcslen(buf));
        swprintf_s(buf, L"C1 rot deg: yaw=%7.1f  pitch=%7.1f", snap1.yawDeg, snap1.pitchDeg);
        TextOutW(memDC, 10, 96, buf, (int)wcslen(buf));
        swprintf_s(buf, L"C1 quat: (%.2f, %.2f, %.2f, %.2f)  trig=%.2f  btn=0x%03X  en=%d dock=%d",
            snap1.quat[0], snap1.quat[1], snap1.quat[2], snap1.quat[3],
            snap1.trigger, snap1.buttons, snap1.enabled, snap1.is_docked);
        TextOutW(memDC, 10, 116, buf, (int)wcslen(buf));

        SelectObject(memDC, oldFont);
        DeleteObject(font);

        BitBlt(hdc, 0, 0, w, h, memDC, 0, 0, SRCCOPY);

        SelectObject(memDC, oldBmp);
        DeleteObject(memBmp);
        DeleteDC(memDC);

        EndPaint(hwnd, &ps);
        return 0;
    }
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

static bool InitDebugWindow(HINSTANCE hInst)
{
    WNDCLASSEXW wc = {};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = DebugWndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wc.lpszClassName = kDebugClassName;
    RegisterClassExW(&wc); // если уже зарегистрирован — не страшно, просто игнорируем ошибку

    g_debugWnd = CreateWindowExW(0, kDebugClassName, L"HydraMouse — 3D debug",
        WS_OVERLAPPEDWINDOW, 40, 40, 560, 420, nullptr, nullptr, hInst, nullptr);
    if (!g_debugWnd)
        return false;

    ShowWindow(g_debugWnd, SW_SHOWNOACTIVATE); // не отбирает фокус у игры
    UpdateWindow(g_debugWnd);
    SetTimer(g_debugWnd, 1, 16, nullptr); // ~60 Гц перерисовка

    return true;
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
    if (g_cfgDebug3DView.load())
        InitDebugWindow(hInst); // дебаг-окно 3D визуализации поворота/позиции контроллеров (только если Debug3DView=true в cfg)

    MSG msg;
    while (g_running.load())
    {
        // Следим за фокусом окна игры. Проверяем каждую итерацию цикла
        // (интервал ~2мс, см. sleep ниже), чтобы реакция была мгновенной:
        // - потеряли фокус (alt-tab/свернули игру, кликнули в другое окно) —
        //   сразу возвращаем курсор, даже если Q/motion-режим всё ещё "включён"
        //   внутри игры. Раньше курсор мог остаться заблокированным навсегда
        //   после сворачивания игры, пока был активен Q.
        // - вернули фокус на игру — если Q всё ещё включён, снова прячем
        //   курсор (как будто ничего и не происходило).
        bool focusedNow = IsGameWindowForeground();
        bool wasFocused = g_gameFocused.exchange(focusedNow);
        if (focusedNow != wasFocused)
        {
            if (!focusedNow)
                RestoreCursor();
            else if (g_emulationActive.load())
                HideCursorIfFocused();
        }

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
    if (g_debugWnd) { KillTimer(g_debugWnd, 1); DestroyWindow(g_debugWnd); }
    g_mouseHook = nullptr;
    g_keyboardHook = nullptr;
    g_rawInputWnd = nullptr;
    g_debugWnd = nullptr;
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
    static const unsigned long ENTER_HOLD_FRAMES = 20; // ~0.3с держим анлок, пока Start долетает до игры
    static const unsigned long ENTER_TOTAL_FRAMES = ENTER_CALIB_FRAMES + ENTER_HOLD_FRAMES;

    // --- Отложенное выключение Q: запрашивается либо повторным нажатием Q,
    // либо отпусканием ЛКМ/ПКМ (см. RequestQDisable). Сначала выдерживаем
    // паузу RELEASE_PULSE_FRAMES кадров (SIXENSE_BUTTON_1 при этом НЕ
    // форсируем — см. закомментированную строку ниже), и только потом
    // реально гасим g_emulationActive и сбрасываем данные контроллера.
    // Пока пауза идёт, Q фактически ещё "включён".
    bool disablingInProgress = false;
    unsigned long disableFrame = 0;
    static const unsigned long RELEASE_PULSE_FRAMES = 20; // ~0.3с пауза перед реальным выключением

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
            HydraLog("[HydraMouse] Enter (Q выкл): анлок+калибровка обоих контроллеров перед Start\n");
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
                HydraLog("[HydraMouse] Enter-последовательность завершена, состояние докинга возвращено к обычному\n");
                fflush(stdout);
            }
            if (enterSeqActive) enterSeqFrame++;
        }

        compatAllControllerData all_data = {};

        float pos[3], yaw, heldYaw, dirX, dirY, mouseSpeed, trigger, triggerLeft, moveX, moveY;
        unsigned int buttons;
        {
            std::lock_guard<std::mutex> lk(g_input_mutex);

            // g_dirX/g_dirY больше НЕ затухают сами по себе — направление, которое
            // выбрала мышь, остаётся зафиксированным (никакого отката "в обратное
            // положение"), пока не будет явно сброшено в 0 — при отпускании
            // ЛКМ/ПКМ или при выключении Q (см. соответствующие reset-блоки выше).
            {
                // g_mouseSpeed всё ещё затухает каждый кадр — она отражает, насколько
                // резко мышь двигалась ПРЯМО СЕЙЧАС, а не когда-то раньше, и нужна только
                // для скорости подъезда curYaw/curPitch к цели, а не для сброса цели.
                float speedDecay = std::exp(-kMouseSpeedReturnPerSec * (interval.count() / 1000.0f));
                g_mouseSpeed *= speedDecay;
                if (g_mouseSpeed < 0.01f) g_mouseSpeed = 0.0f;
            }

            pos[0] = g_pos[0]; pos[1] = g_pos[1]; pos[2] = g_pos[2];
            yaw = g_yaw;
            heldYaw = g_heldYaw;
            dirX = g_dirX;
            dirY = g_dirY;
            mouseSpeed = g_mouseSpeed;
            trigger = g_trigger;
            triggerLeft = g_triggerLeft;
            buttons = g_buttons;
            moveX = g_moveX;
            moveY = g_moveY;
        }

        // Раньше выбиралась ОДНА доминирующая ось (yaw либо pitch), это было
        // неудобно управлять по диагонали. Теперь обе оси работают одновременно
        // и независимо: угол-цель по каждой оси пропорционален смещению мыши по
        // ЭТОЙ ЖЕ оси (dirX для yaw, dirY для pitch, диапазон -1..1), умножается
        // на максимум kHalfTurnRad (45°). Деадзона применяется к каждой оси
        // отдельно — если конкретная ось ниже kDirDeadzone, её цель — 0,
        // но другая ось при этом продолжает работать как обычно.
        float targetYaw = 0.0f;   // влево/вправо — поворот вокруг вертикальной оси (Y)
        float targetPitch = 0.0f; // вверх/вниз — поворот вокруг перпендикулярной оси (X)
        {
            if (std::fabs(dirX) > kDirDeadzone)
                targetYaw = dirX * kHalfTurnRad;
            if (std::fabs(dirY) > kDirDeadzone)
                targetPitch = dirY * kHalfTurnRad;
        }

        // РЕАЛЬНЫЙ поворот (g_curYaw/g_curPitch) не прыгает мгновенно к цели —
        // он плавно подъезжает к ней каждый кадр с одной и той же небольшой
        // фиксированной скоростью (kFixedTurnRatePerSec), независимо от того,
        // как резко двигали мышью. Раньше скорость подъезда зависела от скорости
        // мыши и джойстик "мотало" слишком быстро — теперь всегда одинаково плавно.
        float snappedYaw, snappedPitch;
        {
            float dt = interval.count() / 1000.0f;
            float maxStep = kFixedTurnRatePerSec * dt;

            float diffYaw = targetYaw - g_curYaw;
            if (std::fabs(diffYaw) <= maxStep) g_curYaw = targetYaw;
            else g_curYaw += (diffYaw > 0.0f ? maxStep : -maxStep);

            float diffPitch = targetPitch - g_curPitch;
            if (std::fabs(diffPitch) <= maxStep) g_curPitch = targetPitch;
            else g_curPitch += (diffPitch > 0.0f ? maxStep : -maxStep);

            snappedYaw = g_curYaw;
            snappedPitch = g_curPitch;
        }

        for (int i = 0; i < 3; i++)
            pos[i] = std::max(-kPosLimit, std::min(kPosLimit, pos[i]));

        if (!enabledNow)
        {
            // Пока режим выключен, контроллер 0 репортится "включённым" (см. выше —
            // это нужно только чтобы Enter/Start доходил до игры), но мышь/WASD/
            // триггер не должны влиять на игру, пока Q не нажат — обнуляем всё,
            // кроме кнопки Start.
            pos[0] = pos[1] = 0.0f;
            pos[2] = 250.0f; // idle-позиция контроллера 0 по Z (мм), а не 0
            yaw = 0.0f;
            heldYaw = 0.0f;
            snappedYaw = 0.0f;
            snappedPitch = 0.0f;
            trigger = 0.0f;
            triggerLeft = 0.0f;
            moveX = moveY = 0.0f;
            buttons &= SIXENSE_BUTTON_START;
        }
        else
        {
            // Пока режим Q включён, ходьба с WASD полностью игнорируется —
            // перемещение теперь идёт только через мышь/контроллер, клавиши
            // W/A/S/D на джойстик контроллера больше не транслируются.
            moveX = moveY = 0.0f;
            // Триггеры больше НЕ держим нажатыми автоматически при включении Q —
            // ЛКМ теперь напрямую управляет триггером C0 (правый), ПКМ — триггером
            // C1 (левый), полностью аналогично тому, как колёсико мыши обрабатывается
            // выше в LowLevelMouseProc. trigger/triggerLeft уже содержат актуальное
            // состояние кнопок мыши, взятое из g_trigger/g_triggerLeft — трогать их
            // здесь больше не нужно.
        }

        // --- Отложенное выключение Q: пока идёт пауза выключения,
        // g_emulationActive НЕ трогаем (он всё ещё true — enabledNow видит
        // это как "Q включён", реальные мышь/ЛКМ/триггеры продолжают
        // репортиться как есть). Как только пауза полностью доиграет
        // RELEASE_PULSE_FRAMES кадров — ВОТ ТОГДА уже по-настоящему гасим Q:
        // g_emulationActive=false, сбрасываем ВСЕ данные контроллера
        // (включая триггеры ЛКМ/ПКМ), возвращаем курсор.
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

                // Portal 2 могла получить WASD до включения Q, а KEYUP/KEYDOWN
                // во время Q мы намеренно съедали. Восстанавливаем только
                // пропущенные переходы клавиш.
                SyncGameWASDWithPhysical();

                {
                    std::lock_guard<std::mutex> lk(g_input_mutex);
                    g_moveX = (g_keyD ? 1.0f : 0.0f) - (g_keyA ? 1.0f : 0.0f);
                    g_moveY = (g_keyW ? 1.0f : 0.0f) - (g_keyS ? 1.0f : 0.0f);
                    g_pos[0] = g_pos[1] = 0.0f; g_pos[2] = 250.0f; // idle Z = 250 мм
                    g_dirX = g_dirY = 0.0f; g_curYaw = g_curPitch = 0.0f; g_mouseSpeed = 0.0f;
                    g_buttons = 0;
                    g_trigger = 0.0f;
                    g_triggerLeft = 0.0f;
                    g_heldYaw = 0.0f;
                }
                ShowCursor(TRUE);
                HydraLog("[HydraMouse] Q: DISABLED (полный сброс контроллера после паузы выключения)\n");
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

        // heldYaw — доп. вращение правого контроллера колесом мыши, пока зажата
        // ЛКМ/ПКМ (см. LowLevelMouseProc); складывается поверх обычного g_yaw
        // и сбрасывается в 0 сразу после отпускания кнопки. Это ROLL — крутит
        // вокруг оси Z (ребром вправо/влево), как и раньше.
        //
        // snappedYaw/snappedPitch — дискретный поворот "наполовину" в сторону,
        // куда сейчас доминирует движение мыши (см. дискретизацию dirX/dirY выше):
        // snappedPitch крутит "нос" вверх/вниз вокруг оси X — так уже было и это
        // выглядело правильно; snappedYaw теперь ТАК ЖЕ разворачивает "нос"
        // влево/вправо, но вокруг вертикальной оси Y (а не вокруг Z, как колесо/
        // heldYaw) — иначе это был бы roll ("ребром"), а не yaw ("носом").
        // Активна всегда только одна из них — вторая строго 0.
        sixenseMath::Vector3 axisRoll(0.0f, 0.0f, 1.0f);   // колесо / heldYaw — как и раньше
        sixenseMath::Vector3 axisYaw(0.0f, -1.0f, 0.0f);   // влево/вправо "носом" — вокруг Y (инвертировано, была зеркальная)
        sixenseMath::Vector3 axisPitch(1.0f, 0.0f, 0.0f);  // вверх/вниз "носом" — вокруг X
        sixenseMath::Matrix3 matRoll = sixenseMath::Matrix3::rotation(yaw + heldYaw, axisRoll);
        sixenseMath::Matrix3 matYaw = sixenseMath::Matrix3::rotation(snappedYaw, axisYaw);
        sixenseMath::Matrix3 matPitch = sixenseMath::Matrix3::rotation(snappedPitch, axisPitch);
        sixenseMath::Matrix3 mat = matRoll * matYaw * matPitch;

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
            data.trigger = autoCalibrateTrigger ? (uint8_t)255 : (uint8_t)(triggerLeft * 255.0f);
#else
            // В float-протоколе 0.0f и так является центром стика — здесь баг
            // не проявлялся, но выставляем явно для симметрии и ясности.
            data.joystick_x = 0.0f;
            data.joystick_y = 0.0f;
            data.trigger = autoCalibrateTrigger ? 1.0f : triggerLeft;
            data.hemi_tracking_enabled = 1;
#endif
        }

        {
            std::lock_guard<std::mutex> lk(g_data_mutex);
            g_controller_data.push_front(all_data);
            g_controller_data.pop_back();
        }

        // --- Снимок для дебаг-окна 3D визуализации (см. DrawControllerGizmo/
        // DebugWndProc выше). Берём готовые данные из all_data, чтобы окно
        // видело ровно то же, что уходит в игру, плюс отдельно углы в
        // градусах (yaw/pitch), которые уже посчитаны выше как raw-значения. ---
        {
            std::lock_guard<std::mutex> lk(g_debug_mutex);
            const compatControllerData& c0 = all_data.controllers[0];
            const compatControllerData& c1 = all_data.controllers[1];
            static const float kRadToDeg = 57.29577951308232f;

            for (int i = 0; i < 3; i++) g_debugSnap[0].pos[i] = c0.pos[i];
            for (int col = 0; col < 3; col++)
                for (int row = 0; row < 3; row++)
                    g_debugSnap[0].rotMat[col][row] = c0.rot_mat[col][row];
            for (int i = 0; i < 4; i++) g_debugSnap[0].quat[i] = c0.rot_quat[i];
            g_debugSnap[0].yawDeg = (yaw + heldYaw + snappedYaw) * kRadToDeg;   // суммарный (roll+yaw+held) — для общей картины
            g_debugSnap[0].pitchDeg = snappedPitch * kRadToDeg;                // это и так был "чистый" snap, без примесей
            g_debugSnap[0].snapYawDeg = snappedYaw * kRadToDeg;                 // "чистый" поворот носом влево/вправо — должен быть <= 10°
#ifdef SIXENSE_LEGACY
            g_debugSnap[0].trigger = c0.trigger / 255.0f;
#else
            g_debugSnap[0].trigger = c0.trigger;
#endif
            g_debugSnap[0].buttons = c0.buttons;
            g_debugSnap[0].enabled = c0.enabled;
            g_debugSnap[0].is_docked = c0.is_docked;

            for (int i = 0; i < 3; i++) g_debugSnap[1].pos[i] = c1.pos[i];
            for (int col = 0; col < 3; col++)
                for (int row = 0; row < 3; row++)
                    g_debugSnap[1].rotMat[col][row] = c1.rot_mat[col][row];
            for (int i = 0; i < 4; i++) g_debugSnap[1].quat[i] = c1.rot_quat[i];
            g_debugSnap[1].yawDeg = 0.0f;
            g_debugSnap[1].pitchDeg = 0.0f;
#ifdef SIXENSE_LEGACY
            g_debugSnap[1].trigger = c1.trigger / 255.0f;
#else
            g_debugSnap[1].trigger = c1.trigger;
#endif
            g_debugSnap[1].buttons = c1.buttons;
            g_debugSnap[1].enabled = c1.enabled;
            g_debugSnap[1].is_docked = c1.is_docked;
        }

        if (InLogWindow() && (frames_since_enable % 4 == 0)) // ~15 логов/сек
        {
            const compatControllerData& c0 = all_data.controllers[0];
            const compatControllerData& c1 = all_data.controllers[1];
            HydraLog("[HydraMouse][GEN] t=%lldms frame=%lu | C0: pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d | C1: trig=%.2f dock=%d calib=%d\n",
                NowMs() - g_enableEpochMs.load(), frames_since_enable,
                pos[0], pos[1], pos[2], trigger, buttons, (int)currently_enabled, (int)currently_docked_c0,
                (double)c1.trigger, (int)currently_docked_c1, (int)autoCalibrateTrigger);
            fflush(stdout);
        }

        // Отдельный лог для диагностики grab-hold (dirX/dirY/snappedYaw/snappedPitch),
        // не привязан к 5-секундному InLogWindow — печатается всегда, пока зажата
        // ЛКМ/ПКМ, чтобы видно было, какое направление реально выбралось.
        static std::atomic<long> grabLogCount{ 0 };
        bool grabHeldNow = (trigger > 0.0f) || (triggerLeft > 0.0f);
        if (enabledNow && grabHeldNow && (grabLogCount.fetch_add(1) % 15) == 0)
        {
            HydraLog("[HydraMouse][GRAB] dir=(%.2f,%.2f) snappedYaw=%.2f snappedPitch=%.2f pos=(%.1f,%.1f,%.1f)\n",
                dirX, dirY, snappedYaw, snappedPitch, pos[0], pos[1], pos[2]);
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
    // Читаем HydraMouse.cfg рядом с DLL: DebugConsole / Debug3DView / Log.
    // Если файла нет — все флаги остаются false (тихий режим по умолчанию).
    LoadConfig();

    // Лог-файл HydraMouse.log рядом с DLL — открывается заново ("w") каждую
    // сессию, т.е. каждую загрузку DLL, так что старое содержимое не копится.
    OpenLogFile();

    // Отдельная консоль для диагностики: DLL грузится внутрь процесса игры,
    // у которой обычно нет своей консоли, поэтому HydraLog() без AllocConsole
    // просто никуда не пишет и все логи молча теряются. Включается только
    // если DebugConsole = true в cfg.
    if (g_cfgDebugConsole.load() && AllocConsole())
    {
        FILE* fp = nullptr;
        freopen_s(&fp, "CONOUT$", "w", stdout);
        freopen_s(&fp, "CONOUT$", "w", stderr);
        SetConsoleTitleA("HydraMouse debug log");
        HydraLog("[HydraMouse] Debug console attached\n");
        fflush(stdout);
    }

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
    CloseLogFile();
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
            HydraLog("[HydraMouse][CALL] t=%lldms sixenseIsBaseConnected(%d) -> 1\n", NowMs() - g_enableEpochMs.load(), i);
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
            HydraLog("[HydraMouse][CALL] t=%lldms sixenseIsControllerEnabled(%d) -> %d\n", NowMs() - g_enableEpochMs.load(), which, result);
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
            HydraLog("[HydraMouse][CALL] t=%lldms sixenseGetData(which=%d) pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d\n",
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
            HydraLog("[HydraMouse][CALL] t=%lldms sixenseGetNewestData(which=%d) pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d\n",
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
            HydraLog("[HydraMouse][CALL] t=%lldms sixenseGetAllNewestData C0: pos=(%.1f,%.1f,%.1f) trig=%.2f btn=0x%03X en=%d dock=%d | C1: trig=%.2f en=%d dock=%d\n",
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
