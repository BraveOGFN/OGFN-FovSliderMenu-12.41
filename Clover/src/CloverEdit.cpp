// =====================================================================
//  Clover  -  in-game edit helper for OGFN
//
//  Inject CloverEdit.dll into FortniteClient-Win64-Shipping.exe.
//  Press H in-game to open/close the Clover menu.
//
//  How it stays fast
//   * Input is read inside the game's own message loop (WH_GETMESSAGE on the
//     game thread). Nothing sits between your mouse/keyboard and the game:
//     no low-level hooks, no polling, no extra input latency.
//   * The menu is drawn on its own thread and only while it is open.
//   * The confirm key is sent the frame right after the reset, timed off the
//     game's own message pump, so the reset is always applied first.
//
//  Engine features (FOV, real edit-state detection) find what they need by
//  READING the engine's object list and name table - Clover never calls game
//  code. If a build doesn't match, those features just switch off.
// =====================================================================

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>

#ifdef CLOVER_NOCRT
extern "C" void* memset(void* dst, int v, size_t n) {
    void* d = dst;
    __asm__ volatile("rep stosb" : "+D"(d), "+c"(n) : "a"(v) : "memory");
    return dst;
}
extern "C" void* memcpy(void* dst, const void* src, size_t n) {
    void* d = dst; const void* s = src;
    __asm__ volatile("rep movsb" : "+D"(d), "+S"(s), "+c"(n) : : "memory");
    return dst;
}
static inline float fsqrt(float x) { return __builtin_sqrtf(x); }
#define NOINLINE __attribute__((noinline))
#else
#include <math.h>
static inline float fsqrt(float x) { return sqrtf(x); }
#define NOINLINE __declspec(noinline)
#endif

#include "binds.h"
#include "colorfx.h"

#ifndef CREATE_WAITABLE_TIMER_HIGH_RESOLUTION
#define CREATE_WAITABLE_TIMER_HIGH_RESOLUTION 0x00000002
#endif

// ---------------------------------------------------------------------
//  Small helpers
// ---------------------------------------------------------------------
static inline float fmin2(float a, float b) { return a < b ? a : b; }
static inline float fmax2(float a, float b) { return a > b ? a : b; }
static inline float fabs1(float a) { return a < 0 ? -a : a; }
static inline float clamp01(float a) { return a < 0 ? 0 : (a > 1 ? 1 : a); }
static inline int   imin(int a, int b) { return a < b ? a : b; }
static inline int   imax(int a, int b) { return a > b ? a : b; }

static int wlen(const wchar_t* s) { int n = 0; while (s[n]) ++n; return n; }
static void wcopy(wchar_t* d, const wchar_t* s, int cap) {
    int i = 0; for (; s[i] && i < cap - 1; ++i) d[i] = s[i]; d[i] = 0;
}
static bool weq(const wchar_t* a, const wchar_t* b) {
    while (*a && *a == *b) { ++a; ++b; } return *a == *b;
}
static void itow(int v, wchar_t* out) {
    wchar_t tmp[16]; int n = 0; bool neg = v < 0; unsigned u = neg ? (unsigned)(-v) : (unsigned)v;
    do { tmp[n++] = (wchar_t)(L'0' + u % 10); u /= 10; } while (u);
    int i = 0; if (neg) out[i++] = L'-';
    while (n) out[i++] = tmp[--n];
    out[i] = 0;
}

// ---------------------------------------------------------------------
//  Timing
// ---------------------------------------------------------------------
static LONGLONG g_qpf;
static inline LONGLONG Qpc() { LARGE_INTEGER t; QueryPerformanceCounter(&t); return t.QuadPart; }
static inline LONGLONG Ms(double ms) { return (LONGLONG)(ms * (double)g_qpf / 1000.0); }

// ---------------------------------------------------------------------
//  Settings
// ---------------------------------------------------------------------
static const ULONG_PTR CLOVER_TAG = 0xC10FE7ED;
static const UINT      MENU_KEY   = 'H';
static const UINT      VK_WHEEL_UP   = 0x0E;   // unused VK slots = scroll wheel
static const UINT      VK_WHEEL_DOWN = 0x0F;
static inline bool IsWheel(UINT vk) { return vk == VK_WHEEL_UP || vk == VK_WHEEL_DOWN; }
static inline bool IsMouseVk(UINT vk) {
    return vk == VK_LBUTTON || vk == VK_RBUTTON || vk == VK_MBUTTON || vk == VK_XBUTTON1 || vk == VK_XBUTTON2;
}

static const int FOV_MIN = 80, FOV_MAX = 140;   // 80 = game default (off)

static HMODULE g_hMod;
static wchar_t g_iniPath[MAX_PATH];

static volatile bool g_resetOnRelease = true;
static volatile UINT g_editKey  = 'F';
static volatile UINT g_resetKey = VK_WHEEL_DOWN;
static volatile int  g_fov      = FOV_MIN;
static volatile int g_fpsMult = 1;  // FPS counter multiplier (1 = counter off)
static volatile int g_potato  = 1;   // potato graphics level (1 = off)
static volatile bool g_stretch;      // stretched resolution
static volatile int  g_stretchIdx = 4;   // index into STRETCH_W (default 1440x1080)
static volatile bool g_color;        // color booster
static volatile int  g_colorAmt = 50;
static volatile bool g_lowLat;       // low latency mode
static volatile bool g_noRender;     // no render limit (max draw distance)
static volatile LONG g_gfxDirty = 1; // engine settings need (re)applying
static volatile bool g_bubble;       // bubble wrap builds
static volatile bool g_customBuild;  // custom build colour
static volatile int  g_buildColor;   // 0 pink, 1 green, 2 blue, 3 white
static volatile LONG g_buildGen = 1; // bumps whenever a build look setting changes
static const int STRETCH_W[6] = { 1920, 1720, 1650, 1550, 1440, 1080 };
static int  g_extraDelayMs  = 0;     // added on top of the 1-frame confirm timing
static int  g_editTimeoutMs = 4000;  // fallback tracker only
static bool g_useSendInput  = false; // confirm via SendInput instead of posting to the window
static volatile bool g_instant = true;   // confirm in the SAME frame as the reset (always on)
static bool g_cancelKey[256];

static void SetDefaultCancelKeys() {
    for (int i = 0; i < 256; ++i) g_cancelKey[i] = false;
    const UINT keys[] = { '1','2','3','4','5','6','7','8','9','0','Q','E','Z','X','C','V',
                          VK_F1, VK_F2, VK_F3, VK_F4, VK_F5, VK_F6, VK_ESCAPE, VK_TAB };
    for (UINT k : keys) g_cancelKey[k] = true;
}

static void ParseCancelKeys(const wchar_t* s) {
    for (int i = 0; i < 256; ++i) g_cancelKey[i] = false;
    wchar_t tok[16];
    while (*s) {
        int n = 0;
        while (*s == L' ' || *s == L',') ++s;
        while (*s && *s != L',' && *s != L' ' && n < 15) {
            wchar_t c = *s++; if (c >= L'a' && c <= L'z') c = (wchar_t)(c - 32); tok[n++] = c;
        }
        tok[n] = 0;
        if (!n) continue;
        UINT vk = 0;
        if (n == 1) vk = tok[0];
        else if (tok[0] == L'F' && tok[1] >= L'1' && tok[1] <= L'9') {
            int f = tok[1] - L'0'; if (n == 3) f = f * 10 + (tok[2] - L'0');
            if (f >= 1 && f <= 24) vk = VK_F1 + f - 1;
        }
        else if (tok[0] == L'0' && tok[1] == L'X') {
            for (int i = 2; i < n; ++i) {
                wchar_t c = tok[i]; int d = (c >= L'0' && c <= L'9') ? c - L'0' : (c >= L'A' && c <= L'F') ? c - L'A' + 10 : 0;
                vk = vk * 16 + d;
            }
        }
        else {
            struct { const wchar_t* name; UINT vk; } names[] = {
                {L"ESC", VK_ESCAPE}, {L"ESCAPE", VK_ESCAPE}, {L"TAB", VK_TAB}, {L"SPACE", VK_SPACE},
                {L"SHIFT", VK_SHIFT}, {L"CTRL", VK_CONTROL}, {L"ALT", VK_MENU}, {L"CAPS", VK_CAPITAL} };
            for (auto& nm : names) if (weq(nm.name, tok)) { vk = nm.vk; break; }
        }
        if (vk && vk < 256) g_cancelKey[vk] = true;
    }
}

static void LoadSettings() {
    GetModuleFileNameW(g_hMod, g_iniPath, MAX_PATH);
    int n = wlen(g_iniPath);
    while (n > 0 && g_iniPath[n - 1] != L'.' && g_iniPath[n - 1] != L'\\') --n;
    if (n > 0 && g_iniPath[n - 1] == L'.') { g_iniPath[n] = 0; wcopy(g_iniPath + n, L"ini", 4); }
    else wcopy(g_iniPath + wlen(g_iniPath), L".ini", 5);

    const wchar_t* S = L"Clover";
    g_resetOnRelease = GetPrivateProfileIntW(S, L"ResetOnRelease", 1, g_iniPath) != 0;
    g_editKey        = GetPrivateProfileIntW(S, L"EditKey", 'F', g_iniPath);
    g_resetKey       = GetPrivateProfileIntW(S, L"ResetKey", VK_WHEEL_DOWN, g_iniPath);
    g_fov            = GetPrivateProfileIntW(S, L"Fov", FOV_MIN, g_iniPath);
    g_fpsMult        = GetPrivateProfileIntW(S, L"FpsMultiplier", 1, g_iniPath);
    g_potato         = GetPrivateProfileIntW(S, L"Potato", 1, g_iniPath);
    if (g_fpsMult < 1 || g_fpsMult > 10) g_fpsMult = 1;
    if (g_potato < 1 || g_potato > 10) g_potato = 1;
    g_stretch    = false;                     // stretched res removed (never switches your monitor)
    g_stretchIdx = GetPrivateProfileIntW(S, L"StretchedRes", 4, g_iniPath);
    g_color      = GetPrivateProfileIntW(S, L"ColorBooster", 0, g_iniPath) != 0;
    g_colorAmt   = GetPrivateProfileIntW(S, L"ColorAmount", 50, g_iniPath);
    g_lowLat     = GetPrivateProfileIntW(S, L"LowLatency", 0, g_iniPath) != 0;
    g_noRender   = false;                     // no render limit removed
    g_bubble      = false;                    // bubble wrap builds removed
    g_customBuild = false;                    // custom builds removed
    g_buildColor  = GetPrivateProfileIntW(S, L"BuildColor", 0, g_iniPath);
    if (g_buildColor < 0 || g_buildColor > 3) g_buildColor = 0;
    if (g_stretchIdx < 0 || g_stretchIdx > 5) g_stretchIdx = 4;
    if (g_colorAmt < 1 || g_colorAmt > 100) g_colorAmt = 50;
    g_extraDelayMs   = GetPrivateProfileIntW(S, L"ExtraDelayMs", 0, g_iniPath);
    g_editTimeoutMs  = GetPrivateProfileIntW(S, L"EditTimeoutMs", 4000, g_iniPath);
    g_useSendInput   = GetPrivateProfileIntW(S, L"UseSendInput", 0, g_iniPath) != 0;
    if (g_editKey == 0 || g_editKey > 255 || IsWheel(g_editKey)) g_editKey = 'F';
    if (g_resetKey == 0 || g_resetKey > 255 || g_resetKey == g_editKey) g_resetKey = VK_WHEEL_DOWN;
    if (g_fov < FOV_MIN || g_fov > FOV_MAX) g_fov = FOV_MIN;
    if (g_extraDelayMs < 0 || g_extraDelayMs > 100) g_extraDelayMs = 0;

    wchar_t buf[256];
    GetPrivateProfileStringW(S, L"CancelKeys", L"", buf, 256, g_iniPath);
    if (buf[0]) ParseCancelKeys(buf); else SetDefaultCancelKeys();
}

static void SaveSettings() {
    const wchar_t* S = L"Clover";
    wchar_t num[16];
    WritePrivateProfileStringW(S, L"ResetOnRelease", g_resetOnRelease ? L"1" : L"0", g_iniPath);
    itow((int)g_editKey, num);   WritePrivateProfileStringW(S, L"EditKey", num, g_iniPath);
    itow((int)g_resetKey, num);  WritePrivateProfileStringW(S, L"ResetKey", num, g_iniPath);
    itow(g_fov, num);            WritePrivateProfileStringW(S, L"Fov", num, g_iniPath);
    itow(g_fpsMult, num);        WritePrivateProfileStringW(S, L"FpsMultiplier", num, g_iniPath);
    itow(g_potato, num);         WritePrivateProfileStringW(S, L"Potato", num, g_iniPath);
    WritePrivateProfileStringW(S, L"Stretched", g_stretch ? L"1" : L"0", g_iniPath);
    itow(g_stretchIdx, num);     WritePrivateProfileStringW(S, L"StretchedRes", num, g_iniPath);
    WritePrivateProfileStringW(S, L"ColorBooster", g_color ? L"1" : L"0", g_iniPath);
    itow(g_colorAmt, num);       WritePrivateProfileStringW(S, L"ColorAmount", num, g_iniPath);
    WritePrivateProfileStringW(S, L"LowLatency", g_lowLat ? L"1" : L"0", g_iniPath);
    WritePrivateProfileStringW(S, L"NoRenderLimit", g_noRender ? L"1" : L"0", g_iniPath);
    WritePrivateProfileStringW(S, L"BubbleWrap", g_bubble ? L"1" : L"0", g_iniPath);
    WritePrivateProfileStringW(S, L"CustomBuilds", g_customBuild ? L"1" : L"0", g_iniPath);
    itow(g_buildColor, num);     WritePrivateProfileStringW(S, L"BuildColor", num, g_iniPath);
    itow(g_extraDelayMs, num);   WritePrivateProfileStringW(S, L"ExtraDelayMs", num, g_iniPath);
    itow(g_editTimeoutMs, num);  WritePrivateProfileStringW(S, L"EditTimeoutMs", num, g_iniPath);
    WritePrivateProfileStringW(S, L"UseSendInput", g_useSendInput ? L"1" : L"0", g_iniPath);
}

// ---------------------------------------------------------------------
//  Log file (CloverEdit.log next to the DLL) - engine lookup diagnostics
// ---------------------------------------------------------------------
static wchar_t g_logPath[MAX_PATH];
static int g_logLines;
static void LogRaw(const char* s, int n) {
    if (++g_logLines > 300) return;
    if (!g_logPath[0]) {
        wcopy(g_logPath, g_iniPath, MAX_PATH);
        int k = wlen(g_logPath);
        if (k > 3) { g_logPath[k - 3] = L'l'; g_logPath[k - 2] = L'o'; g_logPath[k - 1] = L'g'; }
    }
    static bool fresh = true;     // start a new log each launch
    HANDLE f = CreateFileW(g_logPath, FILE_APPEND_DATA, FILE_SHARE_READ, nullptr, fresh ? CREATE_ALWAYS : OPEN_ALWAYS,
                           FILE_ATTRIBUTE_NORMAL, nullptr);
    fresh = false;
    if (f == INVALID_HANDLE_VALUE) return;
    DWORD w; WriteFile(f, s, (DWORD)n, &w, nullptr); CloseHandle(f);
}
// Log("text", value) -> "text 0x1234\r\n" ; value < 0 omits the number
static void Log(const char* msg, LONG_PTR v = -1, const wchar_t* wextra = nullptr) {
    char buf[512]; int n = 0;
    while (*msg && n < 300) buf[n++] = *msg++;
    if (wextra) { buf[n++] = ' '; while (*wextra && n < 480) buf[n++] = (char)*wextra++; }
    if (v >= 0) {
        buf[n++] = ' '; buf[n++] = '0'; buf[n++] = 'x';
        char hex[20]; int h = 0; ULONG_PTR u = (ULONG_PTR)v;
        do { int d = (int)(u & 15); hex[h++] = (char)(d < 10 ? '0' + d : 'A' + d - 10); u >>= 4; } while (u);
        while (h) buf[n++] = hex[--h];
    }
    buf[n++] = '\r'; buf[n++] = '\n';
    LogRaw(buf, n);
}


// ---------------------------------------------------------------------
//  Your Fortnite keybinds, read from the game's own settings save
//  (%LOCALAPPDATA%\FortniteGame\Saved\Cloud\<account>\ClientSettings.Sav)
//  Re-read automatically whenever the game saves new binds.
// ---------------------------------------------------------------------
static wchar_t  g_bindsFile[MAX_PATH];
static FILETIME g_bindsTime;
static bool     g_bindsFromGame;

static bool NewestClientSettings(wchar_t* out, FILETIME* when) {
    wchar_t dir[MAX_PATH];
    DWORD n = GetEnvironmentVariableW(L"LOCALAPPDATA", dir, MAX_PATH);
    if (!n || n > MAX_PATH - 80) return false;
    wcopy(dir + n, L"\\FortniteGame\\Saved\\Cloud\\", MAX_PATH - n);
    int dlen = wlen(dir);
    wchar_t pat[MAX_PATH]; wcopy(pat, dir, MAX_PATH); wcopy(pat + dlen, L"*", MAX_PATH - dlen);
    WIN32_FIND_DATAW fd;
    HANDLE h = FindFirstFileW(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) return false;
    bool found = false;
    do {
        if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) || fd.cFileName[0] == L'.') continue;
        wchar_t f[MAX_PATH]; wcopy(f, dir, MAX_PATH);
        int k = wlen(f); wcopy(f + k, fd.cFileName, MAX_PATH - k);
        k = wlen(f); wcopy(f + k, L"\\ClientSettings.Sav", MAX_PATH - k);
        WIN32_FILE_ATTRIBUTE_DATA a;
        if (!GetFileAttributesExW(f, GetFileExInfoStandard, &a)) continue;
        if (!found || CompareFileTime(&a.ftLastWriteTime, when) > 0) { *when = a.ftLastWriteTime; wcopy(out, f, MAX_PATH); found = true; }
    } while (FindNextFileW(h, &fd));
    FindClose(h);
    return found;
}

// Returns true if binds changed.
static bool LoadGameBinds(bool force) {
    wchar_t path[MAX_PATH]; FILETIME t = {};
    if (!NewestClientSettings(path, &t)) return false;
    if (!force && weq(path, g_bindsFile) && CompareFileTime(&t, &g_bindsTime) == 0) return false;
    wcopy(g_bindsFile, path, MAX_PATH); g_bindsTime = t;

    HANDLE f = CreateFileW(path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, nullptr, OPEN_EXISTING, 0, nullptr);
    if (f == INVALID_HANDLE_VALUE) return false;
    DWORD size = GetFileSize(f, nullptr), got = 0;
    if (size == INVALID_FILE_SIZE || size < 32 || size > (8u << 20)) { CloseHandle(f); return false; }
    BYTE* file = (BYTE*)VirtualAlloc(nullptr, size, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    bool ok = file && ReadFile(f, file, size, &got, nullptr) && got == size;
    CloseHandle(f);
    bool changed = false;
    if (ok) {
        binds::u32 dsz = binds::DecompressedSize(file, size);
        BYTE* data = dsz && dsz < (64u << 20) ? (BYTE*)VirtualAlloc(nullptr, dsz, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE) : nullptr;
        binds::u32 n = data ? binds::Decompress(file, size, data, dsz) : 0;
        char ek[64], rk[64];
        UINT evk = 0, rvk = 0;
        if (n && binds::FindBind(data, n, "PerformBuildingEditInteraction", ek, 64)) evk = binds::KeyToVk(ek);
        if (n && binds::FindBind(data, n, "BuildingEditReset", rk, 64))              rvk = binds::KeyToVk(rk);
        if (evk && !IsWheel(evk) && evk != g_editKey)  { g_editKey = evk; changed = true; }
        if (rvk && rvk != evk && rvk != g_resetKey)    { g_resetKey = rvk; changed = true; }
        g_bindsFromGame = evk && rvk;
        wchar_t w[80]; int i = 0;
        const char* a = evk ? ek : "?"; while (*a && i < 38) w[i++] = (wchar_t)*a++;
        w[i++] = L' '; w[i++] = L'/'; w[i++] = L' ';
        a = rvk ? rk : "?"; while (*a && i < 78) w[i++] = (wchar_t)*a++;
        w[i] = 0;
        Log("binds from game save (edit / reset):", -1, w);
        if (data) VirtualFree(data, 0, MEM_RELEASE);
    }
    if (file) VirtualFree(file, 0, MEM_RELEASE);
    return changed;
}

// ---------------------------------------------------------------------
//  Color booster: NVIDIA Digital Vibrance through the driver's own API
//  (nvapi64.dll). Only boosted while Fortnite is the focused window;
//  your normal vibrance comes back on alt-tab, when turned off, and on exit.
// ---------------------------------------------------------------------
struct NvDvcInfo { unsigned version; int current, minLevel, maxLevel; };
typedef void* (*NvQI_t)(unsigned id);
typedef int (*NvInit_t)();
typedef int (*NvEnum_t)(int index, void** handle);
typedef int (*NvName_t)(void* handle, char* name);
typedef int (*NvOutId_t)(void* handle, unsigned* outputId);
typedef int (*NvGetDvc_t)(void* handle, unsigned outputId, NvDvcInfo* info);
typedef int (*NvSetDvc_t)(void* handle, unsigned outputId, int level);
static NvEnum_t   g_nvEnum;
static NvName_t   g_nvName;
static NvOutId_t  g_nvOutId;
static NvGetDvc_t g_nvGet;
static NvSetDvc_t g_nvSet;
static bool       g_nvOK, g_nvTried;
static volatile bool g_nvNotOnGame;          // Fortnite's monitor isn't driven by the NVIDIA card
static void*      g_nvHandle;                 // the display Fortnite is on
static unsigned   g_nvOut;
static int        g_nvOrig, g_nvMax;
static int        g_nvApplied = -1;          // -1 = original level
static wchar_t    g_nvForDev[CCHDEVICENAME];
extern HWND g_game;
static void Log(const char* msg, LONG_PTR v, const wchar_t* wextra);

static bool NvInit() {
    if (g_nvTried) return g_nvOK;
    g_nvTried = true;
    HMODULE nv = LoadLibraryW(L"nvapi64.dll");
    if (!nv) return false;
    NvQI_t qi = (NvQI_t)GetProcAddress(nv, "nvapi_QueryInterface");
    if (!qi) return false;
    NvInit_t init = (NvInit_t)qi(0x0150E828);
    g_nvEnum  = (NvEnum_t)qi(0x9ABDD40D);
    g_nvName  = (NvName_t)qi(0x22A78B05);
    g_nvOutId = (NvOutId_t)qi(0xD995937E);
    g_nvGet   = (NvGetDvc_t)qi(0x4085DE45);
    g_nvSet   = (NvSetDvc_t)qi(0x172409B4);
    if (!init || !g_nvEnum || !g_nvName || !g_nvGet || !g_nvSet || init() != 0) { Log("color booster: NVAPI unavailable", -1, nullptr); return false; }
    g_nvOK = true;
    return true;
}

// Finds the NVIDIA display handle for the monitor Fortnite is on (by its \\.\DISPLAYn name).
static int g_nvLastSet = -1000;
static bool NvBindToGameMonitor() {
    HMONITOR mon = MonitorFromWindow(g_game, MONITOR_DEFAULTTONEAREST);
    MONITORINFOEXW mi; mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(mon, &mi)) return false;
    if (weq(mi.szDevice, g_nvForDev)) { if (g_nvHandle) return true; if (g_nvNotOnGame) return false; }
    wcopy(g_nvForDev, mi.szDevice, CCHDEVICENAME);
    g_nvHandle = nullptr; g_nvNotOnGame = false;
    for (int i = 0; i < 16; ++i) {
        void* h = nullptr;
        if (g_nvEnum(i, &h) != 0 || !h) break;
        char name[64] = {};
        if (g_nvName(h, name) != 0) continue;
        wchar_t wname[64]; int k = 0; while (name[k] && k < 63) { wname[k] = (wchar_t)name[k]; ++k; } wname[k] = 0;
        Log("color booster: NVIDIA display", i, wname);
        if (!weq(wname, mi.szDevice)) continue;
        unsigned out = 0;
        if (g_nvOutId) g_nvOutId(h, &out);
        NvDvcInfo info = { (unsigned)sizeof(NvDvcInfo) | (1u << 16), 0, 0, 0 };
        int r = g_nvGet(h, out, &info);
        if (r != 0) { info.version = (unsigned)sizeof(NvDvcInfo) | (1u << 16); out = 0; r = g_nvGet(h, 0, &info); }
        if (r != 0) { Log("color booster: vibrance not available on that display, code:", -r, nullptr); break; }
        g_nvHandle = h; g_nvOut = out; g_nvMax = info.maxLevel;
        // Your normal vibrance. Remembered across launches so a boost left behind by a crash or an
        // older Clover build is never mistaken for "normal" (driver default is the minimum level).
        int saved = GetPrivateProfileIntW(L"Clover", L"NormalVibrance", -1000, g_iniPath);
        if (saved != -1000) g_nvOrig = saved;
        else {
            // first time: your current level is your normal - unless it's pinned at max (left over), then the driver default
            g_nvOrig = info.current;
            wchar_t num[16]; itow(g_nvOrig, num);
            WritePrivateProfileStringW(L"Clover", L"NormalVibrance", num, g_iniPath);
        }
        if (info.current != g_nvOrig) g_nvSet(h, out, g_nvOrig);   // undo a leftover boost right away
        g_nvApplied = 0;
        g_nvLastSet = g_nvOrig;
        Log("color booster bound to Fortnite's monitor; current / max:", info.current * 1000 + info.maxLevel, mi.szDevice);
        return true;
    }
    g_nvNotOnGame = true;
    Log("color booster: Fortnite's monitor is not on the NVIDIA card", -1, mi.szDevice);
    return false;
}

// amount 0 = your original vibrance, 1..100 = boosted towards the driver's maximum
static void NvSaveNormal() { wchar_t num[16]; itow(g_nvOrig, num); WritePrivateProfileStringW(L"Clover", L"NormalVibrance", num, g_iniPath); }
static void NvApply(int amount) {
    if (!g_nvOK) return;
    if (amount > 0 && !NvBindToGameMonitor()) return;
    if (!g_nvHandle || amount == g_nvApplied) return;
    if (g_nvApplied <= 0 && amount > 0) {
        // About to boost from your normal level. If you changed vibrance yourself (NVIDIA Control Panel)
        // since Clover last touched it, that's your new normal: remember it and come back to exactly that.
        NvDvcInfo info = { (unsigned)sizeof(NvDvcInfo) | (1u << 16), 0, 0, 0 };
        if (g_nvGet(g_nvHandle, g_nvOut, &info) == 0 && g_nvLastSet != -1000 && info.current != g_nvLastSet &&
            info.current != g_nvOrig && info.current < info.maxLevel) {
            g_nvOrig = info.current; NvSaveNormal();
            Log("color booster: you changed vibrance yourself - new normal level:", g_nvOrig, nullptr);
        }
    }
    int level = amount <= 0 ? g_nvOrig : g_nvOrig + (g_nvMax - g_nvOrig) * amount / 100;
    g_nvSet(g_nvHandle, g_nvOut, level);
    g_nvLastSet = level;
    g_nvApplied = amount;
}


// ---------------------------------------------------------------------
//  Color booster for AMD: Radeon "Saturation" through AMD's driver API
//  (atiadlxx.dll / ADL), on the monitor Fortnite is on.
// ---------------------------------------------------------------------
struct AdlAdapterInfo {
    int iSize, iAdapterIndex; char strUDID[256]; int iBusNumber, iDeviceNumber, iFunctionNumber, iVendorID;
    char strAdapterName[256]; char strDisplayName[256]; int iPresent, iExist;
    char strDriverPath[256]; char strDriverPathExt[256]; char strPNPString[256]; int iOSDisplayIndex;
};
struct AdlDisplayInfo {
    int iLogical, iPhysical, iLogicalAdapter, iPhysicalAdapter;
    int iDisplayControllerIndex; char strDisplayName[256]; char strManufacturer[256];
    int iDisplayType, iDisplayOutputType, iDisplayConnector, iDisplayInfoMask, iDisplayInfoValue;
};
typedef void* (__stdcall* AdlMalloc_t)(int);
typedef int (*AdlCreate_t)(AdlMalloc_t, int, void**);
typedef int (*AdlNumAdapters_t)(void*, int*);
typedef int (*AdlAdapterInfo_t)(void*, AdlAdapterInfo*, int);
typedef int (*AdlDisplayInfo_t)(void*, int, int*, AdlDisplayInfo**, int);
typedef int (*AdlColorGet_t)(void*, int, int, int, int*, int*, int*, int*, int*);
typedef int (*AdlColorSet_t)(void*, int, int, int, int);
static void* __stdcall AdlAlloc(int size) { return HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, (SIZE_T)size); }
static const int ADL_COLOR_SATURATION = 1 << 2;

static void*            g_adl;
static AdlColorGet_t    g_adlGet;
static AdlColorSet_t    g_adlSet;
static AdlNumAdapters_t g_adlNum;
static AdlAdapterInfo_t g_adlInfo;
static AdlDisplayInfo_t g_adlDisp;
static bool             g_adlOK;
static int              g_adlAdapter = -1, g_adlDisplay = -1, g_adlOrig, g_adlMax, g_adlApplied = -1;
static wchar_t          g_adlForDev[CCHDEVICENAME];

static bool AdlInit() {
    HMODULE m = LoadLibraryW(L"atiadlxx.dll");
    if (!m) return false;
    AdlCreate_t create = (AdlCreate_t)GetProcAddress(m, "ADL2_Main_Control_Create");
    g_adlNum  = (AdlNumAdapters_t)GetProcAddress(m, "ADL2_Adapter_NumberOfAdapters_Get");
    g_adlInfo = (AdlAdapterInfo_t)GetProcAddress(m, "ADL2_Adapter_AdapterInfo_Get");
    g_adlDisp = (AdlDisplayInfo_t)GetProcAddress(m, "ADL2_Display_DisplayInfo_Get");
    g_adlGet  = (AdlColorGet_t)GetProcAddress(m, "ADL2_Display_Color_Get");
    g_adlSet  = (AdlColorSet_t)GetProcAddress(m, "ADL2_Display_Color_Set");
    if (!create || !g_adlNum || !g_adlInfo || !g_adlDisp || !g_adlGet || !g_adlSet) return false;
    if (create(AdlAlloc, 1, &g_adl) != 0 || !g_adl) return false;
    g_adlOK = true;
    Log("color booster: AMD driver found", -1, nullptr);
    return true;
}

static bool AdlBindToGameMonitor() {
    HMONITOR mon = MonitorFromWindow(g_game, MONITOR_DEFAULTTONEAREST);
    MONITORINFOEXW mi; mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(mon, &mi)) return false;
    if (weq(mi.szDevice, g_adlForDev)) return g_adlDisplay >= 0;
    wcopy(g_adlForDev, mi.szDevice, CCHDEVICENAME);
    g_adlAdapter = g_adlDisplay = -1;
    int n = 0;
    if (g_adlNum(g_adl, &n) != 0 || n <= 0 || n > 64) return false;
    AdlAdapterInfo* ai = (AdlAdapterInfo*)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(AdlAdapterInfo) * n);
    if (!ai) return false;
    for (int i = 0; i < n; ++i) ai[i].iSize = sizeof(AdlAdapterInfo);
    if (g_adlInfo(g_adl, ai, (int)sizeof(AdlAdapterInfo) * n) == 0) {
        for (int i = 0; i < n && g_adlDisplay < 0; ++i) {
            wchar_t w[64]; int k = 0; while (ai[i].strDisplayName[k] && k < 63) { w[k] = (wchar_t)ai[i].strDisplayName[k]; ++k; } w[k] = 0;
            if (!weq(w, mi.szDevice)) continue;
            int nd = 0; AdlDisplayInfo* di = nullptr;
            if (g_adlDisp(g_adl, ai[i].iAdapterIndex, &nd, &di, 0) == 0 && di) {
                for (int d = 0; d < nd; ++d)
                    if ((di[d].iDisplayInfoValue & 3) == 3 && di[d].iLogicalAdapter == ai[i].iAdapterIndex) {
                        g_adlAdapter = ai[i].iAdapterIndex; g_adlDisplay = di[d].iLogical; break;
                    }
                HeapFree(GetProcessHeap(), 0, di);
            }
        }
    }
    HeapFree(GetProcessHeap(), 0, ai);
    if (g_adlDisplay < 0) { Log("color booster: Fortnite's monitor is not on the AMD card", -1, mi.szDevice); return false; }
    int cur = 0, def = 0, mn = 0, mx = 0, step = 0;
    if (g_adlGet(g_adl, g_adlAdapter, g_adlDisplay, ADL_COLOR_SATURATION, &cur, &def, &mn, &mx, &step) != 0) {
        Log("color booster: saturation not available on that display", -1, nullptr); g_adlDisplay = -1; return false;
    }
    g_adlMax = mx;
    int saved = GetPrivateProfileIntW(L"Clover", L"NormalSaturation", -1000, g_iniPath);
    if (saved != -1000) g_adlOrig = saved;
    else {
        g_adlOrig = cur;
        wchar_t num[16]; itow(g_adlOrig, num); WritePrivateProfileStringW(L"Clover", L"NormalSaturation", num, g_iniPath);
    }
    if (cur != g_adlOrig) g_adlSet(g_adl, g_adlAdapter, g_adlDisplay, ADL_COLOR_SATURATION, g_adlOrig);
    g_adlApplied = 0;
    Log("color booster bound (AMD) - normal / max:", g_adlOrig * 1000 + mx, mi.szDevice);
    return true;
}

static void AdlApply(int amount) {
    if (!g_adlOK) return;
    if (amount > 0 && !AdlBindToGameMonitor()) return;
    if (g_adlDisplay < 0 || amount == g_adlApplied) return;
    int level = amount <= 0 ? g_adlOrig : g_adlOrig + (g_adlMax - g_adlOrig) * amount / 100;
    g_adlSet(g_adl, g_adlAdapter, g_adlDisplay, ADL_COLOR_SATURATION, level);
    g_adlApplied = amount;
}

// One entry point for both vendors.
static bool g_colorTried, g_colorAvail;
static void ColorApply(int amount) {
    if (!g_colorTried) {
        g_colorTried = true;
        bool nv = NvInit();
        bool amd = AdlInit();
        g_colorAvail = nv || amd;
        if (!g_colorAvail) Log("color booster: no NVIDIA or AMD driver interface found", -1, nullptr);
    }
    if (g_nvOK) NvApply(amount);
    if (g_adlOK) AdlApply(amount);
}

// ---------------------------------------------------------------------
//  Stretched res: switches the monitor Fortnite is on to e.g. 1440x1080 with
//  FULL-SCREEN STRETCH scaling (no black bars), keeping your refresh rate.
//  It's a temporary mode (CDS_FULLSCREEN): Windows puts your normal
//  resolution back by itself when Fortnite closes, even after a crash.
// ---------------------------------------------------------------------
static volatile int g_dispApplied = -1;      // STRETCH_W index currently on the monitor, -1 = normal
static volatile bool g_stretchFailed;
static wchar_t g_dispDev[CCHDEVICENAME];
extern HWND g_game;
static void Log(const char* msg, LONG_PTR v, const wchar_t* wextra);

static volatile bool g_stretchAvail[6];
static volatile bool g_stretchAvailKnown;
static DWORD g_stretchHz[6];
static int StretchList(int* out) {
    int n = 0;
    for (int i = 0; i < 6; ++i) if (!g_stretchAvailKnown || g_stretchAvail[i]) out[n++] = i;
    if (!n) out[n++] = 0;
    return n;
}
static void RequestRedraw();
// Which of the 6 resolutions this monitor can do (and the best refresh rate for each).
static void ScanStretchModes() {
    HMONITOR mon = MonitorFromWindow(g_game, MONITOR_DEFAULTTONEAREST);
    MONITORINFOEXW mi; mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(mon, &mi)) return;
    DEVMODEW reg = {}; reg.dmSize = sizeof(reg);
    EnumDisplaySettingsW(mi.szDevice, ENUM_REGISTRY_SETTINGS, &reg);
    for (int i = 0; i < 6; ++i) { g_stretchAvail[i] = false; g_stretchHz[i] = 0; }
    DEVMODEW dm = {}; dm.dmSize = sizeof(dm);
    for (DWORD m = 0; EnumDisplaySettingsW(mi.szDevice, m, &dm); ++m) {
        if (dm.dmPelsHeight != 1080) continue;
        for (int i = 0; i < 6; ++i)
            if (dm.dmPelsWidth == (DWORD)STRETCH_W[i] && dm.dmDisplayFrequency <= reg.dmDisplayFrequency + 1 &&
                dm.dmDisplayFrequency > g_stretchHz[i]) { g_stretchAvail[i] = true; g_stretchHz[i] = dm.dmDisplayFrequency; }
    }
    g_stretchAvailKnown = true;
    for (int i = 0; i < 6; ++i) Log(g_stretchAvail[i] ? "stretched res available (Hz):" : "stretched res NOT offered by monitor:",
                                    g_stretchAvail[i] ? (LONG_PTR)g_stretchHz[i] : STRETCH_W[i], nullptr);
}

static bool SetStretchMode(int idx) {
    if (idx < 0) {
        if (g_dispDev[0]) ChangeDisplaySettingsExW(g_dispDev, nullptr, nullptr, 0, nullptr);   // back to your saved mode
        return true;
    }
    HMONITOR mon = MonitorFromWindow(g_game, MONITOR_DEFAULTTONEAREST);
    MONITORINFOEXW mi; mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(mon, &mi)) return false;
    wcopy(g_dispDev, mi.szDevice, CCHDEVICENAME);
    DEVMODEW cur = {}; cur.dmSize = sizeof(cur);
    EnumDisplaySettingsW(g_dispDev, ENUM_REGISTRY_SETTINGS, &cur);
    DEVMODEW dm = {}; dm.dmSize = sizeof(dm);
    dm.dmPelsWidth = STRETCH_W[idx]; dm.dmPelsHeight = 1080;
    dm.dmDisplayFrequency = g_stretchHz[idx] ? g_stretchHz[idx] : cur.dmDisplayFrequency;
    dm.dmDisplayFixedOutput = DMDFO_STRETCH;
    const DWORD tries[3] = {
        DM_PELSWIDTH | DM_PELSHEIGHT | DM_DISPLAYFREQUENCY | DM_DISPLAYFIXEDOUTPUT,
        DM_PELSWIDTH | DM_PELSHEIGHT | DM_DISPLAYFIXEDOUTPUT,
        DM_PELSWIDTH | DM_PELSHEIGHT | DM_DISPLAYFREQUENCY };
    for (DWORD f : tries) {
        dm.dmFields = f;
        LONG r = ChangeDisplaySettingsExW(g_dispDev, &dm, nullptr, CDS_FULLSCREEN, nullptr);
        if (r == DISP_CHANGE_SUCCESSFUL) { Log("stretched display mode set, width:", STRETCH_W[idx], nullptr); return true; }
        Log("display mode attempt failed, code:", -r, nullptr);
    }
    return false;
}

// UI thread: keep the monitor mode in line with the menu.
static void UpdateStretchDisplay() {
    if (!g_stretchAvailKnown && g_game) ScanStretchModes();
    if (!g_stretchAvail[g_stretchIdx]) {            // saved choice not on this monitor: nearest one that is
        int l[6]; int n = StretchList(l), best = l[0];
        for (int i = 0; i < n; ++i) if (l[i] <= g_stretchIdx) best = l[i];
        g_stretchIdx = best; RequestRedraw();
    }
    int want = g_stretch && g_stretchAvail[g_stretchIdx] && g_stretchIdx != 0 ? g_stretchIdx : -1;   // 1920 = normal
    if (want == g_dispApplied) return;
    if (!SetStretchMode(want)) {                     // didn't take: go back to normal, don't get stuck
        Log("stretched res: switch failed", STRETCH_W[want], nullptr);
        g_stretchAvail[want] = false;
        want = -1; SetStretchMode(-1);
    }
    g_dispApplied = want;
    g_gfxDirty = 1;                                  // let the game resize to match
}

// ---------------------------------------------------------------------
//  Game window
// ---------------------------------------------------------------------
HWND  g_game;
static DWORD g_gameTid;
static HWND  g_overlay;

static BOOL CALLBACK EnumProc(HWND h, LPARAM lp) {
    DWORD pid = 0; GetWindowThreadProcessId(h, &pid);
    if (pid != GetCurrentProcessId() || h == g_overlay || !IsWindowVisible(h)) return TRUE;
    wchar_t cls[64]; GetClassNameW(h, cls, 64);
    HWND* best = (HWND*)lp;
    if (weq(cls, L"UnrealWindow")) { *best = h; return FALSE; }
    if (!*best) *best = h;
    return TRUE;
}
static HWND FindGameWindow() { HWND h = nullptr; EnumWindows(EnumProc, (LPARAM)&h); return h; }

static bool GameFocused() {
    HWND g = g_game;
    return g && GetForegroundWindow() == g && !IsIconic(g);
}

// ---------------------------------------------------------------------
//  Safe memory access. Engine lookups ONLY READ memory - Clover never calls
//  into game code, so a mismatch can't crash the game; the feature just
//  switches off.
// ---------------------------------------------------------------------
static bool ProtReadable(DWORD p) {
    return !(p & (PAGE_NOACCESS | PAGE_GUARD)) &&
           (p & (PAGE_READONLY | PAGE_READWRITE | PAGE_WRITECOPY | PAGE_EXECUTE_READ |
                 PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY));
}
static bool Readable(const void* p, size_t n) {
    ULONG_PTR a = (ULONG_PTR)p;
    if (a < 0x10000 || a > 0x7FFFFFFEFFFFull) return false;
    MEMORY_BASIC_INFORMATION mbi;
    if (!VirtualQuery(p, &mbi, sizeof(mbi)) || mbi.State != MEM_COMMIT || !ProtReadable(mbi.Protect)) return false;
    return a + n <= (ULONG_PTR)mbi.BaseAddress + mbi.RegionSize;
}
static bool Writable(const void* p, size_t n) {
    ULONG_PTR a = (ULONG_PTR)p;
    if (a < 0x10000 || a > 0x7FFFFFFEFFFFull) return false;
    MEMORY_BASIC_INFORMATION mbi;
    if (!VirtualQuery(p, &mbi, sizeof(mbi)) || mbi.State != MEM_COMMIT) return false;
    if (mbi.Protect & (PAGE_NOACCESS | PAGE_GUARD)) return false;
    if (!(mbi.Protect & (PAGE_READWRITE | PAGE_EXECUTE_READWRITE))) return false;
    return a + n <= (ULONG_PTR)mbi.BaseAddress + mbi.RegionSize;
}
template <class T> static bool Rd(const void* base, LONG_PTR off, T* out) {
    if (!base) return false;
    const char* p = (const char*)base + off;
    if (!Readable(p, sizeof(T))) return false;
    *out = *(const T*)p; return true;
}

// Region cache for the one-time big scans (engine thread only).
struct RegionCache { ULONG_PTR base[64], end[64]; bool ok[64]; int next; };
static RegionCache g_rc;
static bool ReadableFastC(RegionCache& rc, ULONG_PTR a, size_t n) {
    if (a < 0x10000 || a > 0x7FFFFFFEFFFFull) return false;
    for (int i = 0; i < 64; ++i)
        if (rc.end[i] && a >= rc.base[i] && a + n <= rc.end[i]) return rc.ok[i];
    MEMORY_BASIC_INFORMATION mbi;
    if (!VirtualQuery((void*)a, &mbi, sizeof(mbi))) return false;
    int s = rc.next; rc.next = (rc.next + 1) & 63;
    rc.base[s] = (ULONG_PTR)mbi.BaseAddress; rc.end[s] = rc.base[s] + mbi.RegionSize;
    rc.ok[s] = mbi.State == MEM_COMMIT && ProtReadable(mbi.Protect);
    return rc.ok[s] && a + n <= rc.end[s];
}
static bool ReadableFast(ULONG_PTR a, size_t n) { return ReadableFastC(g_rc, a, n); }
template <class T> static bool RdF(const void* base, LONG_PTR off, T* out) {
    if (!base) return false;
    ULONG_PTR p = (ULONG_PTR)base + off;
    if (!ReadableFast(p, sizeof(T))) return false;
    *out = *(const T*)p; return true;
}

static bool BytesEq(const BYTE* p, const char* s) { while (*s) if (*p++ != (BYTE)*s++) return false; return true; }

// ---------------------------------------------------------------------
//  Engine data (UE 4.23+ name pool, chunked object array; built for 17.30)
// ---------------------------------------------------------------------
static volatile bool g_reflOK;     // object chain available
static volatile bool g_reflGaveUp; // this build isn't supported
static volatile bool g_fovOK;      // LockedFOV found
static void* g_engine;
static void* g_editToolClass;
static LONG_PTR g_superOff;        // UStruct::SuperStruct
static LONG_PTR o_GameViewport = -1, o_World = -1, o_GameInstance = -1, o_LocalPlayers = -1,
                o_PlayerController = -1, o_CameraManager = -1, o_LockedFOV = -1,
                o_Pawn = -1, o_CurrentWeapon = -1;

static BYTE** g_nameBlocks;        // FNamePool::Blocks
static BYTE** g_objChunks;         // FChunkedFixedUObjectArray::Objects
static int    g_objNum;
static int    g_itemSize;
static BYTE*  g_objArrayAddr;

struct ExeSection { BYTE* p; size_t n; };
static int WritableSections(ExeSection* out, int max) {
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    auto nt = (IMAGE_NT_HEADERS64*)(base + ((IMAGE_DOS_HEADER*)base)->e_lfanew);
    auto sec = IMAGE_FIRST_SECTION(nt);
    int n = 0;
    for (int i = 0; i < nt->FileHeader.NumberOfSections && n < max; ++i)
        if (sec[i].Characteristics & IMAGE_SCN_MEM_WRITE) {
            out[n].p = base + sec[i].VirtualAddress; out[n].n = sec[i].Misc.VirtualSize; ++n;
        }
    return n;
}

// Name block 0 always starts with "None" then "ByteProperty".
static bool FindNamePool() {
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    ExeSection secs[16]; int ns = WritableSections(secs, 16);
    for (int s = 0; s < ns; ++s) {
        ULONG_PTR* q = (ULONG_PTR*)secs[s].p;
        size_t count = secs[s].n / 8;
        for (size_t k = 0; k < count; ++k) {
            ULONG_PTR v = q[k];
            if ((v & 1) || !ReadableFast(v, 24)) continue;
            const BYTE* e = (const BYTE*)v;
            if (BytesEq(e + 2, "None") && BytesEq(e + 8, "ByteProperty")) {
                g_nameBlocks = (BYTE**)&q[k];
                Log("name pool at exe+", (LONG_PTR)((BYTE*)&q[k] - base));
                return true;
            }
        }
    }
    Log("name pool not found");
    return false;
}

static int ObjInternalIndex(void* obj) { int v = -1; RdF(obj, 0xC, &v); return v; }

static void* ObjAt(int i) {
    if (i < 0 || i >= 0x4000000) return nullptr;
    BYTE* chunk; if (!RdF(g_objChunks, (i >> 16) * 8, &chunk) || !chunk) return nullptr;
    void* obj; if (!RdF(chunk, (LONG_PTR)(i & 0xFFFF) * g_itemSize, &obj)) return nullptr;
    return obj;
}

// FChunkedFixedUObjectArray { Objects**, PreAllocated*, Max, Num, MaxChunks, NumChunks }
static bool FindObjectArray() {
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    ExeSection secs[16]; int ns = WritableSections(secs, 16);
    for (int s = 0; s < ns; ++s) {
        BYTE* p = secs[s].p;
        for (size_t k = 0; k + 32 <= secs[s].n; k += 8) {
            int mx = *(int*)(p + k + 16), num = *(int*)(p + k + 20);
            int mxc = *(int*)(p + k + 24), nc = *(int*)(p + k + 28);
            if (num < 4096 || num > mx || mx > 0x4000000) continue;
            if (nc != (num + 0xFFFF) / 0x10000 || mxc != (mx + 0xFFFF) / 0x10000) continue;
            BYTE** chunks = *(BYTE***)(p + k);
            if (!ReadableFast((ULONG_PTR)chunks, 8 * nc)) continue;
            const int sizes[] = { 0x18, 0x10, 0x20 };
            for (int sz : sizes) {
                g_objChunks = chunks; g_objNum = num; g_itemSize = sz;
                const int probe[] = { 0, 1, 2, 3, 50, 500, 3000 };
                bool good = true;
                for (int i : probe) { void* o = ObjAt(i); if (!o || ObjInternalIndex(o) != i) { good = false; break; } }
                if (good) {
                    g_objArrayAddr = p + k;
                    Log("object array at exe+", (LONG_PTR)(p + k - base));
                    Log("  objects:", num); Log("  item size:", sz);
                    return true;
                }
            }
            g_objChunks = nullptr; g_objNum = 0;
        }
    }
    Log("object array not found");
    return false;
}

static UINT32 ObjName(void* obj) { UINT32 n = 0xFFFFFFFF; RdF(obj, 0x18, &n); return n; }

// Collect the FName index of every string we care about by walking the name pool once.
enum {
    N_CoreUObject, N_Engine_Pkg, N_FortniteGame_Pkg,
    N_Object, N_Actor, N_Engine, N_GameViewportClient, N_World, N_GameInstance, N_Player,
    N_PlayerController, N_Controller, N_PlayerCameraManager, N_FortPawn, N_FortWeap_EditingTool, N_FortEngine,
    N_GameViewport, N_OwningGameInstance, N_LocalPlayers, N_PlayerCameraManager_Prop, N_DefaultFOV,
    N_DefaultOrthoWidth, N_LockedFOV, N_Pawn, N_CurrentWeapon,
    N_COUNT
};
static const char* g_nameStr[N_COUNT] = {
    "/Script/CoreUObject", "/Script/Engine", "/Script/FortniteGame",
    "Object", "Actor", "Engine", "GameViewportClient", "World", "GameInstance", "Player",
    "PlayerController", "Controller", "PlayerCameraManager", "FortPawn", "FortWeap_EditingTool", "FortEngine",
    "GameViewport", "OwningGameInstance", "LocalPlayers", "PlayerCameraManager", "DefaultFOV",
    "DefaultOrthoWidth", "LockedFOV", "Pawn", "CurrentWeapon",
};
static UINT32 g_nameIdx[N_COUNT];

static bool ResolveNames() {
    for (int i = 0; i < N_COUNT; ++i) g_nameIdx[i] = 0xFFFFFFFF;
    UINT32 curBlock = 0, cursor = 0;
    if (!RdF((BYTE*)g_nameBlocks, -8, &curBlock) || !RdF((BYTE*)g_nameBlocks, -4, &cursor) || curBlock > 8191) {
        Log("name pool header unreadable"); return false;
    }
    int found = 0;
    for (UINT32 b = 0; b <= curBlock; ++b) {
        BYTE* blk; if (!RdF(g_nameBlocks, b * 8, &blk) || !blk) continue;
        UINT32 size = b == curBlock ? cursor : 0x20000;
        if (!ReadableFast((ULONG_PTR)blk, size)) continue;
        for (UINT32 off = 0; off + 2 <= size;) {
            UINT16 hdr = *(UINT16*)(blk + off);
            int len = hdr >> 6; bool wide = hdr & 1;
            if (len == 0) break;
            UINT32 esz = 2 + (wide ? len * 2 : len);
            if (!wide) {
                const char* str = (const char*)(blk + off + 2);
                for (int i = 0; i < N_COUNT; ++i) {
                    if (g_nameIdx[i] != 0xFFFFFFFF) continue;
                    const char* t = g_nameStr[i]; int j = 0;
                    while (j < len && t[j] && t[j] == str[j]) ++j;
                    if (j == len && !t[j]) {
                        UINT32 idx = (b << 16) | (off >> 1);
                        for (int k = i; k < N_COUNT; ++k)        // same text used twice in the table
                            if (g_nameIdx[k] == 0xFFFFFFFF && !lstrcmpA(g_nameStr[k], g_nameStr[i])) { g_nameIdx[k] = idx; ++found; }
                        break;
                    }
                }
            }
            off += (esz + 1) & ~1u;
        }
    }
    Log("names resolved:", found);
    return g_nameIdx[N_Object] != 0xFFFFFFFF && g_nameIdx[N_PlayerController] != 0xFFFFFFFF;
}

// Walk a class (and its parents) for an FProperty by name -> offset.
// FField: Next @0x20, Name @0x28 | FProperty: ElementSize @0x3C, Offset_Internal @0x4C
// UStruct: ChildProperties @0x50
static LONG_PTR FieldOffset(void* cls, int nameId, int elementSize, const char* label) {
    UINT32 want = g_nameIdx[nameId];
    if (want == 0xFFFFFFFF || !cls) { Log("  missing name:", -1); Log(label); return -1; }
    void* c = cls;
    for (int depth = 0; c && depth < 16; ++depth) {
        void* f; if (!RdF(c, 0x50, &f)) break;
        for (int i = 0; f && i < 4000; ++i) {
            UINT32 nm;
            if (!RdF(f, 0x28, &nm)) break;
            if (nm == want) {
                int es = 0, off = 0;
                if (!RdF(f, 0x3C, &es) || !RdF(f, 0x4C, &off)) return -1;
                if (es != elementSize || off <= 0 || off > 0x10000) { Log("  bad layout:", es); Log(label); return -1; }
                Log(label, off);
                return off;
            }
            if (!RdF(f, 0x20, &f)) break;
        }
        if (!RdF(c, g_superOff, &c)) break;
    }
    Log("  not found:", -1); Log(label);
    return -1;
}

// ---------------------------------------------------------------------
//  StaticFindObject (exact byte-pattern match only - never a guess).
//  Used when the name table can't be read (e.g. 17.30).
// ---------------------------------------------------------------------
static CONTEXT        g_guardCtx;
static volatile LONG  g_guardOn, g_guardHit;
static volatile DWORD g_guardTid;

static LONG CALLBACK GuardVeh(PEXCEPTION_POINTERS e) {
    if (g_guardOn && GetCurrentThreadId() == g_guardTid) {
        DWORD c = e->ExceptionRecord->ExceptionCode;
        if (c == EXCEPTION_ACCESS_VIOLATION || c == EXCEPTION_ILLEGAL_INSTRUCTION ||
            c == EXCEPTION_PRIV_INSTRUCTION || c == EXCEPTION_INT_DIVIDE_BY_ZERO) {
            g_guardOn = 0; g_guardHit = 1;
            *e->ContextRecord = g_guardCtx;
            return EXCEPTION_CONTINUE_EXECUTION;
        }
    }
    return EXCEPTION_CONTINUE_SEARCH;
}

typedef void* (*SFO_t)(void* cls, void* outer, const wchar_t* name, bool exact);
static SFO_t g_sfo;

NOINLINE static void* GuardedFind(SFO_t fn, const wchar_t* name) {
    void* volatile result = nullptr;
    g_guardHit = 0;
    g_guardTid = GetCurrentThreadId();
    RtlCaptureContext(&g_guardCtx);
    if (g_guardHit) return nullptr;
    g_guardOn = 1;
    result = fn(nullptr, nullptr, name, false);
    g_guardOn = 0;
    return result;
}
static void* Find(const wchar_t* path) { return g_sfo ? GuardedFind(g_sfo, path) : nullptr; }

static BYTE* FindPattern(const char* pat) {
    BYTE bytes[96]; bool mask[96]; int n = 0;
    for (const char* c = pat; *c && n < 96;) {
        if (*c == ' ') { ++c; continue; }
        if (*c == '?') { mask[n] = false; bytes[n++] = 0; ++c; if (*c == '?') ++c; continue; }
        auto hx = [](char ch) { return ch >= 'a' ? ch - 'a' + 10 : ch >= 'A' ? ch - 'A' + 10 : ch - '0'; };
        bytes[n] = (BYTE)(hx(c[0]) * 16 + hx(c[1])); mask[n++] = true; c += 2;
    }
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    auto nt = (IMAGE_NT_HEADERS64*)(base + ((IMAGE_DOS_HEADER*)base)->e_lfanew);
    auto sec = IMAGE_FIRST_SECTION(nt);
    for (int s = 0; s < nt->FileHeader.NumberOfSections; ++s) {
        if (!(sec[s].Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        BYTE* t = base + sec[s].VirtualAddress; DWORD len = sec[s].Misc.VirtualSize;
        for (DWORD i = 0; i + n < len; ++i) {
            if (t[i] != bytes[0]) continue;
            int j = 1; while (j < n && (!mask[j] || t[i + j] == bytes[j])) ++j;
            if (j == n) return t + i;
        }
    }
    return nullptr;
}

static bool ValidateSFO(SFO_t fn) {
    void* objCls = GuardedFind(fn, L"/Script/CoreUObject.Object");
    if (!objCls || !Readable(objCls, 0x60)) return false;
    void* actorCls = GuardedFind(fn, L"/Script/Engine.Actor");
    if (!actorCls || actorCls == objCls || !Readable(actorCls, 0x60)) return false;
    const LONG_PTR offs[] = { 0x40, 0x30 };
    for (LONG_PTR off : offs) {
        void* c = actorCls;
        for (int i = 0; i < 16 && c; ++i) {
            if (c == objCls) { g_superOff = off; return true; }
            if (!Rd(c, off, &c)) break;
        }
    }
    return false;
}

static bool LocateSFO() {
    const char* pats[] = {
        "40 55 53 57 41 54 41 55 41 57 48 8D AC 24 ? ? ? ? 48 81 EC ? ? ? ? 48 8B 05 ? ? ? ? 48 33 C4 48 89 85",        // 4.26 (16.x-17.x)
        "48 89 5C 24 ? 48 89 74 24 ? 48 89 7C 24 ? 55 41 54 41 55 41 56 41 57 48 8B EC 48 83 EC 60 45 33 ED 45 8A F9 44 38 2D ? ? ? ? 49 8B F8 48 8B F2 4C 8B E1", // 16.50
        "48 89 5C 24 ? 48 89 74 24 ? 48 89 7C 24 ? 55 41 54 41 55 41 56 41 57 48 8B EC 48 83 EC 60 45 33 ED 45 8A F9 44 38 2D ? ? ? ? 49 8B F8 48 8B", // 18.x
        "4C 8B DC 57 48 81 EC ? ? ? ? 80 3D ? ? ? ? ? 49 89 6B F0 49 89 73 E8",                         // 4.16
        "4C 8B DC 49 89 5B 08 49 89 6B 18 49 89 73 20 57 41 56 41 57 48 83 EC 60 80 3D",                 // 4.19
    };
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    for (const char* p : pats) {
        BYTE* a = FindPattern(p);
        if (a && ValidateSFO((SFO_t)a)) {
            g_sfo = (SFO_t)a;
            Log("StaticFindObject (exact match) at exe+", (LONG_PTR)(a - base));
            return true;
        }
    }
    Log("no exact StaticFindObject match for this build");
    return false;
}

// ---------- camera-scan mode (no names needed) ----------
static bool     g_camScanMode;
static void*    g_pcmClass;
static LONGLONG g_lastPcmScan;
static LONG_PTR g_lockedOffScan = -1;
static bool     g_lockedSearchDone;

static int LiveObjNum() { int n = g_objNum; if (g_objArrayAddr) Rd(g_objArrayAddr, 20, &n); return n; }

// non-cached, fully checked read of object slot i (used every tick)
static void* ObjAtSafe(int i) {
    BYTE* chunk; if (!Rd(g_objChunks, (i >> 16) * 8, &chunk) || !chunk) return nullptr;
    void* obj; if (!Rd(chunk, (LONG_PTR)(i & 0xFFFF) * g_itemSize, &obj)) return nullptr;
    return obj;
}

static void* g_cams[8];
static int   g_camIdx[8];
static int   g_camCount;

// All live (non-default) camera managers. Rescans at most every 2 s, or when one dies.
static void* g_pcClass;
static void* volatile g_pcObj;
static volatile int   g_pcIdx = -1;
static bool PcValid() { void* pc = g_pcObj; return pc && g_pcIdx >= 0 && ObjAtSafe(g_pcIdx) == pc; }

static int FindCameras() {
    bool camsOk = g_camCount > 0;
    for (int i = 0; i < g_camCount && camsOk; ++i) if (ObjAtSafe(g_camIdx[i]) != g_cams[i]) camsOk = false;
    bool pcOk = !g_pcClass || PcValid();
    LONGLONG now = Qpc();
    if (camsOk && pcOk) return g_camCount;
    // cameras gone: rescan soon; only the controller missing: rescan slowly (it may simply not exist yet)
    if (now - g_lastPcmScan < Ms(camsOk ? 6000 : 1500)) return camsOk ? g_camCount : 0;
    g_lastPcmScan = now;
    // build the results on the side and publish them at the end, so the current list stays usable meanwhile
    void* newCams[8]; int newIdx[8]; int newCount = 0;
    void* pc = nullptr; int pcIdx = -1;
    memset(&g_rc, 0, sizeof(g_rc));
    int num = LiveObjNum();
    for (int i = 0; i < num; ++i) {
        void* o = ObjAt(i); if (!o) continue;
        void* c; if (!RdF(o, 0x10, &c)) continue;
        int kind = 0;                            // 1 = camera manager, 2 = player controller
        for (int d = 0; d < 12 && c; ++d) {
            if (c == g_pcmClass) { kind = 1; break; }
            if (g_pcClass && c == g_pcClass) { kind = 2; break; }
            if (!RdF(c, g_superOff, &c)) break;
        }
        if (!kind) continue;
        UINT32 flags = 0; RdF(o, 0x8, &flags);
        if (flags & 0x30) continue;              // class defaults / archetypes
        {   // skip objects the engine is throwing away (old lobby controller etc.)
            BYTE* chunk; int ifl = 0;
            if (RdF(g_objChunks, (i >> 16) * 8, &chunk) && chunk && RdF(chunk, (LONG_PTR)(i & 0xFFFF) * g_itemSize + 8, &ifl) &&
                (ifl & ((1 << 29) | (1 << 28)))) continue;
        }
        if (kind == 1) { if (newCount < 8) { newCams[newCount] = o; newIdx[newCount] = i; ++newCount; } }
        else {
            // prefer the controller that actually has a pawn (yours, in a match)
            void* pawn = nullptr; if (o_Pawn > 0) RdF(o, o_Pawn, &pawn);
            void* curPawn = nullptr; if (pc && o_Pawn > 0) RdF(pc, o_Pawn, &curPawn);
            if (!pc || pawn || !curPawn) { pc = o; pcIdx = i; }
        }
    }
    if (newCount) {
        g_camCount = 0;
        for (int i = 0; i < newCount; ++i) { g_cams[i] = newCams[i]; g_camIdx[i] = newIdx[i]; }
        g_camCount = newCount;
    } else g_camCount = 0;
    if (pc) { g_pcIdx = -1; g_pcObj = pc; g_pcIdx = pcIdx; }
    static int pcLogged;
    if (pcLogged < 3) { ++pcLogged; Log(pc ? "  player controller found" : "  player controller not found yet"); }
    static int scansLogged;
    if (scansLogged < 6) { ++scansLogged; Log("camera scan - objects:", num); Log("  cameras:", g_camCount); }
    return g_camCount;
}

// DefaultFOV, LockedFOV, DefaultOrthoWidth(=512), LockedOrthoWidth, DefaultAspectRatio
static LONG_PTR FindLockedFovSlot(void* pcm) {
    const int span = 0x1000;
    if (!Readable(pcm, span)) return -1;
    const BYTE* b = (const BYTE*)pcm;
    for (int off = 0x100; off + 12 < span; off += 4) {
        float ortho = *(const float*)(b + off);
        if (ortho != 512.0f) continue;
        float dfov = *(const float*)(b + off - 8), locked = *(const float*)(b + off - 4);
        float aspect = *(const float*)(b + off + 8);
        if (dfov >= 60 && dfov <= 130 && (locked == 0 || (locked >= 5 && locked <= 170)) && aspect >= 1.0f && aspect <= 2.5f) {
            Log("camera: DefaultFOV x100", (LONG_PTR)(dfov * 100));
            return off - 4;
        }
        Log("camera: 512 at offset (rejected)", off);
    }
    return -1;
}


// ---------------------------------------------------------------------
//  Potato graphics: runs console commands (cvars) through the engine's
//  KismetSystemLibrary.ExecuteConsoleCommand, on the GAME thread.
// ---------------------------------------------------------------------
typedef void (*PE_t)(void* obj, void* fn, void* parms);
static PE_t  g_pe;
static void* g_kslCDO;
static void* g_execCmdFn;
static volatile bool g_peOK, g_peGaveUp;
static void* g_getCvarF;
static void* g_getCvarI;

static int FindStringRefs(const wchar_t* str, BYTE** out, int max) {
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    auto nt = (IMAGE_NT_HEADERS64*)(base + ((IMAGE_DOS_HEADER*)base)->e_lfanew);
    auto sec = IMAGE_FIRST_SECTION(nt);
    BYTE *tp = nullptr, *rp = nullptr; DWORD tn = 0, rn = 0;
    for (int i = 0; i < nt->FileHeader.NumberOfSections; ++i) {
        const char* nm = (const char*)sec[i].Name;
        if (nm[0] == '.' && nm[1] == 't' && nm[2] == 'e' && nm[3] == 'x' && nm[4] == 't') { tp = base + sec[i].VirtualAddress; tn = sec[i].Misc.VirtualSize; }
        if (nm[0] == '.' && nm[1] == 'r' && nm[2] == 'd' && nm[3] == 'a' && nm[4] == 't' && nm[5] == 'a') { rp = base + sec[i].VirtualAddress; rn = sec[i].Misc.VirtualSize; }
    }
    if (!tp || !rp) return 0;
    int len = wlen(str), found = 0;
    for (DWORD i = 0; i + 7 < tn && found < max; ++i) {
        BYTE* b = tp + i;
        if ((b[0] != 0x48 && b[0] != 0x4C) || b[1] != 0x8D || (b[2] & 0xC7) != 0x05) continue;
        BYTE* target = b + 7 + *(INT32*)(b + 3);
        if (target < rp || target + len * 2 > rp + rn) continue;
        const wchar_t* w = (const wchar_t*)target;
        if (w[0] != str[0]) continue;
        int k = 0; while (k < len && w[k] == str[k]) ++k;
        if (k == len && w[k] == 0) out[found++] = b;
    }
    return found;
}

static bool InVtable(void* obj, void* fn) {
    void** vt; if (!Rd(obj, 0, &vt) || !vt) return false;
    for (int i = 0; i < 0x120; ++i) { void* e; if (!Rd(vt, i * 8, &e)) return false; if (e == fn) { Log("ProcessEvent vtable index:", i); return true; } }
    return false;
}

static bool InitPotato() {
    if (g_peOK || g_peGaveUp) return g_peOK;
    if (!g_sfo) return false;
    void* objCDO = Find(L"/Script/CoreUObject.Default__Object");
    g_kslCDO     = Find(L"/Script/Engine.Default__KismetSystemLibrary");
    g_execCmdFn  = Find(L"/Script/Engine.KismetSystemLibrary.ExecuteConsoleCommand");
    if (!objCDO || !g_kslCDO || !g_execCmdFn) { Log("potato: engine objects not found"); g_peGaveUp = true; return false; }
    // UObject::ProcessEvent: 2nd call after this string's reference (checked against the vtable)
    BYTE* refs[2];
    if (FindStringRefs(L"UMeshNetworkComponent::ProcessEvent: Invalid mesh network node type: %s", refs, 2) > 0) {
        int calls = 0;
        for (int i = 0; i < 2000; ++i) {
            BYTE* b = refs[0] + i;
            if (b[0] != 0xE8) continue;
            if (++calls < 2) continue;
            BYTE* target = b + 5 + *(INT32*)(b + 1);
            if (InVtable(objCDO, target)) { g_pe = (PE_t)target; break; }
            break;
        }
    }
    if (!g_pe) { Log("potato: ProcessEvent not confirmed - disabled"); g_peGaveUp = true; return false; }
    g_getCvarF = Find(L"/Script/Engine.KismetSystemLibrary.GetConsoleVariableFloatValue");
    g_getCvarI = Find(L"/Script/Engine.KismetSystemLibrary.GetConsoleVariableIntValue");
    if (!g_getCvarF || !g_getCvarI) { Log("potato: can't read settings on this build - disabled"); g_peGaveUp = true; return false; }
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    Log("ProcessEvent at exe+", (LONG_PTR)((BYTE*)g_pe - base));
    g_peOK = true;
    return true;
}

struct FStr { const wchar_t* data; int num, max; };
static void* g_potatoWorld;
static void* PotatoWorld() {
    if (g_camCount <= 0) return nullptr;
    void* c = g_cams[0]; int idx = g_camIdx[0];
    return ObjAtSafe(idx) == c ? c : nullptr;
}
static void ConsoleCmd(const wchar_t* cmd) {
    struct { void* world; FStr command; void* player; } parms;
    int n = wlen(cmd) + 1;
    parms.world = g_potatoWorld; parms.command = { cmd, n, n }; parms.player = nullptr;
    g_pe(g_kslCDO, g_execCmdFn, &parms);
}

static void FmtFloat(wchar_t* out, float v) {           // up to 3 decimals
    int k = 0;
    if (v < 0) { out[k++] = L'-'; v = -v; }
    int whole = (int)v, frac = (int)((v - whole) * 1000 + 0.5f);
    if (frac >= 1000) { whole++; frac -= 1000; }
    itow(whole, out + k); k = wlen(out);
    out[k++] = L'.';
    out[k++] = (wchar_t)(L'0' + frac / 100); out[k++] = (wchar_t)(L'0' + frac / 10 % 10); out[k++] = (wchar_t)(L'0' + frac % 10);
    out[k] = 0;
}
static void CmdSet(const wchar_t* name, float v, bool isInt) {
    wchar_t buf[128]; wcopy(buf, name, 96); int k = wlen(buf); buf[k++] = L' ';
    if (isInt) itow((int)(v < 0 ? v - 0.5f : v + 0.5f), buf + k); else FmtFloat(buf + k, v);
    ConsoleCmd(buf);
}

// Reads a console variable's current value (KismetSystemLibrary.GetConsoleVariable*Value).
static bool ReadCvar(const wchar_t* name, bool isInt, float* out) {
    void* fn = isInt ? g_getCvarI : g_getCvarF;
    if (!fn) return false;
    struct { FStr name; union { float f; int i; } ret; int pad; } parms;
    int n = wlen(name) + 1;
    parms.name = { name, n, n }; parms.ret.i = 0x7FC00000; parms.pad = 0;
    g_pe(g_kslCDO, fn, &parms);
    *out = isInt ? (float)parms.ret.i : parms.ret.f;
    return !(!isInt && parms.ret.i == 0x7FC00000);
}

// Every setting potato touches. Your original values are captured before the first change
// and put back exactly when potato goes to Off.
struct PotatoVar { const wchar_t* name; bool isInt; float orig; bool have; bool keep; };
// keep = always held at YOUR value while potato is on (colour, exposure, resolution never change)
static PotatoVar g_pv[] = {
    { L"sg.PostProcessQuality", true, 0.f, false, false }, { L"sg.ShadowQuality", true, 0.f, false, false },
    { L"sg.FoliageQuality", true, 0.f, false, false },     { L"sg.EffectsQuality", true, 0.f, false, false },
    { L"sg.TextureQuality", true, 0.f, false, false },     { L"sg.ViewDistanceQuality", true, 0.f, false, false },
    { L"r.MotionBlurQuality", true, 0.f, false, false },   { L"r.MotionBlurAmount", false, 0.f, false, false },
    { L"r.RayTracing.ForceAllRayTracingEffects", true, 0.f, false, false },
    { L"r.SSR.Quality", true, 0.f, false, false },         { L"r.AmbientOcclusionLevels", true, 0.f, false, false },
    { L"r.DepthOfFieldQuality", true, 0.f, false, false }, { L"r.LensFlareQuality", true, 0.f, false, false },
    { L"r.SceneColorFringeQuality", true, 0.f, false, false }, { L"r.BloomQuality", true, 0.f, false, false },
    { L"r.ShadowQuality", true, 0.f, false, false },       { L"r.ContactShadows", true, 0.f, false, false },
    { L"r.LightFunctionQuality", true, 0.f, false, false },{ L"r.VolumetricFog", true, 0.f, false, false },
    { L"r.DetailMode", true, 0.f, false, false },          { L"r.MaterialQualityLevel", true, 0.f, false, false },
    { L"r.SkeletalMeshLODBias", true, 0.f, false, false }, { L"r.StaticMeshLODDistanceScale", false, 0.f, false, false },
    { L"r.ViewDistanceScale", false, 0.f, false, false },  { L"r.MipMapLODBias", false, 0.f, false, false },
    { L"r.OneFrameThreadLag", true, 0.f, false, false },   { L"r.GTSyncType", true, 0.f, false, false },
    // no render limit (full detail at any distance):
    { L"r.LightShaftQuality", true, 0.f, false, false },
    { L"r.ForceLOD", true, 0.f, false, false },            { L"foliage.LODDistanceScale", false, 0.f, false, false },
    { L"r.LandscapeLODDistributionScale", false, 0.f, false, false }, { L"r.LandscapeLOD0DistributionScale", false, 0.f, false, false },
    { L"r.MaxAnisotropy", true, 0.f, false, false },       { L"r.Streaming.Boost", false, 0.f, false, false },
    // held at your values:
    { L"r.Tonemapper.Quality", true, 0.f, false, true },   { L"r.EyeAdaptationQuality", true, 0.f, false, true },
    { L"r.ScreenPercentage", false, 0.f, false, true },    { L"r.Color.Mid", false, 0.f, false, true },
};
static const int PV_COUNT = sizeof(g_pv) / sizeof(g_pv[0]);
static bool g_pvCaptured;

static void CapturePotatoBaseline() {
    int got = 0;
    for (int i = 0; i < PV_COUNT; ++i) {
        g_pv[i].have = ReadCvar(g_pv[i].name, g_pv[i].isInt, &g_pv[i].orig);
        if (g_pv[i].have) ++got;
    }
    g_pvCaptured = true;
    Log("potato: saved your current settings:", got);
}

// Potato levels (1 = Default, nothing changed). Colour, exposure and resolution are never touched.
static const wchar_t* POTATO_NAME[11] = { L"", L"Default", L"Light", L"Low", L"Performance", L"Basic Potato",
                                          L"Potato", L"Deep Potato", L"Ultra Potato", L"Extreme", L"Max Potato" };
// What each setting should be at level L (2..10). Returns false = leave at your original.
// Every level makes a visible difference; colour, brightness and resolution are never touched.
static bool PotatoValue(const wchar_t* n, int L, float orig, float* v) {
    auto is = [&](const wchar_t* x) { return weq(n, x); };
    static const float VIEW[11] = { 1, 1, 1,   0.92f, 0.85f, 0.75f, 0.68f, 0.6f, 0.55f, 0.5f, 0.45f };
    static const float SMLOD[11]= { 1, 1, 1,   1.f,   1.25f, 1.6f,  2.2f,  2.8f, 3.4f,  4.0f, 4.6f };
    static const float MIP[11]  = { 0, 0, 0,   0,     0.f,   0.5f,  1.2f,  1.9f, 2.6f,  3.3f, 4.0f };
    // 2 Light: glow, ambient occlusion, reflections and extras off
    if (is(L"r.MotionBlurQuality") || is(L"r.MotionBlurAmount") || is(L"r.RayTracing.ForceAllRayTracingEffects") ||
        is(L"r.DepthOfFieldQuality") || is(L"r.LensFlareQuality") || is(L"r.SceneColorFringeQuality") ||
        is(L"r.BloomQuality") || is(L"r.AmbientOcclusionLevels") || is(L"r.SSR.Quality") ||
        is(L"r.ContactShadows") || is(L"r.LightShaftQuality"))   { *v = 0; return L >= 2; }
    // 3 Low: shadows off, low post-processing, low foliage, medium-low textures
    if (is(L"sg.ShadowQuality") || is(L"r.ShadowQuality") || is(L"sg.PostProcessQuality") || is(L"sg.FoliageQuality"))
                                          { *v = 0; return L >= 3; }
    if (is(L"r.LightFunctionQuality"))    { *v = 0; return L >= 3; }
    if (is(L"sg.TextureQuality"))         { *v = L >= 4 ? 0.f : 1.f; return L >= 3 && (L >= 4 || orig > 1); }
    if (is(L"sg.EffectsQuality"))         { *v = L >= 4 ? 0.f : 1.f; return L >= 3 && (L >= 4 || orig > 1); }
    // 4 Performance: lowest textures & effects, no volumetric fog, less detail
    if (is(L"r.VolumetricFog"))           { *v = 0; return L >= 4; }
    if (is(L"r.DetailMode"))              { *v = L >= 5 ? 0.f : 1.f; return L >= 4 && (L >= 5 || orig > 1); }
    // view distance and mesh detail shrink every level from 3 up
    if (is(L"r.ViewDistanceScale"))       { *v = orig * VIEW[L]; return L >= 3; }
    if (is(L"r.StaticMeshLODDistanceScale")) { *v = SMLOD[L]; return L >= 4; }
    // 5 Basic Potato: low view-distance group, textures start to blur
    if (is(L"sg.ViewDistanceQuality"))    { *v = 0; return L >= 5; }
    if (is(L"r.MipMapLODBias"))           { *v = MIP[L]; return L >= 5; }
    // 6 Potato: simple materials, lower-detail characters
    if (is(L"r.MaterialQualityLevel"))    { *v = 0; return L >= 6; }
    if (is(L"r.SkeletalMeshLODBias"))     { *v = L >= 8 ? 2.f : 1.f; return L >= 6; }
    return false;
}

static float g_pvApplied[64];
static bool  g_pvAppliedValid[64];

// Final value for each setting from all features together. false = your original value.
static bool FeatureValue(const wchar_t* n, float orig, float* v) {
    bool set = false;
    if (g_lowLat) {
        if (weq(n, L"r.OneFrameThreadLag")) { *v = 0; set = true; }   // no extra frame between game & render
        if (weq(n, L"r.GTSyncType"))        { *v = 1; set = true; }   // sync game thread with the GPU submit
    }
    if (g_noRender) {                                 // everything at full quality, however far away
        if (weq(n, L"r.ViewDistanceScale"))                { *v = 10.f; set = true; }
        if (weq(n, L"r.ForceLOD"))                         { *v = 0;    set = true; }   // highest-detail models everywhere
        if (weq(n, L"r.StaticMeshLODDistanceScale"))       { *v = 0.1f; set = true; }
        if (weq(n, L"r.SkeletalMeshLODBias"))              { *v = -2;   set = true; }
        if (weq(n, L"foliage.LODDistanceScale"))           { *v = 8.f;  set = true; }
        if (weq(n, L"r.LandscapeLODDistributionScale"))    { *v = 3.f;  set = true; }
        if (weq(n, L"r.LandscapeLOD0DistributionScale"))   { *v = 3.f;  set = true; }
        if (weq(n, L"r.MaxAnisotropy"))                    { *v = 16;   set = true; }   // sharp textures at a distance
        if (weq(n, L"r.Streaming.Boost"))                  { *v = 2.f;  set = true; }
        if (weq(n, L"r.MipMapLODBias"))                    { *v = 0.f;  set = true; }
    }
    if (g_potato > 1 && PotatoValue(n, g_potato, orig, v)) set = true;   // potato wins where both apply
    return set;
}

// Stretched res: original resolution / window mode from your Fortnite settings.
static int  g_origResX = 1920, g_origResY = 1080, g_origMode = 1;
static int  g_stretchApplied = -1;           // -1 = never touched, else STRETCH_W index, 99 = restored
static void LoadUserResolution() {
    wchar_t ini[MAX_PATH];
    DWORD n = GetEnvironmentVariableW(L"LOCALAPPDATA", ini, MAX_PATH);
    if (!n || n > MAX_PATH - 80) return;
    wcopy(ini + n, L"\\FortniteGame\\Saved\\Config\\WindowsClient\\GameUserSettings.ini", MAX_PATH - n);
    const wchar_t* S = L"/Script/FortniteGame.FortGameUserSettings";
    g_origResX = GetPrivateProfileIntW(S, L"ResolutionSizeX", 1920, ini);
    g_origResY = GetPrivateProfileIntW(S, L"ResolutionSizeY", 1080, ini);
    g_origMode = GetPrivateProfileIntW(S, L"LastConfirmedFullscreenMode", 1, ini);
    if (g_origResX < 640 || g_origResY < 480) { g_origResX = 1920; g_origResY = 1080; }
}
static void SetRes(int w, int h, int mode) {     // mode: 0 fullscreen, 1 windowed fullscreen, 2 windowed
    wchar_t buf[64]; wcopy(buf, L"r.SetRes ", 64);
    int k = wlen(buf); itow(w, buf + k); k = wlen(buf); buf[k++] = L'x'; itow(h, buf + k); k = wlen(buf);
    if (mode == 0) buf[k++] = L'f'; else if (mode == 1) { buf[k++] = L'w'; buf[k++] = L'f'; } else buf[k++] = L'w';
    buf[k] = 0;
    ConsoleCmd(buf);
}

// Game thread only.
static void ApplyGraphics() {
    g_potatoWorld = PotatoWorld();
    if (!g_potatoWorld) return;
    g_gfxDirty = 0;
    bool anyActive = g_potato > 1 || g_lowLat || g_noRender;
    bool forceAll = g_potato <= 1 && g_pvCaptured;   // potato back to Default: re-send every value, no shortcuts
    if (!g_pvCaptured) {
        if (anyActive) CapturePotatoBaseline();
    }
    if (g_pvCaptured) {
        // scalability groups first (they set many things at once), then the individual settings
        bool groupsChanged = false;
        for (int pass = 0; pass < 2; ++pass)
            for (int i = 0; i < PV_COUNT && i < 64; ++i) {
                PotatoVar& p = g_pv[i];
                bool isGroup = p.name[0] == L's' && p.name[1] == L'g' && p.name[2] == L'.';
                if ((pass == 0) != isGroup || !p.have) continue;
                float v = p.orig;
                FeatureValue(p.name, p.orig, &v);
                if (p.keep) {          // quality groups can change these underneath us: pin them to your value
                    if (anyActive || (g_pvAppliedValid[i] && g_pvApplied[i] != p.orig) || groupsChanged) {
                        CmdSet(p.name, p.orig, p.isInt); g_pvApplied[i] = p.orig; g_pvAppliedValid[i] = true;
                    }
                    continue;
                }
                if (!forceAll && g_pvAppliedValid[i] && g_pvApplied[i] == v) continue;   // already like that
                if (!forceAll && !g_pvAppliedValid[i] && v == p.orig) { g_pvApplied[i] = v; g_pvAppliedValid[i] = true; continue; }
                CmdSet(p.name, v, p.isInt);
                if (isGroup) groupsChanged = true;
                g_pvApplied[i] = v; g_pvAppliedValid[i] = true;
            }
    }
    // stretched resolution: the monitor is already switched (UI thread); size the game to it,
    // always windowed fullscreen so alt-tab and the menu keep working.
    int want = g_dispApplied >= 0 ? g_dispApplied : 99;
    if (want != g_stretchApplied && !(want == 99 && g_stretchApplied < 0)) {
        if (want == 99) SetRes(g_origResX, g_origResY, g_origMode == 0 ? 1 : g_origMode);
        else SetRes(STRETCH_W[want], 1080, 1);
        g_stretchApplied = want;
        Log("game resolution:", want == 99 ? g_origResX : STRETCH_W[want]);
    }
    Log("graphics applied, potato level:", g_potato);
    float chk;
    if (ReadCvar(L"sg.ShadowQuality", true, &chk)) Log("  check: shadow quality is now", (LONG_PTR)chk);
    if (ReadCvar(L"r.ViewDistanceScale", false, &chk)) Log("  check: view distance x100 is now", (LONG_PTR)(chk * 100));
}

// Camera POV caches (FMinimalViewInfo: FOV, DesiredFOV, OrthoWidth=512, Near, Far, AspectRatio).
// They hold the game's own FOV (zoom included) even while LockedFOV overrides it.
static int   g_povCount;
static LONG_PTR g_povOff[8];
static float g_povHip[8];
static void FindPovSlots(void* pcm, LONG_PTR skipOff) {
    const int span = 0x3000;
    g_povCount = 0;
    if (!Readable(pcm, span)) return;
    const BYTE* b = (const BYTE*)pcm;
    for (int off = 0x100; off + 0x18 < span && g_povCount < 8; off += 4) {
        if (*(const float*)(b + off + 8) != 512.0f || off == skipOff) continue;
        float fov = *(const float*)(b + off), desired = *(const float*)(b + off + 4), aspect = *(const float*)(b + off + 0x14);
        if (fov >= 5 && fov <= 170 && desired >= 0 && desired <= 170 && aspect >= 0.5f && aspect <= 4.f) {
            g_povOff[g_povCount] = off; g_povHip[g_povCount] = 0; ++g_povCount;
        }
    }
    Log("camera view caches found:", g_povCount);
}

// Finds a replicated property's offset by the OnRep function it notifies (FProperty::RepNotifyFunc),
// so no name table is needed. FField: Next @0x20 | FProperty: ElementSize @0x3C, Offset @0x4C, RepNotify @0x50
static LONG_PTR OffsetByRepNotify(void* cls, void* onRepFn, int elementSize) {
    if (!cls || !onRepFn) return -1;
    UINT32 want; if (!Rd(onRepFn, 0x18, &want)) return -1;
    void* c = cls;
    for (int depth = 0; c && depth < 16; ++depth) {
        void* f; if (!Rd(c, 0x50, &f)) break;
        for (int i = 0; f && i < 4000; ++i) {
            UINT32 rep = 0; int es = 0, off = 0;
            if (Rd(f, 0x50, &rep) && rep == want && Rd(f, 0x3C, &es) && es == elementSize && Rd(f, 0x4C, &off) && off > 0 && off < 0x10000)
                return off;
            if (!Rd(f, 0x20, &f)) break;
        }
        if (!Rd(c, g_superOff, &c)) break;
    }
    return -1;
}

static bool InitBySFO() {
    if (!g_sfo && !LocateSFO()) { g_reflGaveUp = true; return false; }
    g_pcmClass = Find(L"/Script/Engine.PlayerCameraManager");
    if (!g_pcmClass) { Log("PlayerCameraManager class not found yet"); return false; }
    int idx = ObjInternalIndex(g_pcmClass);
    if (ObjAtSafe(idx) != g_pcmClass) { Log("object array mismatch"); g_reflGaveUp = true; return false; }
    g_camScanMode = true;
    g_fovOK = true;
    // Real edit state: local controller -> Pawn -> CurrentWeapon is the editing tool?
    g_pcClass = Find(L"/Script/Engine.PlayerController");
    o_Pawn = OffsetByRepNotify(Find(L"/Script/Engine.Controller"), Find(L"/Script/Engine.Controller.OnRep_Pawn"), 8);
    o_CurrentWeapon = OffsetByRepNotify(Find(L"/Script/FortniteGame.FortPawn"), Find(L"/Script/FortniteGame.FortPawn.OnRep_CurrentWeapon"), 8);
    g_editToolClass = Find(L"/Script/FortniteGame.FortWeap_EditingTool");
    Log("edit state - Controller.Pawn offset:", o_Pawn);
    Log("edit state - FortPawn.CurrentWeapon offset:", o_CurrentWeapon);
    Log(g_pcClass && g_editToolClass && o_Pawn > 0 && o_CurrentWeapon > 0 ? "edit state: reading it from the game"
                                                                          : "edit state: using key tracking");
    if (!(g_pcClass && g_editToolClass && o_Pawn > 0 && o_CurrentWeapon > 0)) { o_Pawn = o_CurrentWeapon = -1; g_pcClass = nullptr; }
    g_reflOK = true;
    Log("FOV via camera scan ready");
    InitPotato();
    return true;
}

static bool InitReflection() {
    if (!g_objChunks && !FindObjectArray()) return false;
    static int named = 0;        // 0 = untried, 1 = names readable, 2 = not readable
    if (!named) named = (FindNamePool() && ResolveNames()) ? 1 : 2;
    if (named == 2) return InitBySFO();

    // One pass over all objects: find the classes (by name + package) and the engine instance.
    enum { C_Object, C_Actor, C_Engine, C_GVC, C_World, C_GameInstance, C_Player, C_PlayerController,
           C_Controller, C_PCM, C_FortPawn, C_EditTool, C_FortEngine, C_COUNT };
    struct Want { int name, pkg; } wants[C_COUNT] = {
        { N_Object, N_CoreUObject }, { N_Actor, N_Engine_Pkg }, { N_Engine, N_Engine_Pkg },
        { N_GameViewportClient, N_Engine_Pkg }, { N_World, N_Engine_Pkg }, { N_GameInstance, N_Engine_Pkg },
        { N_Player, N_Engine_Pkg }, { N_PlayerController, N_Engine_Pkg }, { N_Controller, N_Engine_Pkg },
        { N_PlayerCameraManager, N_Engine_Pkg }, { N_FortPawn, N_FortniteGame_Pkg },
        { N_FortWeap_EditingTool, N_FortniteGame_Pkg }, { N_FortEngine, N_FortniteGame_Pkg } };
    void* cls[C_COUNT] = {};
    int num = g_objNum;
    for (int i = 0; i < num; ++i) {
        void* o = ObjAt(i); if (!o) continue;
        UINT32 nm = ObjName(o);
        for (int w = 0; w < C_COUNT; ++w) {
            if (cls[w] || nm != g_nameIdx[wants[w].name]) continue;
            void* outer; if (!RdF(o, 0x20, &outer) || !outer) continue;
            if (ObjName(outer) == g_nameIdx[wants[w].pkg]) cls[w] = o;
        }
    }
    if (!cls[C_Object] || !cls[C_Actor] || !cls[C_Engine]) { Log("core classes not found"); return false; }

    // SuperStruct offset: Actor -> ... -> Object
    g_superOff = 0;
    const LONG_PTR offs[] = { 0x40, 0x30 };
    for (LONG_PTR off : offs) {
        void* c = cls[C_Actor];
        for (int i = 0; i < 16 && c; ++i) {
            if (c == cls[C_Object]) { g_superOff = off; break; }
            if (!RdF(c, off, &c)) break;
        }
        if (g_superOff) break;
    }
    Log("SuperStruct offset:", g_superOff);
    if (g_superOff != 0x40) { Log("engine layout not supported"); g_reflGaveUp = true; return false; }

    // Engine instance: the live (non-default) object whose class derives from UEngine.
    for (int i = 0; i < num && !g_engine; ++i) {
        void* o = ObjAt(i); if (!o) continue;
        UINT32 flags = 0; if (!RdF(o, 0x8, &flags) || (flags & 0x10)) continue;   // skip RF_ClassDefaultObject
        void* c; if (!RdF(o, 0x10, &c) || !c) continue;
        for (int d = 0; d < 12 && c; ++d) {
            if (c == cls[C_Engine]) { g_engine = o; break; }
            if (!RdF(c, g_superOff, &c)) break;
        }
    }
    if (!g_engine) { static bool once; if (!once) { Log("engine instance not found yet"); once = true; } return false; }
    Log("engine found, object index:", ObjInternalIndex(g_engine));

    Log("looking up fields:");
    o_GameViewport     = FieldOffset(cls[C_Engine],           N_GameViewport,      8,  "  Engine.GameViewport");
    o_World            = FieldOffset(cls[C_GVC],              N_World,             8,  "  GameViewportClient.World");
    o_GameInstance     = FieldOffset(cls[C_World],            N_OwningGameInstance,8,  "  World.OwningGameInstance");
    o_LocalPlayers     = FieldOffset(cls[C_GameInstance],     N_LocalPlayers,      16, "  GameInstance.LocalPlayers");
    o_PlayerController = FieldOffset(cls[C_Player],           N_PlayerController,  8,  "  Player.PlayerController");
    if (o_GameViewport < 0 || o_World < 0 || o_GameInstance < 0 || o_LocalPlayers < 0 || o_PlayerController < 0) {
        Log("player chain incomplete"); g_reflGaveUp = true; return false;
    }

    o_CameraManager = FieldOffset(cls[C_PlayerController], N_PlayerCameraManager_Prop, 8, "  PlayerController.PlayerCameraManager");
    if (g_nameIdx[N_LockedFOV] != 0xFFFFFFFF)
        o_LockedFOV = FieldOffset(cls[C_PCM], N_LockedFOV, 4, "  PlayerCameraManager.LockedFOV");
    if (o_LockedFOV < 0) {
        // Normally not reflected: it sits right after DefaultFOV (before DefaultOrthoWidth).
        LONG_PTR dfov  = FieldOffset(cls[C_PCM], N_DefaultFOV, 4, "  PlayerCameraManager.DefaultFOV");
        LONG_PTR ortho = FieldOffset(cls[C_PCM], N_DefaultOrthoWidth, 4, "  PlayerCameraManager.DefaultOrthoWidth");
        if (dfov > 0 && ortho >= dfov + 8) o_LockedFOV = dfov + 4;
    }
    g_fovOK = o_CameraManager >= 0 && o_LockedFOV > 0;
    Log(g_fovOK ? "FOV ready, LockedFOV offset:" : "FOV unavailable", g_fovOK ? o_LockedFOV : -1);

    o_Pawn          = FieldOffset(cls[C_Controller], N_Pawn, 8, "  Controller.Pawn");
    o_CurrentWeapon = FieldOffset(cls[C_FortPawn], N_CurrentWeapon, 8, "  FortPawn.CurrentWeapon");
    g_editToolClass = cls[C_EditTool];
    Log(g_editToolClass && o_Pawn >= 0 && o_CurrentWeapon >= 0 ? "edit-state detection ready"
                                                               : "edit-state detection unavailable (using key tracking)");
    g_reflOK = true;
    Log("engine lookups done");
    return true;
}

static void* LocalPC() {
    if (!g_reflOK) return nullptr;
    if (g_camScanMode) return PcValid() ? g_pcObj : nullptr;
    void *gvc, *world, *gi, *data, *lp, *pc; int num = 0;
    if (!Rd(g_engine, o_GameViewport, &gvc) || !gvc) return nullptr;
    if (!Rd(gvc, o_World, &world) || !world) return nullptr;
    if (!Rd(world, o_GameInstance, &gi) || !gi) return nullptr;
    if (!Rd(gi, o_LocalPlayers, &data) || !Rd(gi, o_LocalPlayers + 8, &num) || num < 1 || !data) return nullptr;
    if (!Rd(data, 0, &lp) || !lp) return nullptr;
    if (!Rd(lp, o_PlayerController, &pc)) return nullptr;
    return pc;
}

static bool IsA(void* obj, void* cls) {
    void* c;
    if (!Rd(obj, 0x10, &c)) return false;
    for (int i = 0; i < 32 && c; ++i) {
        if (c == cls) return true;
        if (!Rd(c, g_superOff, &c)) return false;
    }
    return false;
}

// 1 = holding the edit tool, 0 = not, -1 = unknown (engine lookups unavailable)
static void* g_fortPcClass;
static const LONG_PTR O_PC_EDITACTOR = 0x16F8;   // AFortPlayerController::EditBuildingActor (17.30 SDK)
static volatile bool g_editSeen;          // detection has seen you editing at least once (so it works)
static int ReadEditing() {
    if (!g_reflOK || o_Pawn < 0 || o_CurrentWeapon < 0 || !g_editToolClass) return -1;
    void* pc = LocalPC(); if (!pc) return -1;
    // 1) the controller's edit target (set the moment edit mode opens, cleared when it closes)
    if (!g_fortPcClass) g_fortPcClass = Find(L"/Script/FortniteGame.FortPlayerController");
    if (g_fortPcClass && IsA(pc, g_fortPcClass)) {
        void* eba = nullptr;
        if (Rd(pc, O_PC_EDITACTOR, &eba) && eba) {
            if (!g_editSeen) { g_editSeen = true; Log("edit state: seen editing (edit target)"); }
            return 1;
        }
    }
    // 2) holding the editing tool
    void* pawn; if (!Rd(pc, o_Pawn, &pawn)) return -1;
    if (!pawn) return 0;
    void* weapon; if (!Rd(pawn, o_CurrentWeapon, &weapon)) return -1;
    if (!weapon) return 0;
    if (IsA(weapon, g_editToolClass)) {
        if (!g_editSeen) { g_editSeen = true; Log("edit state: seen editing (edit tool)"); }
        return 1;
    }
    return 0;
}

// ---------------------------------------------------------------------
//  Build looks: bubble wrap builds + custom build colours (your team's builds only, visual only,
//  nothing is sent to the server). Builds are found on a background thread; the material changes
//  run on the game thread through ProcessEvent, a few builds per frame.
// ---------------------------------------------------------------------
struct FNm { INT32 idx, num; };
static void *g_bsmClass, *g_matIfClass, *g_primClass;
static void *g_fnSetMat, *g_fnGetMat, *g_fnNumMat, *g_fnSetVecOnMats, *g_fnStrToName, *g_fnNameToStr, *g_fnPathName, *g_kstrCDO;
static volatile bool g_bvOK, g_bvGaveUp;
static LONG_PTR o_PlayerState = -1, o_PSTeam = -1;
static LONG_PTR o_MatParent = -1;                 // UMaterialInstance::Parent (found at runtime)
// ABuildingActor / ABuildingSMActor layout for this build (Dumper-7 SDK, 17.30)
static const LONG_PTR O_BA_TEAM = 0x44D, O_BSM_SMC = 0x850, O_BSM_UNDERCON = 0x791,
                      O_BSM_ANIMMAPS = 0xA20, O_BSM_EDITING = 0xA90;

static bool BuildLooksInit() {
    if (g_bvOK || g_bvGaveUp) return g_bvOK;
    if (!g_peOK) return false;
    g_bsmClass       = Find(L"/Script/FortniteGame.BuildingSMActor");
    g_matIfClass     = Find(L"/Script/Engine.MaterialInterface");
    g_primClass      = Find(L"/Script/Engine.PrimitiveComponent");
    g_fnSetMat       = Find(L"/Script/Engine.PrimitiveComponent.SetMaterial");
    g_fnGetMat       = Find(L"/Script/Engine.PrimitiveComponent.GetMaterial");
    g_fnNumMat       = Find(L"/Script/Engine.PrimitiveComponent.GetNumMaterials");
    g_fnSetVecOnMats = Find(L"/Script/Engine.MeshComponent.SetVectorParameterValueOnMaterials");
    g_kstrCDO        = Find(L"/Script/Engine.Default__KismetStringLibrary");
    g_fnStrToName    = Find(L"/Script/Engine.KismetStringLibrary.Conv_StringToName");
    g_fnNameToStr    = Find(L"/Script/Engine.KismetStringLibrary.Conv_NameToString");
    g_fnPathName     = Find(L"/Script/Engine.KismetSystemLibrary.GetPathName");
    o_PlayerState = OffsetByRepNotify(Find(L"/Script/Engine.Controller"), Find(L"/Script/Engine.Controller.OnRep_PlayerState"), 8);
    o_PSTeam      = OffsetByRepNotify(Find(L"/Script/FortniteGame.FortPlayerStateAthena"),
                                      Find(L"/Script/FortniteGame.FortPlayerStateAthena.OnRep_TeamIndex"), 1);
    if (o_PSTeam < 0) o_PSTeam = 0xED0;
    Log("builds - PlayerState offset:", o_PlayerState);
    Log("builds - team offset:", o_PSTeam);
    if (!g_bsmClass || !g_matIfClass || !g_primClass || !g_fnSetMat || !g_fnGetMat || !g_fnNumMat ||
        !g_fnSetVecOnMats || !g_kstrCDO || !g_fnStrToName || o_PlayerState < 0) {
        Log("builds: engine functions not found - build looks disabled");
        g_bvGaveUp = true; RequestRedraw(); return false;
    }
    g_bvOK = true;
    Log("builds: ready");
    return true;
}

static int MyTeam() {
    void* pc = LocalPC(); if (!pc) return -1;
    void* ps; if (!Rd(pc, o_PlayerState, &ps) || !ps) return -1;
    BYTE t; if (!Rd(ps, o_PSTeam, &t)) return -1;
    return t;
}

// FUObjectItem flags: PendingKill (1<<29) / Unreachable (1<<28)
static bool AliveAt(void* obj, int idx) {
    if (!obj || idx < 0) return false;
    BYTE* chunk; if (!Rd(g_objChunks, (idx >> 16) * 8, &chunk) || !chunk) return false;
    BYTE* item = chunk + (LONG_PTR)(idx & 0xFFFF) * g_itemSize;
    void* o; int fl; if (!Rd(item, 0, &o) || o != obj || !Rd(item, 8, &fl)) return false;
    return !(fl & ((1 << 29) | (1 << 28)));
}
static bool Alive(void* obj) { return obj && AliveAt(obj, ObjInternalIndex(obj)); }

// ---- background scan: your team's player builds ----
static const int BV_MAX = 6000;
static void* g_bvList[2][BV_MAX];
static int   g_bvIdx[2][BV_MAX];
static volatile int  g_bvCount[2];
static volatile LONG g_bvPub = -1;           // which buffer is published
static volatile int  g_bvTeam = -1;

static DWORD WINAPI BuildScanThread(LPVOID) {
    static RegionCache rc;
    struct CV { void* c; signed char v; };
    static CV cache[16384];
    int buf = 0;
    for (;;) {
        Sleep(250);
        bool want = g_bubble || g_customBuild;
        static bool wasWanted;
        if (!want && !wasWanted) continue;
        wasWanted = want;
        if (!g_reflOK || !g_peOK) continue;
        if (!g_bvOK) { if (g_bvGaveUp || !BuildLooksInit()) continue; }
        int team = MyTeam();
        g_bvTeam = team;
        for (int i = 0; i < 64; ++i) rc.end[i] = 0;       // fresh region map each pass
        int n = LiveObjNum(), cnt = 0;
        int nBsm = 0, nPlaced = 0, nPlacedCnt = 0;
        static void* placedList[BV_MAX]; static int placedIdx[BV_MAX];
        int teamHist[256] = {};
        for (int i = 0; i < n && cnt < BV_MAX; ++i) {
            BYTE* chunk; ULONG_PTR ca = (ULONG_PTR)g_objChunks + (ULONG_PTR)(i >> 16) * 8;
            if (!ReadableFastC(rc, ca, 8) || !(chunk = *(BYTE**)ca)) { i |= 0xFFFF; continue; }
            ULONG_PTR ia = (ULONG_PTR)chunk + (ULONG_PTR)(i & 0xFFFF) * g_itemSize;
            if (!ReadableFastC(rc, ia, 16)) continue;
            void* o = *(void**)ia; int fl = *(int*)(ia + 8);
            if (!o || (fl & ((1 << 29) | (1 << 28)))) continue;
            ULONG_PTR oa = (ULONG_PTR)o;
            if (!ReadableFastC(rc, oa, 0x10)) continue;
            void* cls = *(void**)(oa + 0x10);
            if (!cls) continue;
            unsigned h = (unsigned)(((ULONG_PTR)cls >> 4) * 2654435761u) & 16383;
            signed char v = -1;
            for (int k = 0; k < 8; ++k) {
                CV& e = cache[(h + k) & 16383];
                if (e.c == cls) { v = e.v; break; }
                if (!e.c) {
                    void* c = cls; v = 0;
                    for (int d = 0; d < 32 && c; ++d) {
                        if (c == g_bsmClass) { v = 1; break; }
                        ULONG_PTR sa = (ULONG_PTR)c + g_superOff;
                        if (!ReadableFastC(rc, sa, 8)) break;
                        c = *(void**)sa;
                    }
                    e.c = cls; e.v = v; break;
                }
            }
            if (v != 1) continue;
            if (!ReadableFastC(rc, oa + 8, 4) || (*(UINT32*)(oa + 8) & 0x10)) continue;      // class default object
            if (!ReadableFastC(rc, oa + 0x44E, 1)) continue;
            ++nBsm;
            BYTE bteam = *(BYTE*)(oa + O_BA_TEAM);
            bool placed = (*(BYTE*)(oa + 0x446) & 1) != 0;            // ABuildingActor::bPlayerPlaced
            if (placed) { ++nPlaced; ++teamHist[bteam]; if (nPlacedCnt < BV_MAX) { placedList[nPlacedCnt] = o; placedIdx[nPlacedCnt] = i; ++nPlacedCnt; } }
            if (team <= 0 || bteam != (BYTE)team) continue;
            g_bvList[buf][cnt] = o; g_bvIdx[buf][cnt] = i; ++cnt;
        }
        // can't match your team (team unknown / different numbering): use every player-placed build
        bool fallback = cnt == 0 && nPlacedCnt > 0;
        if (fallback) {
            for (int k = 0; k < nPlacedCnt; ++k) { g_bvList[buf][k] = placedList[k]; g_bvIdx[buf][k] = placedIdx[k]; }
            cnt = nPlacedCnt;
        }
        g_bvCount[buf] = cnt;
        {
            static int logs; static int lastB = -1, lastP = -1, lastT = -2, lastC = -1;
            if (logs < 40 && (nBsm / 50 != lastB / 50 || nPlaced != lastP || team != lastT || cnt != lastC)) {
                ++logs; lastB = nBsm; lastP = nPlaced; lastT = team; lastC = cnt;
                int best = -1, bestN = 0; for (int t = 0; t < 256; ++t) if (teamHist[t] > bestN) { bestN = teamHist[t]; best = t; }
                char msg[160]; int k = 0;
                const char* a = "builds scan - buildings / player-placed / your team / most common build team / using:";
                while (*a) msg[k++] = *a++;
                msg[k] = 0;
                Log(msg);
                Log("   buildings", nBsm); Log("   player-placed", nPlaced); Log("   your team", team < 0 ? 0xFFFF : team);
                Log("   most common team on placed builds", best < 0 ? 0xFFFF : best);
                Log(fallback ? "   using all player-placed builds:" : "   using your team's builds:", cnt);
            }
        }
        InterlockedExchange(&g_bvPub, buf);
        buf ^= 1;
    }
}

// ---- helpers that call into the game (game thread only) ----
static int  CompNumMats(void* c) { struct { int ret; } p = { 0 }; g_pe(c, g_fnNumMat, &p); return p.ret; }
static void* CompGetMat(void* c, int i) { struct { int idx, pad; void* ret; } p = { i, 0, nullptr }; g_pe(c, g_fnGetMat, &p); return p.ret; }
static void CompSetMat(void* c, int i, void* m) { struct { int idx, pad; void* m; } p = { i, 0, m }; g_pe(c, g_fnSetMat, &p); }
static FNm  ToName(const wchar_t* s) {
    struct { FStr in; FNm ret; } p; int n = wlen(s) + 1;
    p.in = { s, n, n }; p.ret = { 0, 0 };
    g_pe(g_kstrCDO, g_fnStrToName, &p); return p.ret;
}
static void CompSetColor(void* c, FNm name, float r, float g, float b) {
    struct { FNm n; float x, y, z; } p = { name, r, g, b };
    g_pe(c, g_fnSetVecOnMats, &p);
}
static bool NameToStr(FNm n, wchar_t* out, int cap) {
    out[0] = 0;
    if (!g_fnNameToStr) return false;
    struct { FNm in; FStr ret; } p = { n, { nullptr, 0, 0 } };
    g_pe(g_kstrCDO, g_fnNameToStr, &p);
    if (!p.ret.data || p.ret.num <= 0 || !Readable(p.ret.data, (size_t)p.ret.num * 2)) return false;
    wcopy(out, p.ret.data, cap);           // (engine string is leaked: only used for a handful of names)
    return true;
}
static void LogObj(const char* what, void* o) {
    static int budget = 60;
    if (!o || !g_fnPathName || budget <= 0) return;
    --budget;
    struct { void* o; FStr ret; } p = { o, { nullptr, 0, 0 } };
    g_pe(g_kslCDO, g_fnPathName, &p);
    if (p.ret.data && p.ret.num > 0 && Readable(p.ret.data, (size_t)p.ret.num * 2)) Log(what, -1, p.ret.data);
}
static bool IsMat(void* o) { return o && Alive(o) && IsA(o, g_matIfClass); }

// UMaterialInstance::Parent: the first material pointer in the instance (found once)
static void* MatParent(void* m) {
    if (!m) return nullptr;
    if (o_MatParent < 0) {
        for (LONG_PTR off = 0x28; off < 0x200; off += 8) {
            void* p; if (!Rd(m, off, &p) || !p || p == m) continue;
            if (IsMat(p)) { o_MatParent = off; Log("builds: material parent offset", off); break; }
        }
        if (o_MatParent < 0) return nullptr;
    }
    void* p; if (!Rd(m, o_MatParent, &p) || !IsMat(p)) return nullptr;
    return p;
}

// Material parameter names (vector params) found in an instance's parameter list - by shape:
// { FName name; u8 association(0..2); pad; int32 index; FLinearColor value; [FGuid] }
static int VectorParamNames(void* mat, FNm* out, int max) {
    int n = 0;
    for (int depth = 0; mat && depth < 4 && n < max; ++depth, mat = MatParent(mat)) {
        for (LONG_PTR off = 0x28; off < 0x400 && n < max; off += 8) {
            void* data; int num, cap;
            if (!Rd(mat, off, &data) || !Rd(mat, off + 8, &num) || !Rd(mat, off + 12, &cap)) continue;
            if (!data || num <= 0 || num > 64 || cap < num || cap > 256) continue;
            static const int strides[2] = { 0x30, 0x20 };
            for (int stride : strides) {
                if (!Readable(data, (size_t)num * stride)) continue;
                BYTE* d = (BYTE*)data; bool good = true;
                for (int k = 0; k < num && good; ++k) {
                    BYTE* e = d + k * stride;
                    FNm nm = *(FNm*)e; BYTE assoc = e[8]; int index = *(int*)(e + 12);
                    float* col = (float*)(e + 16);
                    good = nm.idx > 0 && nm.num >= 0 && nm.num < 64 && assoc <= 2 && index >= -1 && index < 64;
                    for (int c = 0; c < 4 && good; ++c) good = col[c] > -1000.f && col[c] < 1000.f && col[c] == col[c];
                }
                if (!good) continue;
                for (int k = 0; k < num && n < max; ++k) {
                    FNm nm = *(FNm*)(d + k * stride);
                    bool dup = false; for (int q = 0; q < n; ++q) if (out[q].idx == nm.idx && out[q].num == nm.num) dup = true;
                    if (!dup) out[n++] = nm;
                }
                break;
            }
        }
    }
    return n;
}
static bool HasCI(const wchar_t* s, const wchar_t* sub) {
    for (; *s; ++s) {
        int k = 0;
        while (sub[k] && s[k] && (s[k] | 0x20) == (sub[k] | 0x20)) ++k;
        if (!sub[k]) return true;
    }
    return false;
}

// The colour parameters to drive for a material: its own colour/tint parameters (read from the
// material) plus common names. Cached per base material.
struct ColorNames { void* mat; int n; FNm names[16]; };
static ColorNames g_cnCache[64]; static int g_cnNext;
static const ColorNames* ColorNamesFor(void* mat) {
    for (int i = 0; i < 64; ++i) if (g_cnCache[i].mat == mat && mat) return &g_cnCache[i];
    ColorNames& c = g_cnCache[g_cnNext]; g_cnNext = (g_cnNext + 1) & 63;
    c.mat = mat; c.n = 0;
    FNm found[48]; int nf = VectorParamNames(mat, found, 48);     // the material and its parents
    static int logBudget = 6;
    bool doLog = logBudget > 0;
    if (doLog) { --logBudget; LogObj("builds: material", mat); Log("builds: vector parameters:", nf); }
    for (int i = 0; i < nf && c.n < 12; ++i) {
        wchar_t s[96]; if (!NameToStr(found[i], s, 96)) continue;
        if (doLog) Log("   param", -1, s);
        bool colorish = HasCI(s, L"color") || HasCI(s, L"colour") || HasCI(s, L"tint") || HasCI(s, L"albedo") || HasCI(s, L"diffuse");
        bool bad = HasCI(s, L"emiss") || HasCI(s, L"damage") || HasCI(s, L"edit") || HasCI(s, L"highlight") ||
                   HasCI(s, L"outline") || HasCI(s, L"fresnel") || HasCI(s, L"glow") || HasCI(s, L"fog");
        if (colorish && !bad) c.names[c.n++] = found[i];
    }
    static FNm common[8]; static int ncommon = -1;
    if (ncommon < 0) {
        ncommon = 0;
        static const wchar_t* const list[8] = { L"Color", L"BaseColor", L"Base Color", L"Tint", L"TintColor", L"Tint Color", L"ColorTint", L"Color Tint" };
        for (const wchar_t* w : list) { FNm f = ToName(w); if (f.idx) common[ncommon++] = f; }
    }
    for (int i = 0; i < ncommon && c.n < 16; ++i) {
        bool dup = false; for (int q = 0; q < c.n; ++q) if (c.names[q].idx == common[i].idx && c.names[q].num == common[i].num) dup = true;
        if (!dup) c.names[c.n++] = common[i];
    }
    return &c;
}

// Bubble wrap material for a build: the building's own "under construction" material
// (AnimatingMaterialMappings: { Original, Override }), the look OG builds kept.
static void* BubbleFor(void* actor, void* orig, int slot) {
    void* data; int num;
    if (!Rd(actor, O_BSM_ANIMMAPS, &data) || !Rd(actor, O_BSM_ANIMMAPS + 8, &num) || !data || num <= 0 || num > 16) return nullptr;
    if (!Readable(data, (size_t)num * 16)) return nullptr;
    void** pairs = (void**)data;
    static bool logged;
    if (!logged) {
        logged = true;
        Log("builds: construction material pairs:", num);
        for (int k = 0; k < num && k < 3; ++k) { LogObj("  from", pairs[k * 2]); LogObj("  to  ", pairs[k * 2 + 1]); }
    }
    // match the slot's material (or one of its parents) to an Original
    void* m = orig;
    for (int depth = 0; m && depth < 5; ++depth, m = MatParent(m))
        for (int k = 0; k < num; ++k) if (pairs[k * 2] == m && IsMat(pairs[k * 2 + 1])) return pairs[k * 2 + 1];
    if (slot == 0 && IsMat(pairs[1])) return pairs[1];
    return nullptr;
}

static const float BUILD_RGB[4][3] = { { 1.0f, 0.25f, 0.65f }, { 0.25f, 1.0f, 0.3f }, { 0.2f, 0.5f, 1.0f }, { 1.0f, 1.0f, 1.0f } };

// per-build record
struct BuildRec { void* actor; int idx; void* comp; int n; void* orig[4]; void* applied[4]; LONG gen; LONGLONG seen; };
static const int BR_MAX = 8192;
static BuildRec g_br[BR_MAX];
static int g_brCount;

static BuildRec* RecFor(void* actor, int idx, bool create) {
    for (int i = 0; i < g_brCount; ++i) if (g_br[i].actor == actor && g_br[i].idx == idx) return &g_br[i];
    if (!create) return nullptr;
    if (g_brCount >= BR_MAX) {          // drop dead ones
        int w = 0; for (int i = 0; i < g_brCount; ++i) if (AliveAt(g_br[i].actor, g_br[i].idx)) g_br[w++] = g_br[i];
        g_brCount = w;
        if (g_brCount >= BR_MAX) return nullptr;
    }
    BuildRec* r = &g_br[g_brCount++];
    *r = {}; r->actor = actor; r->idx = idx; return r;
}

// Puts a build's own materials back (feature switched off).
static int RestoreBuild(const BuildRec& r) {
    if (!AliveAt(r.actor, r.idx) || !Alive(r.comp)) return 0;
    void* comp; if (!Rd(r.actor, O_BSM_SMC, &comp) || comp != r.comp) return 0;
    int calls = 0;
    for (int i = 0; i < r.n; ++i) {
        void* cur = CompGetMat(comp, i); ++calls;
        if (r.applied[i] && cur == r.applied[i] && r.orig[i] && r.orig[i] != cur) { CompSetMat(comp, i, r.orig[i]); ++calls; }
    }
    return calls;
}

// Applies the build look on one build. Returns the number of engine calls made.
static int g_skip[6];
static int ApplyBuildLook(void* actor, int idx, bool bubble, bool color, int colorIdx) {
    if (!AliveAt(actor, idx)) { ++g_skip[0]; return 0; }
    void* editing = nullptr; Rd(actor, O_BSM_EDITING, &editing);
    if (editing) { ++g_skip[1]; return 0; }                        // being edited: leave the edit visuals alone
    BYTE uc = 0; Rd(actor, O_BSM_UNDERCON, &uc);
    if (uc & 1) {                                                  // still building: the game animates it
        ++g_skip[2];
        float prog = 1; Rd(actor, 0xA5C, &prog);                  // CurBuildProgress: trust it if construction looks done
        if (!(prog >= 0.999f && prog < 2.f)) return 0;
    }
    void* comp; if (!Rd(actor, O_BSM_SMC, &comp) || !Alive(comp) || !IsA(comp, g_primClass)) { ++g_skip[3]; return 0; }
    BuildRec* r = RecFor(actor, idx, true);
    if (!r) return 0;
    int calls = 0;
    if (r->comp != comp) { r->comp = comp; r->n = 0; r->gen = 0; }
    int n = CompNumMats(comp); ++calls;
    if (n <= 0) { ++g_skip[4]; return calls; }
    if (n > 4) n = 4;
    bool changed = r->n != n;
    void* cur[4];
    for (int i = 0; i < n; ++i) {
        cur[i] = CompGetMat(comp, i); ++calls;
        if (changed || cur[i] != r->applied[i]) { r->orig[i] = cur[i]; changed = true; }   // the game (re)set it
    }
    r->n = n;
    LONG gen = g_buildGen;
    if (!changed && r->gen == gen) return calls;                   // already looks right
    void* first = nullptr;
    for (int i = 0; i < n; ++i) {
        void* target = r->orig[i];
        if (bubble) { void* b = BubbleFor(actor, r->orig[i], i); if (b) target = b; }
        if (i == 0) first = target;
        if (target && target != cur[i]) { CompSetMat(comp, i, target); ++calls; }
    }
    if (color && first) {
        const float* c = BUILD_RGB[colorIdx & 3];
        const ColorNames* cn = ColorNamesFor(first);
        for (int k = 0; k < cn->n; ++k) { CompSetColor(comp, cn->names[k], c[0], c[1], c[2]); ++calls; }
    }
    for (int i = 0; i < n; ++i) { r->applied[i] = CompGetMat(comp, i); ++calls; }
    r->gen = gen;
    static int applied;
    if (applied < 3) {
        ++applied;
        Log("builds: look applied, material slots:", n);
        LogObj("   was", r->orig[0]);
        LogObj("   now", r->applied[0]);
    }
    return calls;
}

// Game thread: a slice of builds per call.
static void BuildLooksTick() {
    static LONGLONG last; static int cursor;
    LONGLONG now = Qpc();
    if (now - last < Ms(15)) return;
    last = now;
    if (!g_bvOK) return;
    bool bubble = g_bubble, color = g_customBuild;
    int colorIdx = g_buildColor;
    int calls = 0;
    if (!bubble && !color) {                                      // undo what we changed
        while (g_brCount > 0 && calls < 120) calls += 1 + RestoreBuild(g_br[--g_brCount]);
        return;
    }
    LONG pub = g_bvPub;
    if (pub < 0) return;
    int n = g_bvCount[pub];
    if (n <= 0) return;
    for (int k = 0; k < n && calls < 160; ++k) {
        cursor = (cursor + 1) % n;
        calls += ApplyBuildLook(g_bvList[pub][cursor], g_bvIdx[pub][cursor], bubble, color, colorIdx);
    }
    static LONGLONG lastSkipLog; static int skipLogs;
    if (skipLogs < 12 && now - lastSkipLog > Ms(5000)) {
        lastSkipLog = now; ++skipLogs;
        Log("builds tick - builds / skipped dead / editing / building / no mesh / no materials:", n);
        for (int i = 0; i < 5; ++i) Log("   ", g_skip[i]);
    }
}

// ---------------------------------------------------------------------
//  Input state shared between threads
// ---------------------------------------------------------------------
static volatile bool     g_down[256];
static volatile LONGLONG g_lastMsgQpc;        // last message the game pulled from its queue
static volatile LONGLONG g_selfDownSeenQpc;   // when the game pulled our confirm key-down
static volatile LONG     g_selfDown, g_selfUp;
static HANDLE            g_confirmEvent;

// fallback edit tracker (used when the engine state can't be read)
static bool     g_editing;
static bool     g_lmbArmed, g_resetArmed;
static LONGLONG g_editStartQpc, g_lastEditActQpc;
static volatile LONGLONG g_lastEditPressQpc;

// menu state
enum { ROW_RESET, ROW_INSTANT, ROW_BUBBLE, ROW_CUSTOM, ROW_BUILDCOL, ROW_STRETCH, ROW_STRETCH_RES, ROW_COLOR, ROW_COLOR_AMT, ROW_LATENCY, ROW_NORENDER,
       ROW_FOV, ROW_FPS, ROW_POTATO, ROW_COUNT,
       ROW_EDITKEY = 100, ROW_RESETKEY = 101 };  // key rows: read from the game now
static bool RowVisible(int r) {
    if (r == ROW_STRETCH || r == ROW_STRETCH_RES) return false;   // stretched res removed
    if (r == ROW_COLOR_AMT) return g_color;
    if (r == ROW_BUBBLE || r == ROW_CUSTOM || r == ROW_BUILDCOL) return false;   // build looks removed
    if (r == ROW_INSTANT) return false;          // instant is always on now, no row
    if (r == ROW_NORENDER) return false;         // no render limit removed
    return r >= 0 && r < ROW_COUNT;
}
static int VisibleRows(int* out) { int n = 0; for (int r = 0; r < ROW_COUNT; ++r) if (RowVisible(r)) out[n++] = r; return n; }
static int RowParent(int r) { return r == ROW_STRETCH_RES ? ROW_STRETCH : r == ROW_COLOR_AMT ? ROW_COLOR : r == ROW_INSTANT ? ROW_RESET : r == ROW_BUILDCOL ? ROW_CUSTOM : r; }
static volatile bool g_menuOpen;
static volatile int  g_listening = -1;
static volatile int  g_sel;
static volatile int  g_hover = -1;

enum { WM_CLOVER_REDRAW = WM_APP + 1, WM_CLOVER_MENU, WM_CLOVER_SAVE };
static volatile LONG g_redrawQueued;
static void RequestRedraw() {
    if (g_overlay && !InterlockedExchange(&g_redrawQueued, 1)) PostMessageW(g_overlay, WM_CLOVER_REDRAW, 0, 0);
}
static void RequestSave() { if (g_overlay) PostMessageW(g_overlay, WM_CLOVER_SAVE, 0, 0); }

// ---------------------------------------------------------------------
//  Confirm (presses the edit key for you)
// ---------------------------------------------------------------------
static void SendEditKey(bool down) {
    UINT vk = g_editKey;
    if (g_useSendInput) {
        INPUT in = {};
        if (IsMouseVk(vk)) {
            in.type = INPUT_MOUSE; in.mi.dwExtraInfo = CLOVER_TAG;
            switch (vk) {
            case VK_LBUTTON: in.mi.dwFlags = down ? MOUSEEVENTF_LEFTDOWN : MOUSEEVENTF_LEFTUP; break;
            case VK_RBUTTON: in.mi.dwFlags = down ? MOUSEEVENTF_RIGHTDOWN : MOUSEEVENTF_RIGHTUP; break;
            case VK_MBUTTON: in.mi.dwFlags = down ? MOUSEEVENTF_MIDDLEDOWN : MOUSEEVENTF_MIDDLEUP; break;
            default: in.mi.dwFlags = down ? MOUSEEVENTF_XDOWN : MOUSEEVENTF_XUP;
                     in.mi.mouseData = vk == VK_XBUTTON1 ? XBUTTON1 : XBUTTON2;
            }
        } else {
            in.type = INPUT_KEYBOARD;
            in.ki.wVk = (WORD)vk;
            in.ki.wScan = (WORD)MapVirtualKeyW(vk, MAPVK_VK_TO_VSC);
            in.ki.dwFlags = down ? 0 : KEYEVENTF_KEYUP;
            in.ki.dwExtraInfo = CLOVER_TAG;
        }
        SendInput(1, &in, sizeof(in));
        return;
    }
    // Post straight into the game's queue: no OS input path, no latency.
    HWND g = g_game;
    if (IsMouseVk(vk)) {
        POINT pt; GetCursorPos(&pt); ScreenToClient(g, &pt);
        LPARAM lp = MAKELPARAM(pt.x, pt.y);
        switch (vk) {
        case VK_MBUTTON: PostMessageW(g, down ? WM_MBUTTONDOWN : WM_MBUTTONUP, down ? MK_MBUTTON : 0, lp); break;
        case VK_RBUTTON: PostMessageW(g, down ? WM_RBUTTONDOWN : WM_RBUTTONUP, down ? MK_RBUTTON : 0, lp); break;
        case VK_LBUTTON: PostMessageW(g, down ? WM_LBUTTONDOWN : WM_LBUTTONUP, down ? MK_LBUTTON : 0, lp); break;
        default: {
            WORD xb = vk == VK_XBUTTON1 ? XBUTTON1 : XBUTTON2;
            PostMessageW(g, down ? WM_XBUTTONDOWN : WM_XBUTTONUP,
                         MAKEWPARAM(down ? (vk == VK_XBUTTON1 ? MK_XBUTTON1 : MK_XBUTTON2) : 0, xb), lp);
        }
        }
    } else {
        UINT sc = MapVirtualKeyW(vk, MAPVK_VK_TO_VSC);
        LPARAM lp = 0x7C1F | (sc << 16);                 // tag (repeat-count bits) = Clover's own press, never yours
        if (!down) lp |= (1u << 30) | (1u << 31);
        PostMessageW(g, down ? WM_KEYDOWN : WM_KEYUP, vk, lp);
    }
}

static HANDLE g_hrTimer;
// Waits until cond() is true or the timeout passes. Sub-millisecond precision.
template <class F> static bool WaitUntil(F cond, double timeoutMs) {
    LONGLONG end = Qpc() + Ms(timeoutMs);
    for (;;) {
        if (cond()) return true;
        if (Qpc() >= end) return false;
        if (g_hrTimer) {
            LARGE_INTEGER due; due.QuadPart = -2500;           // 0.25 ms
            SetWaitableTimer(g_hrTimer, &due, 0, nullptr, nullptr, FALSE);
            WaitForSingleObject(g_hrTimer, 2);
        } else {
            SwitchToThread();
        }
    }
}

static volatile LONG g_upOutstanding;  // our edit-key release still to send
static volatile LONGLONG g_downQpc;
static const LPARAM SELF_KEY_TAG = 0x7C1F;   // goes in the repeat-count bits of WM_KEYDOWN/UP

static volatile LONGLONG g_reqQpc;
static volatile bool     g_reqHint;          // your own key tracking thought you were editing

// The confirm. It always looks at the game's real state first: the edit key is only pressed while
// you're actually holding the edit tool, and if the game ignores the press (a single light scroll
// notch can land so the game drops it) it checks again a moment later and presses once more.
// Nothing here waits on anything else, so the next edit is never held up.
// Edit phase straight from the controller: 2 = edit mode open (EditBuildingActor),
// 1 = opening (PendingEnterEditModeActor, waiting on the server), 0 = neither, -1 = can't tell.
static const LONG_PTR O_PC_PENDINGEDIT = 0x2338;
static int EditPhase() {
    if (!g_reflOK) return -1;
    void* pc = LocalPC(); if (!pc) return -1;
    if (!g_fortPcClass) g_fortPcClass = Find(L"/Script/FortniteGame.FortPlayerController");
    if (!g_fortPcClass || !IsA(pc, g_fortPcClass)) return -1;
    void* a = nullptr; if (!Rd(pc, O_PC_EDITACTOR, &a)) return -1;
    if (a) return 2;
    void* p = nullptr; Rd(pc, O_PC_PENDINGEDIT, &p);
    return p ? 1 : 0;
}

// The confirm: ONE press of your edit key per edit, the frame right after the reset.
// If you scrolled while the edit was still opening (pressed edit + scrolled instantly), it waits
// for the edit to open first so the press isn't lost, then presses.
static DWORD WINAPI ConfirmThread(LPVOID) {
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);
    g_hrTimer = CreateWaitableTimerExW(nullptr, nullptr, CREATE_WAITABLE_TIMER_HIGH_RESOLUTION, TIMER_ALL_ACCESS);
    const LONGLONG gap = Ms(0.7);
    int logs = 0;
    for (;;) {
        WaitForSingleObject(g_confirmEvent, INFINITE);
        LONGLONG req = g_reqQpc;
        // 1) let the game finish reading this frame's input (the reset)
        WaitUntil([&] { LONGLONG n = Qpc(); return n - g_lastMsgQpc >= gap && n - req >= gap; }, 40);
        if (g_lastEditPressQpc > req) continue;             // you pressed edit yourself
        if (EditPhase() == 1) {
            // edit still opening: wait for it (at most your ping), then one frame
            LONGLONG w0 = Qpc();
            WaitUntil([&] { return EditPhase() != 1 || g_lastEditPressQpc > req; }, 300);
            if (logs < 10) { ++logs; Log("reset on release: waited for the edit to open (ms)", (LONG_PTR)((Qpc() - w0) * 1000 / g_qpf)); }
            if (g_lastEditPressQpc > req) continue;
            LONGLONG r2 = Qpc();
            WaitUntil([&] { LONGLONG n = Qpc(); return n - g_lastMsgQpc >= gap && n - r2 >= gap; }, 40);
        }
        if (InterlockedExchange(&g_upOutstanding, 0)) { g_selfUp = 1; SendEditKey(false); }
        LONGLONG t0 = Qpc();
        g_selfDown = 1;
        SendEditKey(true);                               // read at the start of the next frame
        g_downQpc = t0; g_upOutstanding = 1;
        // 2) let go once the game has read the press (the frame after)
        WaitUntil([&] { LONGLONG n = Qpc(); return g_selfDownSeenQpc >= t0 && n - g_lastMsgQpc >= gap; }, 40);
        if (InterlockedExchange(&g_upOutstanding, 0)) { g_selfUp = 1; SendEditKey(false); }
    }
}

static volatile bool g_confirmLatch;   // one confirm per edit: re-armed by your next edit-key press

// Game thread, called the moment the reset (scroll notch / key release) is seen.
static void RequestConfirm(bool hint) {
    if (!hint || g_confirmLatch) return;   // not editing / extra notches of the same scroll: nothing to do
    g_confirmLatch = true;
    g_reqHint = hint;
    g_reqQpc = Qpc();
    SetEvent(g_confirmEvent);
}

// ---------------------------------------------------------------------
//  Edit logic (runs on the game thread, inside its message loop)
// ---------------------------------------------------------------------
static void SetTracker(bool on, LONGLONG now) {
    if (g_editing != on) { g_editing = on; g_editStartQpc = now; }
    g_lmbArmed = false;
    g_lastEditActQpc = now;
}

static bool EditingNow(LONGLONG now) {
    int ph = EditPhase();
    if (ph >= 1) return true;                                  // the game says the edit is open / opening
    if (g_editing && g_editTimeoutMs > 0 && now - g_lastEditActQpc > Ms(g_editTimeoutMs)) g_editing = false;
    return g_editing;                                          // otherwise your key tracking
}

static void EditLogic(UINT vk, bool press, bool release, LONGLONG now) {
    if (vk == g_editKey) {
        if (press) { SetTracker(!g_editing, now); g_lastEditPressQpc = now; g_confirmLatch = false; }
        return;
    }
    if (vk == g_resetKey) {
        if (press) {
            g_resetArmed = EditingNow(now);
            g_lastEditActQpc = now;
        }
        if (release) {
            bool armed = g_resetArmed;
            g_resetArmed = false;
            // always ask: the confirm thread checks the game's real edit state before pressing anything
            if (g_resetOnRelease) RequestConfirm(armed);
            if (armed) g_editing = false;
        }
        return;
    }
    if (!g_editing) return;
    if (vk == VK_LBUTTON) {
        if (press) { g_lmbArmed = true; g_lastEditActQpc = now; }
        else if (release && g_lmbArmed) SetTracker(false, now);   // game's own edit-on-release
    }
    else if (press && (IsWheel(vk) || g_cancelKey[vk])) SetTracker(false, now);
}

static volatile LONGLONG g_potatoChangedQpc;
static volatile LONGLONG g_stretchChangedQpc;
static bool IsSlider(int row) { return row == ROW_FOV || row == ROW_FPS || row == ROW_POTATO || row == ROW_STRETCH_RES || row == ROW_COLOR_AMT; }
static bool IsCheck(int row)  { return row == ROW_RESET || row == ROW_INSTANT || row == ROW_BUBBLE || row == ROW_CUSTOM || row == ROW_STRETCH || row == ROW_COLOR || row == ROW_LATENCY || row == ROW_NORENDER; }
static int SliderMin(int row) { return row == ROW_FOV ? FOV_MIN : row == ROW_STRETCH_RES ? 0 : 1; }
static int SliderMax(int row) {
    if (row == ROW_STRETCH_RES) { int l[6]; return imax(1, StretchList(l) - 1); }
    return row == ROW_FOV ? FOV_MAX : row == ROW_COLOR_AMT ? 100 : 10;
}
static int SliderGet(int row) {
    switch (row) {
    case ROW_FOV: return g_fov;  case ROW_FPS: return g_fpsMult;  case ROW_POTATO: return g_potato;
    case ROW_STRETCH_RES: {                      // position in the list of available resolutions
        int l[6]; int n = StretchList(l), best = 0;
        for (int i = 0; i < n; ++i) if (l[i] <= g_stretchIdx) best = i;
        return best;
    }
    case ROW_COLOR_AMT: return g_colorAmt;
    }
    return 0;
}
static void SliderSet(int row, int v) {
    v = imax(SliderMin(row), imin(SliderMax(row), v));
    if (v == SliderGet(row)) return;
    switch (row) {
    case ROW_FOV: g_fov = v; break;
    case ROW_FPS: g_fpsMult = v; break;
    case ROW_POTATO: g_potato = v; g_potatoChangedQpc = Qpc(); g_gfxDirty = 1; break;
    case ROW_STRETCH_RES: { int l[6]; int n = StretchList(l); g_stretchIdx = l[imin(v, n - 1)]; g_stretchChangedQpc = Qpc(); break; }
    case ROW_COLOR_AMT: g_colorAmt = v; break;
    }
    RequestRedraw();
}
static bool CheckGet(int row) {
    switch (row) {
    case ROW_RESET: return g_resetOnRelease;  case ROW_INSTANT: return g_instant;  case ROW_STRETCH: return g_stretch;  case ROW_COLOR: return g_color;
    case ROW_LATENCY: return g_lowLat;  case ROW_NORENDER: return g_noRender;
    case ROW_BUBBLE: return g_bubble;  case ROW_CUSTOM: return g_customBuild;
    }
    return false;
}
static void CheckToggle(int row) {
    switch (row) {
    case ROW_RESET:    g_resetOnRelease = !g_resetOnRelease; break;
    case ROW_INSTANT:  g_instant = !g_instant; break;
    case ROW_STRETCH:  g_stretch = !g_stretch; g_stretchFailed = false; g_stretchAvailKnown = false; break;   // rescan modes
    case ROW_COLOR:    g_color = !g_color; break;
    case ROW_LATENCY:  g_lowLat = !g_lowLat; g_gfxDirty = 1; break;
    case ROW_NORENDER: g_noRender = !g_noRender; g_gfxDirty = 1; break;
    case ROW_BUBBLE:   g_bubble = !g_bubble; InterlockedIncrement(&g_buildGen); break;
    case ROW_CUSTOM:   g_customBuild = !g_customBuild; InterlockedIncrement(&g_buildGen); break;
    }
    if (!RowVisible(g_sel)) g_sel = RowParent(g_sel);
    RequestSave();
}
static void SetBuildColor(int c) {
    c = (c % 4 + 4) % 4;
    if (c == g_buildColor) return;
    g_buildColor = c; InterlockedIncrement(&g_buildGen); RequestSave(); RequestRedraw();
}
static void ActivateRow(int row) {
    if (row == ROW_BUILDCOL) { SetBuildColor(g_buildColor + 1); return; }
    if (IsCheck(row)) CheckToggle(row);
    else if (row == ROW_EDITKEY || row == ROW_RESETKEY) g_listening = g_listening == row ? -1 : row;
    else if (row == ROW_FOV) { SliderSet(row, g_fov == FOV_MIN ? 100 : FOV_MIN); RequestSave(); }
    else if (IsSlider(row)) { SliderSet(row, SliderGet(row) == SliderMin(row) ? SliderMax(row) : SliderMin(row)); RequestSave(); }
    RequestRedraw();
}
static int NextVisible(int from, int dir) {
    int r = from;
    for (int i = 0; i < ROW_COUNT; ++i) { r = (r + dir + ROW_COUNT) % ROW_COUNT; if (RowVisible(r)) return r; }
    return from;
}

// Returns true to swallow the message.
static bool OnInput(UINT vk, bool down, bool repeat, LONGLONG now) {
    if (vk >= 256) return false;
    bool was = g_down[vk];
    g_down[vk] = down;
    bool press = down && !was;
    bool release = !down && was;

    if (g_listening >= 0) {
        if (press) {
            bool ok = vk != VK_ESCAPE && vk != VK_LBUTTON && vk != MENU_KEY;
            if (g_listening == ROW_EDITKEY) {
                if (ok && !IsWheel(vk)) {
                    if (vk == g_resetKey) g_resetKey = g_editKey;
                    g_editKey = vk;
                }
            } else if (ok) {
                if (vk == g_editKey) g_editKey = g_resetKey;
                g_resetKey = vk;
            }
            g_listening = -1; RequestSave(); RequestRedraw();
        }
        return vk != VK_LBUTTON;
    }

    if (vk == MENU_KEY) {
        if (press) { g_menuOpen = !g_menuOpen; PostMessageW(g_overlay, WM_CLOVER_MENU, 0, 0); }
        return true;
    }

    if (g_menuOpen) {
        switch (vk) {
        case VK_UP:   if (down) { g_sel = NextVisible(g_sel, -1); RequestRedraw(); } return true;
        case VK_DOWN: if (down) { g_sel = NextVisible(g_sel, +1); RequestRedraw(); } return true;
        case VK_LEFT: case VK_RIGHT:
            if (g_sel == ROW_BUILDCOL) { if (press) SetBuildColor(g_buildColor + (vk == VK_RIGHT ? 1 : -1)); return true; }
            if (IsSlider(g_sel)) { if (down) SliderSet(g_sel, SliderGet(g_sel) + (vk == VK_RIGHT ? 1 : -1)); if (release) RequestSave(); }
            else if (press) ActivateRow(g_sel);
            return true;
        case VK_RETURN:
            if (press) ActivateRow(g_sel);
            return true;
        }
    }
    (void)repeat;
    EditLogic(vk, press, release, now);
    return false;
}

static HHOOK g_msgHook;
static const LPARAM FPS_MARKER = 0x46505321;
static volatile LONGLONG g_markerSeenQpc;
static volatile int      g_fpsReal;            // measured game FPS
static float* volatile   g_gAvgFps;            // engine's GAverageFPS (what Show FPS displays)
static float* volatile   g_gAvgMs;             // engine's GAverageMS
static volatile bool     g_fpsGaveUp;

static LRESULT CALLBACK GetMsgProc(int code, WPARAM wp, LPARAM lp) {
    if (code == HC_ACTION && (wp & PM_REMOVE)) {
        MSG* m = (MSG*)lp;
        LONGLONG now = Qpc();
        g_lastMsgQpc = now;
        UINT msg = m->message;
        if (msg == WM_NULL && m->wParam == CLOVER_TAG && m->lParam == FPS_MARKER) {
            g_markerSeenQpc = now;
            float* fps = g_gAvgFps; float* ms = g_gAvgMs;
            if (fps && ms && g_fpsMult > 1 && *ms > 0.01f) {
                // only ever touch it while it still looks like the engine's FPS value (FPS x ms = 1000)
                static int bad;
                float prod = *fps * *ms;
                if (fabs1(prod - 1000.f) < 2.f || (prod > 1000.f && prod < 1000.f * 10.5f)) { bad = 0; *fps = 1000.f / *ms * (float)g_fpsMult; }
                else if (++bad > 60) { g_gAvgFps = nullptr; g_gAvgMs = nullptr; WritePrivateProfileStringW(L"Clover", L"FpsValueRva", L"0", g_iniPath); }
            }
            goto done;
        }
        UINT vk = 0; bool down = false, repeat = false, wheel = false;
        switch (msg) {
        case WM_KEYDOWN: case WM_SYSKEYDOWN: vk = (UINT)(m->wParam & 0xFF); down = true; repeat = (m->lParam >> 30) & 1; break;
        case WM_KEYUP:   case WM_SYSKEYUP:   vk = (UINT)(m->wParam & 0xFF); break;
        case WM_LBUTTONDOWN: case WM_LBUTTONDBLCLK: vk = VK_LBUTTON; down = true; break;
        case WM_LBUTTONUP:   vk = VK_LBUTTON; break;
        case WM_RBUTTONDOWN: case WM_RBUTTONDBLCLK: vk = VK_RBUTTON; down = true; break;
        case WM_RBUTTONUP:   vk = VK_RBUTTON; break;
        case WM_MBUTTONDOWN: case WM_MBUTTONDBLCLK: vk = VK_MBUTTON; down = true; break;
        case WM_MBUTTONUP:   vk = VK_MBUTTON; break;
        case WM_XBUTTONDOWN: case WM_XBUTTONDBLCLK:
            vk = HIWORD(m->wParam) == XBUTTON1 ? VK_XBUTTON1 : VK_XBUTTON2; down = true; break;
        case WM_XBUTTONUP:   vk = HIWORD(m->wParam) == XBUTTON1 ? VK_XBUTTON1 : VK_XBUTTON2; break;
        case WM_MOUSEWHEEL:
            vk = (short)HIWORD(m->wParam) < 0 ? VK_WHEEL_DOWN : VK_WHEEL_UP; wheel = true; break;
        }
        if (vk) {
            // Our own confirm key: let it through untouched.
            bool self = false;
            if (vk == g_editKey) {
                if (g_useSendInput) self = GetMessageExtraInfo() == (LPARAM)CLOVER_TAG;
                else if (msg >= WM_KEYFIRST && msg <= WM_KEYLAST) self = (m->lParam & 0xFFFF) == SELF_KEY_TAG;
                else self = down ? g_selfDown > 0 : g_selfUp > 0;    // mouse-button edit key: counted
                if (self) {
                    static bool dropUp;
                    if (down) {
                        g_selfDown = 0; g_selfDownSeenQpc = now;
                        // never let our press reach the game once you've left edit mode
                        // (it would open edit on whatever you're looking at)

                    } else {
                        g_selfUp = 0;
                        if (dropUp) { m->message = WM_NULL; dropUp = false; }
                    }
                }
            }
            if (!self) {
                bool swallow;
                if (wheel) { swallow = OnInput(vk, true, false, now); OnInput(vk, false, false, now); }
                else swallow = OnInput(vk, down, repeat, now);
                if (swallow) m->message = WM_NULL;
            }
        }
    }
done:
    // Potato changes run here, on the game thread, a moment after the slider stops moving.
    if (code == HC_ACTION && g_peOK && g_gfxDirty && GameFocused() &&
        Qpc() - g_potatoChangedQpc > Ms(350) && PotatoWorld())
        ApplyGraphics();
    // Bubble wrap / custom build colours: a few builds per frame, on the game thread.
    if (code == HC_ACTION && g_bvOK && (g_bubble || g_customBuild || g_brCount > 0)) BuildLooksTick();
    return CallNextHookEx(g_msgHook, code, wp, lp);
}

// ---------------------------------------------------------------------
//  Engine thread: finds engine objects, applies FOV
// ---------------------------------------------------------------------
static DWORD WINAPI EngineThread(LPVOID) {
    float lastWritten = 0;
    int   tries = 0;
    bool  loggedPc = false, loggedApply = false, loggedBad = false;
    int   resetCount = 0, zeroCount = 0;
    LONGLONG lastAimQpc = 0;
    bool  fastTick = false;
    HANDLE tmr = CreateWaitableTimerExW(nullptr, nullptr, CREATE_WAITABLE_TIMER_HIGH_RESOLUTION, TIMER_ALL_ACCESS);
    Log("---- Clover started ----");
    for (;;) {
        if (!g_reflOK) {
            if (tries < 300 && !g_reflGaveUp && GameFocused()) {
                ++tries;
                if (InitReflection() || g_reflGaveUp) RequestRedraw();
            }
            if (tries >= 300) g_reflGaveUp = true;
            Sleep(2000);
            continue;
        }
        if (fastTick && tmr) {                    // ~200 Hz while zooming so it stays smooth
            LARGE_INTEGER due; due.QuadPart = -50000;
            SetWaitableTimer(tmr, &due, 0, nullptr, nullptr, FALSE);
            WaitForSingleObject(tmr, 20);
        } else Sleep(20);
        if (g_peOK && g_gfxDirty && !PotatoWorld()) FindCameras();   // graphics commands need a live camera
        if (!g_fovOK) continue;

        float want = g_fov > FOV_MIN ? (float)g_fov : 0.f;
        if (g_camScanMode && g_pcClass && !PcValid()) FindCameras();      // keep the controller for edit state
        void* cams[8]; int ncam = 0;
        if (g_camScanMode) {
            if (want == 0 && lastWritten == 0) continue;       // nothing to do, don't scan
            ncam = FindCameras();
            if (!ncam) { if (!loggedPc) { Log("FOV: camera not found yet"); loggedPc = true; } continue; }
            for (int i = 0; i < ncam; ++i) cams[i] = g_cams[i];
            if (!g_lockedSearchDone) {
                g_lockedSearchDone = true;
                g_lockedOffScan = FindLockedFovSlot(cams[0]);
                if (g_lockedOffScan < 0) { Log("FOV: slot not found in camera"); g_fovOK = false; RequestRedraw(); continue; }
                o_LockedFOV = g_lockedOffScan;
                Log("FOV: LockedFOV offset", o_LockedFOV);
                FindPovSlots(cams[0], o_LockedFOV - 4);
            }
        } else {
            void* pc = LocalPC();
            if (!pc) { if (want > 0 && !loggedPc) { Log("FOV: no local player controller yet"); loggedPc = true; } continue; }
            void* pcm; if (!Rd(pc, o_CameraManager, &pcm) || !pcm) continue;
            cams[0] = pcm; ncam = 1;
        }

        // Aiming / scopes: keep the game's zoom amount, relative to your custom FOV.
        if (want > 0 && g_povCount) {
            float ratio = 1.f;
            bool aiming = g_down[VK_RBUTTON];
            LONGLONG nowq = Qpc();
            if (aiming) lastAimQpc = nowq;
            bool settled = !aiming && nowq - lastAimQpc > Ms(400);
            for (int ci = 0; ci < ncam; ++ci) for (int k = 0; k < g_povCount; ++k) {
                float f; if (!Rd(cams[ci], g_povOff[k], &f) || f < 5 || f > 170) continue;
                if (lastWritten > 0 && fabs1(f - lastWritten) < 0.05f) continue;   // that's our own value echoed back
                if (ci == 0) {
                    if (settled || g_povHip[k] == 0) g_povHip[k] = f;          // your normal (hip) FOV
                    if (g_povHip[k] > 0) ratio = fmin2(ratio, f / g_povHip[k]);
                }
            }
            if (ratio < 0.999f) want = fmax2(5.f, want * ratio);
            fastTick = aiming || nowq - lastAimQpc < Ms(600);
        } else fastTick = false;

        bool wroteAny = false;
        for (int ci = 0; ci < ncam; ++ci) {
            float* locked = (float*)((char*)cams[ci] + o_LockedFOV);
            float cur;
            if (!Rd(locked, 0, &cur)) continue;
            // sanity: LockedFOV is 0 (unlocked) or a real FOV - anything else means wrong layout
            if (!(cur == 0 || (cur >= 5 && cur <= 170))) {
                if (!loggedBad) { Log("FOV: unexpected value at LockedFOV, skipping camera", ci); loggedBad = true; }
                continue;
            }
            if (want > 0) {
                if (cur != want) {
                    if (cur != 0 && cur != lastWritten && ++resetCount == 25)
                        Log("FOV: something else keeps changing the value (x100):", (LONG_PTR)(cur * 100));
                    if (lastWritten > 0 && cur == 0 && ++zeroCount == 25)
                        Log("FOV: game keeps resetting it to 0 on camera", ci);
                    if (Writable(locked, 4)) { *locked = want; wroteAny = true; }
                }
            } else if (lastWritten > 0 && cur == lastWritten && Writable(locked, 4)) {
                *locked = 0;   // only undo our own lock
            }
        }
        if (wroteAny && !loggedApply) { Log("FOV: written to cameras:", ncam); loggedApply = true; }
        lastWritten = want;
    }
}

// ---------------------------------------------------------------------
//  FPS measuring: one marker message per frame through the game's own
//  message pump (posted after each pump finishes, picked up at the next
//  frame's pump), so pump-to-pump time = frame time.
// ---------------------------------------------------------------------
enum { WM_CLOVER_FPS = WM_APP + 10 };

// GAverageFPS / GAverageMS sit next to each other in the exe's data and always satisfy
// FPS * MS == 1000 (FPS is computed as 1000 / MS every frame).
static int FindAvgFpsCandidates(float** fpsOut, float** msOut, int max, int realFps) {
    BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
    auto nt = (IMAGE_NT_HEADERS64*)(base + ((IMAGE_DOS_HEADER*)base)->e_lfanew);
    auto sec = IMAGE_FIRST_SECTION(nt);
    int n = 0;
    float lo = realFps * 0.6f, hi = realFps * 1.6f;
    for (int i = 0; i < nt->FileHeader.NumberOfSections && n < max; ++i) {
        if (!(sec[i].Characteristics & IMAGE_SCN_MEM_WRITE)) continue;
        float* f = (float*)(base + sec[i].VirtualAddress);
        size_t cnt = sec[i].Misc.VirtualSize / 4;
        for (size_t k = 0; k + 1 < cnt && n < max; ++k) {
            float a = f[k];
            if (!(a >= lo && a <= hi)) continue;
            for (int d = -2; d <= 2; ++d) {
                if (!d || (LONG_PTR)k + d < 0 || k + d >= cnt) continue;
                float b = f[k + d];
                if (b > 0.05f && b < 1000.f && fabs1(a * b - 1000.f) < 0.5f) { fpsOut[n] = &f[k]; msOut[n] = &f[k + d]; ++n; break; }
            }
        }
    }
    return n;
}

static DWORD WINAPI FpsThread(LPVOID) {
    HANDLE tmr = CreateWaitableTimerExW(nullptr, nullptr, CREATE_WAITABLE_TIMER_HIGH_RESOLUTION, TIMER_ALL_ACCESS);
    auto nap = [&](LONGLONG hundredNs) {
        if (tmr) { LARGE_INTEGER d; d.QuadPart = -hundredNs; SetWaitableTimer(tmr, &d, 0, nullptr, nullptr, FALSE); WaitForSingleObject(tmr, 50); }
        else SwitchToThread();
    };
    LONGLONG windowStart = 0, lastSeen = 0; int frames = 0;
    float* cf[16]; float* cm[16]; int ncand = -1, checks = 0, searches = 0;
    // last launch's location: check it right away so the multiplier works instantly
    {
        BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
        int rva = GetPrivateProfileIntW(L"Clover", L"FpsValueRva", 0, g_iniPath);
        int msd = GetPrivateProfileIntW(L"Clover", L"FpsMsDelta", 0, g_iniPath);
        if (rva > 0 && msd && msd >= -8 && msd <= 8) {
            float* f = (float*)(base + rva); float* m = (float*)(base + rva + msd);
            if (Readable(f, 4) && Readable(m, 4)) { g_gAvgFps = f; g_gAvgMs = m; Log("FPS: using saved engine FPS location"); }
        }
    }
    LONGLONG lastCheck = 0;
    for (;;) {
        if (g_fpsMult <= 1 || !GameFocused()) {
            if (g_fpsReal) { g_fpsReal = 0; PostMessageW(g_overlay, WM_CLOVER_FPS, 0, 0); }
            frames = 0; windowStart = 0; lastSeen = 0;
            Sleep(250);
            continue;
        }
        LONGLONG posted = Qpc();
        PostMessageW(g_game, WM_NULL, CLOVER_TAG, FPS_MARKER);
        LONGLONG deadline = posted + Ms(250);
        while (g_markerSeenQpc < posted && Qpc() < deadline) nap(2000);       // 0.2 ms
        LONGLONG seen = g_markerSeenQpc;
        if (seen < posted) continue;
        if (lastSeen) {
            ++frames;
            if (!windowStart) windowStart = lastSeen;
            if (seen - windowStart >= Ms(500)) {
                g_fpsReal = (int)((double)frames * (double)g_qpf / (double)(seen - windowStart) + 0.5);
                PostMessageW(g_overlay, WM_CLOVER_FPS, 0, 0);
                // Locate the engine's FPS value (once): find candidates, then keep the ones that stay valid.
                if (!g_gAvgFps && !g_fpsGaveUp && g_fpsReal > 5 && seen - lastCheck > Ms(1500)) {
                    lastCheck = seen;
                    if (ncand <= 0) {
                        ncand = FindAvgFpsCandidates(cf, cm, 16, g_fpsReal); checks = 0;
                        Log("FPS: engine value candidates:", ncand);
                        if (ncand == 0 && ++searches >= 5) { g_fpsGaveUp = true; Log("FPS: engine FPS value not found"); PostMessageW(g_overlay, WM_CLOVER_REDRAW, 0, 0); }
                    } else {
                        int keep = 0;
                        for (int i = 0; i < ncand; ++i) {
                            float a = *cf[i], b = *cm[i];
                            if (a > 0 && fabs1(a * b - 1000.f) < 0.5f && a > g_fpsReal * 0.6f && a < g_fpsReal * 1.6f) { cf[keep] = cf[i]; cm[keep] = cm[i]; ++keep; }
                        }
                        ncand = keep;
                        if (ncand == 1 && ++checks >= 2) {
                            g_gAvgMs = cm[0]; g_gAvgFps = cf[0];
                            {
                                wchar_t num[16]; BYTE* base = (BYTE*)GetModuleHandleW(nullptr);
                                itow((int)((BYTE*)cf[0] - base), num); WritePrivateProfileStringW(L"Clover", L"FpsValueRva", num, g_iniPath);
                                itow((int)((BYTE*)cm[0] - (BYTE*)cf[0]), num); WritePrivateProfileStringW(L"Clover", L"FpsMsDelta", num, g_iniPath);
                            }
                            Log("FPS: engine FPS value found at exe+", (LONG_PTR)((BYTE*)cf[0] - (BYTE*)GetModuleHandleW(nullptr)));
                            PostMessageW(g_overlay, WM_CLOVER_REDRAW, 0, 0);
                        } else if (ncand > 1 && ++checks >= 6) {
                            // still ambiguous: they all hold the same thing, multiply the first pair
                            g_gAvgMs = cm[0]; g_gAvgFps = cf[0];
                            Log("FPS: several matches, using first:", ncand);
                        }
                    }
                }
                frames = 0; windowStart = seen;
            }
        }
        lastSeen = seen;
        // wait until this frame's pump is done so the next marker lands in the next frame
        while (Qpc() - g_lastMsgQpc < Ms(0.6) && Qpc() - seen < Ms(100)) nap(2000);
    }
}

// ---------------------------------------------------------------------
//  Rendering  (software, anti-aliased, per-pixel alpha)
// ---------------------------------------------------------------------
struct Col { float r, g, b, a; };
static constexpr Col rgba(int hex, float a) { return { ((hex >> 16) & 255) / 255.f, ((hex >> 8) & 255) / 255.f, (hex & 255) / 255.f, a }; }

static const int PANEL_W = 340, MARGIN = 22, ROW_H = 46, ROWS_TOP = 66;
static const int PANEL_H = ROWS_TOP + ROW_COUNT * ROW_H + 8;          // tallest (all rows open)
static int PanelHeight() { int v[ROW_COUNT]; return ROWS_TOP + VisibleRows(v) * ROW_H + 8; }
static const int SURF_W = PANEL_W + MARGIN * 2, SURF_H = PANEL_H + MARGIN * 2;

static constexpr Col C_BG     = rgba(0x101412, 0.96f);
static constexpr Col C_BORDER = rgba(0xFFFFFF, 0.08f);
static constexpr Col C_TEXT   = rgba(0xEEF2EF, 1.0f);
static constexpr Col C_DIM    = rgba(0x8B9590, 1.0f);
static constexpr Col C_ACCENT = rgba(0x3DDC84, 1.0f);
static constexpr Col C_ROW    = rgba(0xFFFFFF, 0.055f);
static constexpr Col C_LINE   = rgba(0xFFFFFF, 0.07f);

static HDC      g_dc, g_maskDc;
static HBITMAP  g_bmp, g_maskBmp;
static UINT32*  g_px;
static UINT32*  g_mask;
static UINT32*  g_bgCache;
static HFONT    g_fTitle, g_fRow, g_fSmall;
static int      g_alpha;
static bool     g_dragging;

static void BlendPx(int x, int y, Col c, float cov) {
    if (x < 0 || y < 0 || x >= SURF_W || y >= SURF_H) return;
    float a = c.a * cov;
    if (a <= 0.002f) return;
    UINT32& d = g_px[y * SURF_W + x];
    float db = (d & 255) / 255.f, dg = ((d >> 8) & 255) / 255.f, dr = ((d >> 16) & 255) / 255.f, da = (d >> 24) / 255.f;
    float ia = 1 - a;
    float r = c.r * a + dr * ia, g = c.g * a + dg * ia, b = c.b * a + db * ia, al = a + da * ia;
    d = ((UINT32)(al * 255 + .5f) << 24) | ((UINT32)(r * 255 + .5f) << 16) | ((UINT32)(g * 255 + .5f) << 8) | (UINT32)(b * 255 + .5f);
}

static float sdRoundBox(float px, float py, float x, float y, float w, float h, float r) {
    float cx = x + w * .5f, cy = y + h * .5f;
    float qx = fabs1(px - cx) - w * .5f + r, qy = fabs1(py - cy) - h * .5f + r;
    float ox = fmax2(qx, 0), oy = fmax2(qy, 0);
    return fsqrt(ox * ox + oy * oy) + fmin2(fmax2(qx, qy), 0) - r;
}
static float sdCircle(float px, float py, float cx, float cy, float r) {
    float dx = px - cx, dy = py - cy; return fsqrt(dx * dx + dy * dy) - r;
}
static float sdSeg(float px, float py, float ax, float ay, float bx, float by, float r) {
    float pax = px - ax, pay = py - ay, bax = bx - ax, bay = by - ay;
    float h = clamp01((pax * bax + pay * bay) / (bax * bax + bay * bay));
    float dx = pax - bax * h, dy = pay - bay * h; return fsqrt(dx * dx + dy * dy) - r;
}

template <class F>
static void FillSDF(int x0, int y0, int x1, int y1, Col c, F sdf) {
    x0 = imax(x0, 0); y0 = imax(y0, 0); x1 = imin(x1, SURF_W); y1 = imin(y1, SURF_H);
    for (int y = y0; y < y1; ++y)
        for (int x = x0; x < x1; ++x) {
            float cov = clamp01(.5f - sdf(x + .5f, y + .5f));
            if (cov > 0) BlendPx(x, y, c, cov);
        }
}
static void FillRound(float x, float y, float w, float h, float r, Col c) {
    FillSDF((int)x - 1, (int)y - 1, (int)(x + w) + 2, (int)(y + h) + 2, c,
        [=](float px, float py) { return sdRoundBox(px, py, x, y, w, h, r); });
}
static void StrokeRound(float x, float y, float w, float h, float r, float t, Col c) {
    FillSDF((int)x - 1, (int)y - 1, (int)(x + w) + 2, (int)(y + h) + 2, c,
        [=](float px, float py) { float d = sdRoundBox(px, py, x, y, w, h, r); return fmax2(d, -(d + t)); });
}
static void FillCircle(float cx, float cy, float r, Col c) {
    FillSDF((int)(cx - r) - 1, (int)(cy - r) - 1, (int)(cx + r) + 2, (int)(cy + r) + 2, c,
        [=](float px, float py) { return sdCircle(px, py, cx, cy, r); });
}

static int TextWidth(HFONT f, const wchar_t* s) {
    SelectObject(g_maskDc, f);
    SIZE sz = {}; GetTextExtentPoint32W(g_maskDc, s, wlen(s), &sz); return sz.cx;
}
static void DrawText2(HFONT f, const wchar_t* s, int x, int y, Col c) {
    SelectObject(g_maskDc, f);
    SIZE sz = {}; GetTextExtentPoint32W(g_maskDc, s, wlen(s), &sz);
    int w = sz.cx + 4, h = sz.cy + 2;
    int x0 = imax(x, 0), y0 = imax(y, 0), x1 = imin(x + w, SURF_W), y1 = imin(y + h, SURF_H);
    for (int yy = y0; yy < y1; ++yy) for (int xx = x0; xx < x1; ++xx) g_mask[yy * SURF_W + xx] = 0;
    SetBkMode(g_maskDc, TRANSPARENT);
    SetTextColor(g_maskDc, RGB(255, 255, 255));
    TextOutW(g_maskDc, x, y, s, wlen(s));
    GdiFlush();
    for (int yy = y0; yy < y1; ++yy) for (int xx = x0; xx < x1; ++xx) {
        int g = (int)((g_mask[yy * SURF_W + xx] >> 8) & 255);
        if (g) BlendPx(xx, yy, c, g / 255.f);
    }
}

// p: 0 = off, 1 = on. In between it simply cross-fades.
static void DrawCheckbox(float x, float y, float p, bool focused) {
    const float sz = 20;
    if (p < 1) {
        FillRound(x, y, sz, sz, 6, rgba(0xFFFFFF, 0.04f * (1 - p)));
        StrokeRound(x, y, sz, sz, 6, 1.5f, rgba(0xFFFFFF, (focused ? 0.38f : 0.24f) * (1 - p)));
    }
    if (p > 0) {
        Col fill = C_ACCENT; fill.a = p;
        FillRound(x, y, sz, sz, 6, fill);
        Col ink = rgba(0x0B100D, p);
        FillSDF((int)x, (int)y, (int)(x + sz) + 1, (int)(y + sz) + 1, ink, [=](float px, float py) {
            float d = sdSeg(px, py, x + 5.2f, y + 10.3f, x + 8.6f, y + 13.8f, 1.15f);
            return fmin2(d, sdSeg(px, py, x + 8.6f, y + 13.8f, x + 14.8f, y + 6.6f, 1.15f));
        });
    }
}

// --- checkbox fade state per row (UI thread) ---
static float    g_chkFrom[ROW_COUNT], g_chkTo[ROW_COUNT], g_chkVal[ROW_COUNT];
static LONGLONG g_chkStart[ROW_COUNT];
static bool     g_chkAnim[ROW_COUNT], g_chkInit[ROW_COUNT];
static const double CHECK_ANIM_MS = 180;

static float CheckValue(int row) {
    float target = CheckGet(row) ? 1.f : 0.f;
    LONGLONG now = Qpc();
    if (!g_chkInit[row]) { g_chkInit[row] = true; g_chkFrom[row] = g_chkTo[row] = g_chkVal[row] = target; }
    if (target != g_chkTo[row]) {
        g_chkFrom[row] = g_chkVal[row]; g_chkTo[row] = target; g_chkStart[row] = now;
        if (g_alpha > 0) { g_chkAnim[row] = true; SetTimer(g_overlay, 3, 8, nullptr); }
        else g_chkFrom[row] = g_chkVal[row] = target;
    }
    if (g_chkAnim[row]) {
        float t = clamp01((float)((double)(now - g_chkStart[row]) / (double)Ms(CHECK_ANIM_MS)));
        float e = t * t * (3 - 2 * t);               // smoothstep fade
        g_chkVal[row] = g_chkFrom[row] + (g_chkTo[row] - g_chkFrom[row]) * e;
        if (t >= 1) { g_chkAnim[row] = false; g_chkVal[row] = g_chkTo[row]; }
    } else g_chkVal[row] = g_chkTo[row];
    return g_chkVal[row];
}
static bool AnyCheckAnimating() { for (int r = 0; r < ROW_COUNT; ++r) if (g_chkAnim[r]) return true; return false; }

static int RowY(int row) {
    int v[ROW_COUNT]; int n = VisibleRows(v);
    for (int i = 0; i < n; ++i) if (v[i] == row) return MARGIN + ROWS_TOP + i * ROW_H;
    return -1000;
}

// colour boxes (Custom Builds -> Color), right-aligned in the row
static const float SW_SZ = 20, SW_GAP = 12;
static void SwatchPos(int k, int ry, float* x, float* y) {
    float right = MARGIN + PANEL_W - 22;
    *x = right - (4 - k) * SW_SZ - (3 - k) * SW_GAP;
    *y = ry + (ROW_H - SW_SZ) / 2 - 1;
}
static int HitSwatch(int x, int y, int ry) {
    for (int k = 0; k < 4; ++k) {
        float sx, sy; SwatchPos(k, ry, &sx, &sy);
        if (x >= sx - SW_GAP / 2 && x < sx + SW_SZ + SW_GAP / 2 && y >= ry && y < ry + ROW_H) return k;
    }
    return -1;
}

// slider geometry (surface coords)
static const float SL_X0 = MARGIN + 146, SL_X1 = MARGIN + PANEL_W - 108;

static int g_bgHeight;
static void BuildBackground() {
    int H0 = PanelHeight();
    g_bgHeight = H0;
    for (int i = 0; i < SURF_W * SURF_H; ++i) g_px[i] = 0;
    const float X = MARGIN, Y = MARGIN, W = PANEL_W, H = (float)H0, R = 16;
    for (int y = 0; y < imin(SURF_H, H0 + MARGIN * 2); ++y) for (int x = 0; x < SURF_W; ++x) {
        float d = sdRoundBox(x + .5f, y + .5f, X, Y + 5, W, H, R);
        if (d > 0) { float t = 1 - clamp01(d / (MARGIN - 2)); BlendPx(x, y, rgba(0, 1), 0.42f * t * t); }
    }
    FillRound(X, Y, W, H, R, C_BG);
    StrokeRound(X, Y, W, H, R, 1, C_BORDER);
    int tw = TextWidth(g_fTitle, L"Clover");
    DrawText2(g_fTitle, L"Clover", (int)(X + (W - tw) / 2), (int)Y + 14, C_TEXT);
    FillRound(X + 16, Y + 56, W - 32, 1, 0, C_LINE);
    memcpy(g_bgCache, g_px, SURF_W * SURF_H * 4);
}

static void Present() {
    POINT src = { 0, 0 };
    SIZE sz = { SURF_W, SURF_H };
    BLENDFUNCTION bf = { AC_SRC_OVER, 0, (BYTE)g_alpha, AC_SRC_ALPHA };
    UpdateLayeredWindow(g_overlay, nullptr, nullptr, &sz, g_dc, &src, 0, &bf, ULW_ALPHA);
}

static void PlaceOverlay();

static void Redraw() {
    g_redrawQueued = 0;
    if (!g_px || (!g_menuOpen && g_alpha == 0)) return;   // nothing to draw while hidden
    if (PanelHeight() != g_bgHeight) { BuildBackground(); PlaceOverlay(); }
    memcpy(g_px, g_bgCache, SURF_W * SURF_H * 4);
    const float X = MARGIN, W = PANEL_W;

    int vis[ROW_COUNT]; int nv = VisibleRows(vis);
    for (int i = 0; i < nv; ++i) {
        int row = vis[i];
        int ry = RowY(row);
        bool sub = row == ROW_STRETCH_RES || row == ROW_COLOR_AMT || row == ROW_INSTANT || row == ROW_BUILDCOL;
        bool focused = row == g_sel || row == g_hover;
        if (focused) FillRound(X + 8, (float)ry + 1, W - 16, ROW_H - 4, 11, C_ROW);
        if (row == g_sel) FillRound(X + 8, (float)ry + 12, 3, ROW_H - 26, 1.5f, C_ACCENT);
        int tx = (int)X + (sub ? 40 : 22);
        if (sub) FillRound(X + 26, (float)ry + 8, 2, ROW_H - 18, 1, rgba(0x3DDC84, 0.35f));   // child marker

        if (IsCheck(row)) {
            const wchar_t* label = row == ROW_RESET ? L"Reset on release" : row == ROW_INSTANT ? L"Instant (same frame)" : row == ROW_STRETCH ? L"Stretched Res" :
                                   row == ROW_COLOR ? L"Color Booster" : row == ROW_LATENCY ? L"Low Latency" :
                                   row == ROW_BUBBLE ? L"Bubble Wrap Builds" : row == ROW_CUSTOM ? L"Custom Builds" : L"No Render Limit";
            bool ok = true;
            if (row == ROW_BUBBLE || row == ROW_CUSTOM) ok = !g_bvGaveUp && !g_peGaveUp;
            if (row == ROW_COLOR) ok = !colorfx::g_failed;
            if (row == ROW_LATENCY || row == ROW_NORENDER) ok = g_peOK || !g_peGaveUp;
            (void)g_stretchFailed;
            DrawText2(sub ? g_fSmall : g_fRow, label, tx, ry + (sub ? 13 : 10), ok ? (sub ? C_DIM : C_TEXT) : C_DIM);
            if (!ok) {
                int w = TextWidth(g_fSmall, L"N/A");
                DrawText2(g_fSmall, L"N/A", (int)(X + W - 22 - w), ry + 12, C_DIM);
            } else DrawCheckbox(X + W - 22 - 20, (float)ry + 12, CheckValue(row), focused);
        }
        else if (row == ROW_BUILDCOL) {
            DrawText2(g_fSmall, L"Color", tx, ry + 13, C_DIM);
            for (int k = 0; k < 4; ++k) {
                float sx, sy; SwatchPos(k, ry, &sx, &sy);
                bool on = k == g_buildColor;
                const float* c = BUILD_RGB[k];
                Col fill = { c[0], c[1], c[2], 1.f };
                if (on) StrokeRound(sx - 3, sy - 3, SW_SZ + 6, SW_SZ + 6, 8, 2, rgba(0xFFFFFF, 0.9f));
                FillRound(sx, sy, SW_SZ, SW_SZ, 6, fill);
                StrokeRound(sx, sy, SW_SZ, SW_SZ, 6, 1, rgba(0x000000, 0.25f));
            }
        }
        else if (IsSlider(row)) {
            bool ok = true;
            const wchar_t* label = L"FOV";
            switch (row) {
            case ROW_FOV: ok = g_fovOK || (!g_reflOK && !g_reflGaveUp); break;
            case ROW_FPS: label = L"FPS Multiplier"; ok = !g_fpsGaveUp; break;
            case ROW_POTATO: label = L"Potato"; ok = g_peOK || !g_peGaveUp; break;
            case ROW_STRETCH_RES: label = L"Resolution"; break;
            case ROW_COLOR_AMT: label = L"Strength"; break;
            }
            DrawText2(sub ? g_fSmall : g_fRow, label, tx, ry + (sub ? 13 : 10), ok ? (sub ? C_DIM : C_TEXT) : C_DIM);
            int v = SliderGet(row), mn = SliderMin(row), mx = SliderMax(row);
            float t = mx > mn ? (float)(v - mn) / (mx - mn) : 0.f;
            if (row == ROW_STRETCH_RES) v = g_stretchIdx;          // label shows the real resolution
            float cy = ry + 21.f, kx = SL_X0 + t * (SL_X1 - SL_X0);
            FillRound(SL_X0, cy - 2, SL_X1 - SL_X0, 4, 2, rgba(0xFFFFFF, 0.12f));
            if (t > 0) FillRound(SL_X0, cy - 2, kx - SL_X0, 4, 2, ok ? C_ACCENT : C_DIM);
            FillCircle(kx, cy, 7.5f, ok ? rgba(0xF4F7F5, 1) : C_DIM);
            wchar_t txt[24];
            bool off = v == mn && row != ROW_STRETCH_RES && row != ROW_COLOR_AMT;
            if (!ok) wcopy(txt, L"N/A", 24);
            else if (row == ROW_STRETCH_RES) {
                itow(STRETCH_W[v], txt); int k = wlen(txt); wcopy(txt + k, L"x1080", 24 - k);
                if (g_stretchAvailKnown && !g_stretchAvail[v]) {               // monitor doesn't offer it (yet)
                    ok = false; itow(STRETCH_W[v], txt); int q = wlen(txt); wcopy(txt + q, L"  N/A", 24 - q);
                }
            }
            else if (row == ROW_COLOR_AMT) { itow(v, txt); int k = wlen(txt); txt[k] = L'%'; txt[k + 1] = 0; }
            else if (row == ROW_POTATO) wcopy(txt, POTATO_NAME[v], 24);
            else if (off) wcopy(txt, row == ROW_FOV ? L"Default" : L"Off", 24);
            else { itow(v, txt); if (row == ROW_FPS) { int k = wlen(txt); txt[k] = L'x'; txt[k + 1] = 0; } }
            int vw = TextWidth(g_fSmall, txt);
            DrawText2(g_fSmall, txt, (int)(X + W - 22 - vw), ry + 12, off || !ok ? C_DIM : C_TEXT);
        }
    }
    Present();
}

static RECT g_lastPlace;
static void PlaceOverlay() {
    HWND g = g_game; if (!g) return;
    RECT rc; GetClientRect(g, &rc);
    POINT p = { (rc.right - rc.left) / 2, (rc.bottom - rc.top) / 2 };
    ClientToScreen(g, &p);
    RECT want = { p.x - SURF_W / 2, p.y - (PanelHeight() / 2 + MARGIN), 0, 0 };   // panel centred on screen
    if (want.left == g_lastPlace.left && want.top == g_lastPlace.top) return;
    g_lastPlace = want;
    SetWindowPos(g_overlay, HWND_TOPMOST, want.left, want.top, 0, 0, SWP_NOACTIVATE | SWP_NOSIZE);
}

static void CreateCanvas() {
    BITMAPINFO bi = {};
    bi.bmiHeader.biSize = sizeof(bi.bmiHeader);
    bi.bmiHeader.biWidth = SURF_W;
    bi.bmiHeader.biHeight = -SURF_H;
    bi.bmiHeader.biPlanes = 1;
    bi.bmiHeader.biBitCount = 32;
    bi.bmiHeader.biCompression = BI_RGB;
    HDC screen = GetDC(nullptr);
    g_dc = CreateCompatibleDC(screen);
    g_maskDc = CreateCompatibleDC(screen);
    g_bmp = CreateDIBSection(screen, &bi, DIB_RGB_COLORS, (void**)&g_px, nullptr, 0);
    g_maskBmp = CreateDIBSection(screen, &bi, DIB_RGB_COLORS, (void**)&g_mask, nullptr, 0);
    ReleaseDC(nullptr, screen);
    SelectObject(g_dc, g_bmp);
    SelectObject(g_maskDc, g_maskBmp);
    g_bgCache = (UINT32*)VirtualAlloc(nullptr, SURF_W * SURF_H * 4, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);

    auto font = [](int px, int weight) {
        return CreateFontW(-px, 0, 0, 0, weight, FALSE, FALSE, FALSE, DEFAULT_CHARSET, OUT_TT_PRECIS,
                           CLIP_DEFAULT_PRECIS, ANTIALIASED_QUALITY, DEFAULT_PITCH, L"Segoe UI");
    };
    g_fTitle = font(23, FW_BOLD);
    g_fRow   = font(15, FW_SEMIBOLD);
    g_fSmall = font(13, FW_SEMIBOLD);
    BuildBackground();
}

static int HitRow(int x, int y) {
    int vis[ROW_COUNT]; int n = VisibleRows(vis);
    for (int i = 0; i < n; ++i) {
        int ry = RowY(vis[i]);
        if (x >= MARGIN + 8 && x < MARGIN + PANEL_W - 8 && y >= ry && y < ry + ROW_H) return vis[i];
    }
    return -1;
}
static int g_dragRow = -1;
static void SliderFromX(int row, int x) {
    float t = clamp01((x - SL_X0) / (SL_X1 - SL_X0));
    SliderSet(row, SliderMin(row) + (int)(t * (SliderMax(row) - SliderMin(row)) + .5f));
}

enum { TIMER_TRACK = 1, TIMER_FADE = 2, TIMER_CHECK = 3 };

static void InstallMsgHook() {
    DWORD tid = GetWindowThreadProcessId(g_game, nullptr);
    if (tid == g_gameTid && g_msgHook) return;
    if (g_msgHook) UnhookWindowsHookEx(g_msgHook);
    g_gameTid = tid;
    g_msgHook = SetWindowsHookExW(WH_GETMESSAGE, GetMsgProc, g_hMod, tid);
}

static LRESULT CALLBACK OverlayProc(HWND h, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_MOUSEACTIVATE: return MA_NOACTIVATE;
    case WM_CLOVER_REDRAW: Redraw(); return 0;
    case WM_CLOVER_SAVE:   SaveSettings(); return 0;
    case WM_CLOVER_FPS:    return 0;
    case WM_CLOVER_MENU:
        g_listening = -1;
        if (g_menuOpen && GameFocused()) {
            PlaceOverlay();
            if (!IsWindowVisible(h)) { g_alpha = 0; ShowWindow(h, SW_SHOWNOACTIVATE); }
        }
        SetTimer(h, TIMER_FADE, 12, nullptr);
        Redraw();
        return 0;
    case WM_MOUSEMOVE: {
        int x = (short)LOWORD(lp), y = (short)HIWORD(lp);
        if (g_dragging) { SliderFromX(g_dragRow, x); return 0; }
        int r = HitRow(x, y);
        if (r != g_hover) { g_hover = r; if (r >= 0) g_sel = r; Redraw(); }
        TRACKMOUSEEVENT t = { sizeof(t), TME_LEAVE, h, 0 }; TrackMouseEvent(&t);
        return 0;
    }
    case WM_MOUSELEAVE: if (g_hover != -1) { g_hover = -1; Redraw(); } return 0;
    case WM_LBUTTONDOWN: {
        int x = (short)LOWORD(lp), y = (short)HIWORD(lp);
        int r = HitRow(x, y);
        if (r < 0) return 0;
        g_sel = r;
        if (IsSlider(r)) { g_dragging = true; g_dragRow = r; SetCapture(h); SliderFromX(r, x); }
        else if (r == ROW_BUILDCOL) { int k = HitSwatch(x, y, RowY(r)); if (k >= 0) SetBuildColor(k); Redraw(); }
        else ActivateRow(r);
        return 0;
    }
    case WM_LBUTTONUP:
        if (g_dragging) { g_dragging = false; ReleaseCapture(); SaveSettings(); }
        return 0;
    case WM_TIMER:
        if (wp == TIMER_TRACK) {
            // color booster only while you're in the game
            {
                // Colour booster now lives inside Fortnite's own picture (only Fortnite changes).
                static bool driverRestored;
                if (!driverRestored && g_game) {
                    driverRestored = true;
                    // put the monitor's own colour setting back to your normal once (older Clover builds changed it)
                    ColorApply(0);
                    if (g_nvOK) NvBindToGameMonitor();
                    if (g_adlOK) AdlBindToGameMonitor();
                }
                if (g_color && !colorfx::g_hooked && !colorfx::g_failed) { colorfx::Install(g_hMod); RequestRedraw(); }
                colorfx::g_amount = g_color ? (float)g_colorAmt / 100.f : 0.f;
            }
            // (wait until the resolution slider has stopped moving before switching the monitor)
            if ((GameFocused() || !g_stretch) && Qpc() - g_stretchChangedQpc > Ms(600)) UpdateStretchDisplay();
            static int tick;
            if (++tick % 50 == 0 && LoadGameBinds(false)) RequestRedraw();   // you changed binds in game
            HWND g = g_game;
            if (!g || !IsWindow(g)) { HWND n = FindGameWindow(); if (n) { g_game = n; InstallMsgHook(); } }
            else if (GetWindowThreadProcessId(g, nullptr) != g_gameTid) InstallMsgHook();
            bool focused = GameFocused();
            if (!focused) {
                if (IsWindowVisible(h)) { ShowWindow(h, SW_HIDE); g_alpha = 0; }
            } else if (g_menuOpen) {
                PlaceOverlay();
                if (!IsWindowVisible(h)) { g_alpha = 0; ShowWindow(h, SW_SHOWNOACTIVATE); SetTimer(h, TIMER_FADE, 12, nullptr); }
            }
            return 0;
        }
        if (wp == TIMER_CHECK) { Redraw(); if (!AnyCheckAnimating()) KillTimer(h, TIMER_CHECK); return 0; }
        if (wp == TIMER_FADE) {
            int target = g_menuOpen ? 255 : 0;
            g_alpha += g_menuOpen ? 64 : -64;
            if ((g_menuOpen && g_alpha >= target) || (!g_menuOpen && g_alpha <= target)) {
                g_alpha = target; KillTimer(h, TIMER_FADE);
            }
            if (g_alpha == 0 && !g_menuOpen) { ShowWindow(h, SW_HIDE); return 0; }
            Present();
            return 0;
        }
        break;
    }
    return DefWindowProcW(h, msg, wp, lp);
}

// ---------------------------------------------------------------------
//  Entry
// ---------------------------------------------------------------------
static DWORD WINAPI CloverMain(LPVOID) {
    LARGE_INTEGER f; QueryPerformanceFrequency(&f); g_qpf = f.QuadPart;
    LoadSettings();
    AddVectoredExceptionHandler(1, GuardVeh);
    colorfx::g_log = [](const char* m, LONG_PTR v) { Log(m, v); };

    while (!(g_game = FindGameWindow())) Sleep(250);
    LoadGameBinds(true);
    LoadUserResolution();

    WNDCLASSEXW wc = {};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = OverlayProc;
    wc.hInstance = g_hMod;
    wc.hCursor = LoadCursorW(nullptr, (LPCWSTR)IDC_ARROW);
    wc.lpszClassName = L"CloverOverlay";
    RegisterClassExW(&wc);
    g_overlay = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
                                wc.lpszClassName, L"Clover", WS_POPUP,
                                0, 0, SURF_W, SURF_H, nullptr, nullptr, g_hMod, nullptr);
    if (!g_overlay) return 1;
    CreateCanvas();

    g_confirmEvent = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    HANDLE t1 = CreateThread(nullptr, 0, ConfirmThread, nullptr, 0, nullptr); if (t1) CloseHandle(t1);
    HANDLE t2 = CreateThread(nullptr, 0, EngineThread, nullptr, 0, nullptr);  if (t2) CloseHandle(t2);
    HANDLE t3 = CreateThread(nullptr, 0, FpsThread, nullptr, 0, nullptr);     if (t3) CloseHandle(t3);

    InstallMsgHook();
    SetTimer(g_overlay, TIMER_TRACK, 100, nullptr);

    MSG m;
    while (GetMessageW(&m, nullptr, 0, 0) > 0) { TranslateMessage(&m); DispatchMessageW(&m); }
    return 0;
}

extern "C" BOOL WINAPI DllMain(HINSTANCE inst, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_DETACH) {
        if (g_dispApplied >= 0 && g_dispDev[0]) ChangeDisplaySettingsExW(g_dispDev, nullptr, nullptr, 0, nullptr);
        if (g_nvOK && g_nvHandle && g_nvApplied > 0) g_nvSet(g_nvHandle, g_nvOut, g_nvOrig);
        if (g_adlOK && g_adlDisplay >= 0 && g_adlApplied > 0) g_adlSet(g_adl, g_adlAdapter, g_adlDisplay, ADL_COLOR_SATURATION, g_adlOrig);
    }
    if (reason == DLL_PROCESS_ATTACH) {
        g_hMod = inst;
        DisableThreadLibraryCalls(inst);
        HANDLE t = CreateThread(nullptr, 0, CloverMain, nullptr, 0, nullptr);
        if (t) CloseHandle(t);
    }
    return TRUE;
}
