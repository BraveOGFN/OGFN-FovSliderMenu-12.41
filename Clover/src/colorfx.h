// ---------------------------------------------------------------------
//  Color Booster (in-game): adds vibrance to Fortnite's own picture right
//  before it is shown (DirectX 11 Present). Only Fortnite is affected -
//  your desktop and other apps never change - and it works on any GPU.
// ---------------------------------------------------------------------
#pragma once
#include <d3d11.h>
#include <dxgi1_2.h>
#include <d3dcompiler.h>

namespace colorfx {

typedef HRESULT (STDMETHODCALLTYPE* Present_t)(IDXGISwapChain*, UINT, UINT);
typedef HRESULT (STDMETHODCALLTYPE* Present1_t)(IDXGISwapChain1*, UINT, UINT, const DXGI_PRESENT_PARAMETERS*);
typedef HRESULT (WINAPI* CreateDevSwap_t)(IDXGIAdapter*, D3D_DRIVER_TYPE, HMODULE, UINT, const D3D_FEATURE_LEVEL*, UINT, UINT,
                                          const DXGI_SWAP_CHAIN_DESC*, IDXGISwapChain**, ID3D11Device**, D3D_FEATURE_LEVEL*, ID3D11DeviceContext**);
typedef HRESULT (WINAPI* Compile_t)(LPCVOID, SIZE_T, LPCSTR, const D3D_SHADER_MACRO*, ID3DInclude*, LPCSTR, LPCSTR, UINT, UINT, ID3DBlob**, ID3DBlob**);

static Present_t  g_origPresent;
static Present1_t g_origPresent1;
static volatile float g_amount;        // 0 = off, up to ~1
static volatile bool  g_failed;        // gave up (logged once), never touches rendering again
static volatile bool  g_hooked;
static void (*g_log)(const char*, LONG_PTR);

// GPU objects (render thread only)
static ID3D11Device*          g_dev;
static ID3D11VertexShader*    g_vs;
static ID3D11PixelShader*     g_ps;
static ID3D11Buffer*          g_cb;
static ID3D11RasterizerState* g_rs;
static ID3D11BlendState*      g_bs;
static ID3D11DepthStencilState* g_ds;
static ID3D11Texture2D*       g_copy;
static ID3D11ShaderResourceView* g_copySrv;
static UINT g_copyW, g_copyH; static DXGI_FORMAT g_copyFmt;

static const char* SHADER =
    "cbuffer C : register(b0) { float amount; float3 pad; };\n"
    "Texture2D src : register(t0);\n"
    "float4 VS(uint id : SV_VertexID) : SV_Position {\n"
    "  float2 uv = float2((id << 1) & 2, id & 2);\n"
    "  return float4(uv * float2(2, -2) + float2(-1, 1), 0, 1);\n"
    "}\n"
    "float4 PS(float4 pos : SV_Position) : SV_Target {\n"
    "  float4 c = src.Load(int3(pos.xy, 0));\n"
    "  float l = dot(c.rgb, float3(0.299, 0.587, 0.114));\n"
    "  float sat = max(c.r, max(c.g, c.b)) - min(c.r, min(c.g, c.b));\n"
    "  float k = 1.0 + amount * (1.15 - 0.6 * sat);\n"   // vibrance: dull colours get more, already-strong ones less
    "  return float4(saturate(lerp(l.xxx, c.rgb, k)), c.a);\n"
    "}\n";

static DXGI_FORMAT Typed(DXGI_FORMAT f) {
    switch (f) {
    case DXGI_FORMAT_R8G8B8A8_TYPELESS:    return DXGI_FORMAT_R8G8B8A8_UNORM;
    case DXGI_FORMAT_B8G8R8A8_TYPELESS:    return DXGI_FORMAT_B8G8R8A8_UNORM;
    case DXGI_FORMAT_R10G10B10A2_TYPELESS: return DXGI_FORMAT_R10G10B10A2_UNORM;
    case DXGI_FORMAT_R16G16B16A16_TYPELESS:return DXGI_FORMAT_R16G16B16A16_FLOAT;
    default: return f;
    }
}

static void Fail(const char* why) { if (!g_failed && g_log) g_log(why, -1); g_failed = true; }

static bool InitGpu(ID3D11Device* dev) {
    HMODULE dc = LoadLibraryW(L"d3dcompiler_47.dll");
    Compile_t compile = dc ? (Compile_t)GetProcAddress(dc, "D3DCompile") : nullptr;
    if (!compile) { Fail("color booster: d3dcompiler_47.dll missing"); return false; }
    ID3DBlob *vsb = nullptr, *psb = nullptr, *err = nullptr;
    SIZE_T n = 0; while (SHADER[n]) ++n;
    if (FAILED(compile(SHADER, n, "clover", nullptr, nullptr, "VS", "vs_4_0", 0, 0, &vsb, &err)) ||
        FAILED(compile(SHADER, n, "clover", nullptr, nullptr, "PS", "ps_4_0", 0, 0, &psb, &err))) {
        if (err) err->Release();
        Fail("color booster: shader compile failed"); return false;
    }
    bool ok = SUCCEEDED(dev->CreateVertexShader(vsb->GetBufferPointer(), vsb->GetBufferSize(), nullptr, &g_vs)) &&
              SUCCEEDED(dev->CreatePixelShader(psb->GetBufferPointer(), psb->GetBufferSize(), nullptr, &g_ps));
    vsb->Release(); psb->Release();
    if (!ok) { Fail("color booster: shader create failed"); return false; }

    D3D11_BUFFER_DESC bd = {}; bd.ByteWidth = 16; bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_CONSTANT_BUFFER; bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    D3D11_RASTERIZER_DESC rd = {}; rd.FillMode = D3D11_FILL_SOLID; rd.CullMode = D3D11_CULL_NONE; rd.DepthClipEnable = TRUE;
    D3D11_BLEND_DESC bld = {}; bld.RenderTarget[0].RenderTargetWriteMask = D3D11_COLOR_WRITE_ENABLE_ALL;
    D3D11_DEPTH_STENCIL_DESC dsd = {}; dsd.DepthEnable = FALSE; dsd.StencilEnable = FALSE;
    if (FAILED(dev->CreateBuffer(&bd, nullptr, &g_cb)) || FAILED(dev->CreateRasterizerState(&rd, &g_rs)) ||
        FAILED(dev->CreateBlendState(&bld, &g_bs)) || FAILED(dev->CreateDepthStencilState(&dsd, &g_ds))) {
        Fail("color booster: state create failed"); return false;
    }
    g_dev = dev;
    if (g_log) g_log("color booster: in-game shader ready", -1);
    return true;
}

// Saves exactly what we touch and puts it back, so the game's renderer never notices.
struct SavedState {
    ID3D11RenderTargetView* rtv[D3D11_SIMULTANEOUS_RENDER_TARGET_COUNT]; ID3D11DepthStencilView* dsv;
    D3D11_VIEWPORT vp[16]; UINT nvp;
    ID3D11RasterizerState* rs; ID3D11BlendState* bs; FLOAT bf[4]; UINT mask; ID3D11DepthStencilState* ds; UINT sref;
    ID3D11InputLayout* il; D3D11_PRIMITIVE_TOPOLOGY topo;
    ID3D11VertexShader* vs; ID3D11PixelShader* ps; ID3D11GeometryShader* gs; ID3D11HullShader* hs; ID3D11DomainShader* dsh;
    ID3D11ClassInstance *vsci[256], *psci[256], *gsci[256], *hsci[256], *dsci[256]; UINT nvsci, npsci, ngsci, nhsci, ndsci;
    ID3D11ShaderResourceView* srv; ID3D11Buffer* cb;
};
static SavedState g_st;

static void Save(ID3D11DeviceContext* c) {
    SavedState& s = g_st;
    c->OMGetRenderTargets(D3D11_SIMULTANEOUS_RENDER_TARGET_COUNT, s.rtv, &s.dsv);
    s.nvp = 16; c->RSGetViewports(&s.nvp, s.vp);
    c->RSGetState(&s.rs); c->OMGetBlendState(&s.bs, s.bf, &s.mask); c->OMGetDepthStencilState(&s.ds, &s.sref);
    c->IAGetInputLayout(&s.il); c->IAGetPrimitiveTopology(&s.topo);
    s.nvsci = s.npsci = s.ngsci = s.nhsci = s.ndsci = 256;
    c->VSGetShader(&s.vs, s.vsci, &s.nvsci); c->PSGetShader(&s.ps, s.psci, &s.npsci);
    c->GSGetShader(&s.gs, s.gsci, &s.ngsci); c->HSGetShader(&s.hs, s.hsci, &s.nhsci); c->DSGetShader(&s.dsh, s.dsci, &s.ndsci);
    c->PSGetShaderResources(0, 1, &s.srv); c->PSGetConstantBuffers(0, 1, &s.cb);
}
template <class T> static void Rel(T*& p) { if (p) { p->Release(); p = nullptr; } }
static void RelArr(ID3D11ClassInstance** a, UINT n) { for (UINT i = 0; i < n && i < 256; ++i) Rel(a[i]); }
static void Restore(ID3D11DeviceContext* c) {
    SavedState& s = g_st;
    c->OMSetRenderTargets(D3D11_SIMULTANEOUS_RENDER_TARGET_COUNT, s.rtv, s.dsv);
    c->RSSetViewports(s.nvp, s.vp); c->RSSetState(s.rs); c->OMSetBlendState(s.bs, s.bf, s.mask);
    c->OMSetDepthStencilState(s.ds, s.sref); c->IASetInputLayout(s.il); c->IASetPrimitiveTopology(s.topo);
    c->VSSetShader(s.vs, s.vsci, s.nvsci); c->PSSetShader(s.ps, s.psci, s.npsci);
    c->GSSetShader(s.gs, s.gsci, s.ngsci); c->HSSetShader(s.hs, s.hsci, s.nhsci); c->DSSetShader(s.dsh, s.dsci, s.ndsci);
    c->PSSetShaderResources(0, 1, &s.srv); c->PSSetConstantBuffers(0, 1, &s.cb);
    for (int i = 0; i < D3D11_SIMULTANEOUS_RENDER_TARGET_COUNT; ++i) Rel(s.rtv[i]);
    Rel(s.dsv); Rel(s.rs); Rel(s.bs); Rel(s.ds); Rel(s.il); Rel(s.vs); Rel(s.ps); Rel(s.gs); Rel(s.hs); Rel(s.dsh);
    RelArr(s.vsci, s.nvsci); RelArr(s.psci, s.npsci); RelArr(s.gsci, s.ngsci); RelArr(s.hsci, s.nhsci); RelArr(s.dsci, s.ndsci);
    Rel(s.srv); Rel(s.cb);
}

static void Apply(IDXGISwapChain* sc) {
    float amount = g_amount;
    if (amount <= 0.f || g_failed) return;
    ID3D11Device* dev = nullptr;
    if (FAILED(sc->GetDevice(__uuidof(ID3D11Device), (void**)&dev)) || !dev) return;   // not a D3D11 swapchain
    if (!g_dev && !InitGpu(dev)) { dev->Release(); return; }
    if (dev != g_dev) { dev->Release(); return; }                                    // some other device: leave it
    ID3D11Texture2D* bb = nullptr;
    if (FAILED(sc->GetBuffer(0, __uuidof(ID3D11Texture2D), (void**)&bb)) || !bb) { dev->Release(); return; }
    D3D11_TEXTURE2D_DESC d; bb->GetDesc(&d);
    if (d.SampleDesc.Count != 1) { bb->Release(); dev->Release(); return; }
    DXGI_FORMAT fmt = Typed(d.Format);

    if (!g_copy || g_copyW != d.Width || g_copyH != d.Height || g_copyFmt != d.Format) {
        Rel(g_copySrv); Rel(g_copy);
        D3D11_TEXTURE2D_DESC cd = d; cd.BindFlags = D3D11_BIND_SHADER_RESOURCE; cd.Usage = D3D11_USAGE_DEFAULT;
        cd.CPUAccessFlags = 0; cd.MiscFlags = 0; cd.MipLevels = 1; cd.ArraySize = 1;
        D3D11_SHADER_RESOURCE_VIEW_DESC sd = {}; sd.Format = fmt; sd.ViewDimension = D3D11_SRV_DIMENSION_TEXTURE2D; sd.Texture2D.MipLevels = 1;
        if (FAILED(dev->CreateTexture2D(&cd, nullptr, &g_copy)) || FAILED(dev->CreateShaderResourceView(g_copy, &sd, &g_copySrv))) {
            Rel(g_copySrv); Rel(g_copy); bb->Release(); dev->Release(); Fail("color booster: copy texture failed"); return;
        }
        g_copyW = d.Width; g_copyH = d.Height; g_copyFmt = d.Format;
    }
    ID3D11RenderTargetView* rtv = nullptr;
    D3D11_RENDER_TARGET_VIEW_DESC rd = {}; rd.Format = fmt; rd.ViewDimension = D3D11_RTV_DIMENSION_TEXTURE2D;
    if (FAILED(dev->CreateRenderTargetView(bb, &rd, &rtv))) { bb->Release(); dev->Release(); Fail("color booster: render target failed"); return; }

    ID3D11DeviceContext* ctx = nullptr; dev->GetImmediateContext(&ctx);
    Save(ctx);
    ctx->CopyResource(g_copy, bb);
    D3D11_MAPPED_SUBRESOURCE m;
    if (SUCCEEDED(ctx->Map(g_cb, 0, D3D11_MAP_WRITE_DISCARD, 0, &m))) { float* f = (float*)m.pData; f[0] = amount; f[1] = f[2] = f[3] = 0; ctx->Unmap(g_cb, 0); }
    D3D11_VIEWPORT vp = { 0, 0, (FLOAT)d.Width, (FLOAT)d.Height, 0, 1 };
    ctx->OMSetRenderTargets(1, &rtv, nullptr);
    ctx->RSSetViewports(1, &vp); ctx->RSSetState(g_rs);
    FLOAT bf[4] = { 0, 0, 0, 0 }; ctx->OMSetBlendState(g_bs, bf, 0xFFFFFFFF); ctx->OMSetDepthStencilState(g_ds, 0);
    ctx->IASetInputLayout(nullptr); ctx->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_TRIANGLELIST);
    ctx->VSSetShader(g_vs, nullptr, 0); ctx->PSSetShader(g_ps, nullptr, 0);
    ctx->GSSetShader(nullptr, nullptr, 0); ctx->HSSetShader(nullptr, nullptr, 0); ctx->DSSetShader(nullptr, nullptr, 0);
    ctx->PSSetShaderResources(0, 1, &g_copySrv); ctx->PSSetConstantBuffers(0, 1, &g_cb);
    ctx->Draw(3, 0);
    ID3D11ShaderResourceView* nullSrv = nullptr; ctx->PSSetShaderResources(0, 1, &nullSrv);
    Restore(ctx);
    ctx->Release(); rtv->Release(); bb->Release(); dev->Release();
}

static HRESULT STDMETHODCALLTYPE HookPresent(IDXGISwapChain* sc, UINT sync, UINT flags) {
    if (!(flags & DXGI_PRESENT_TEST)) Apply(sc);
    return g_origPresent(sc, sync, flags);
}
static HRESULT STDMETHODCALLTYPE HookPresent1(IDXGISwapChain1* sc, UINT sync, UINT flags, const DXGI_PRESENT_PARAMETERS* p) {
    if (!(flags & DXGI_PRESENT_TEST)) Apply(sc);
    return g_origPresent1(sc, sync, flags, p);
}

static bool PatchSlot(void** vt, int idx, void* fn, void** orig) {
    DWORD old;
    if (!VirtualProtect(&vt[idx], sizeof(void*), PAGE_READWRITE, &old)) return false;
    *orig = vt[idx]; vt[idx] = fn;
    VirtualProtect(&vt[idx], sizeof(void*), old, &old);
    return true;
}

// Finds DXGI's swapchain vtable with a throwaway device on a hidden window and hooks Present.
static bool Install(HINSTANCE inst) {
    if (g_hooked) return true;
    HMODULE d3d = LoadLibraryW(L"d3d11.dll");
    CreateDevSwap_t create = d3d ? (CreateDevSwap_t)GetProcAddress(d3d, "D3D11CreateDeviceAndSwapChain") : nullptr;
    if (!create) { Fail("color booster: d3d11.dll not found"); return false; }
    WNDCLASSEXW wc = {}; wc.cbSize = sizeof(wc); wc.lpfnWndProc = DefWindowProcW; wc.hInstance = inst; wc.lpszClassName = L"CloverDxProbe";
    RegisterClassExW(&wc);
    HWND w = CreateWindowExW(0, wc.lpszClassName, L"", WS_OVERLAPPED, 0, 0, 16, 16, nullptr, nullptr, inst, nullptr);
    DXGI_SWAP_CHAIN_DESC sd = {};
    sd.BufferCount = 1; sd.BufferDesc.Width = 16; sd.BufferDesc.Height = 16; sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT; sd.OutputWindow = w; sd.SampleDesc.Count = 1; sd.Windowed = TRUE;
    IDXGISwapChain* sc = nullptr; ID3D11Device* dev = nullptr; ID3D11DeviceContext* ctx = nullptr;
    HRESULT hr = create(nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr, 0, nullptr, 0, D3D11_SDK_VERSION, &sd, &sc, &dev, nullptr, &ctx);
    if (FAILED(hr) || !sc) { if (w) DestroyWindow(w); Fail("color booster: probe device failed"); return false; }
    void** vt = *(void***)sc;
    bool ok = PatchSlot(vt, 8, (void*)HookPresent, (void**)&g_origPresent);
    IDXGISwapChain1* sc1 = nullptr;
    if (SUCCEEDED(sc->QueryInterface(__uuidof(IDXGISwapChain1), (void**)&sc1)) && sc1) {
        void** vt1 = *(void***)sc1;
        PatchSlot(vt1, 22, (void*)HookPresent1, (void**)&g_origPresent1);
        sc1->Release();
    }
    sc->Release(); ctx->Release(); dev->Release(); DestroyWindow(w);
    g_hooked = ok;
    if (g_log) g_log(ok ? "color booster: hooked into the game's frames" : "color booster: hook failed", -1);
    return ok;
}

} // namespace colorfx
