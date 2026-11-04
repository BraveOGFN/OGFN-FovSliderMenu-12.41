// ---------------------------------------------------------------------
//  Reads your Fortnite keybinds straight from the game's settings save
//  (%LOCALAPPDATA%\FortniteGame\Saved\Cloud\<account>\ClientSettings.Sav).
//  The file is "ECFD" + zlib; this is a tiny self-contained inflate + a
//  scan for the bind records. No Windows calls in here (portable/testable).
// ---------------------------------------------------------------------
#pragma once

namespace binds {

typedef unsigned char  u8;
typedef unsigned short u16;
typedef unsigned int   u32;

// ---------------- inflate (RFC 1951) ----------------
struct Inf {
    const u8* src; const u8* end;
    u32 bitbuf; int bitcnt;
    u8* out; u32 pos, cap;
    bool err;
};
struct Huff { u16 count[16]; u16 symbol[320]; };

static int bits(Inf* s, int need) {
    u32 val = s->bitbuf;
    while (s->bitcnt < need) {
        if (s->src >= s->end) { s->err = true; return 0; }
        val |= (u32)(*s->src++) << s->bitcnt;
        s->bitcnt += 8;
    }
    s->bitbuf = val >> need;
    s->bitcnt -= need;
    return (int)(val & ((1u << need) - 1));
}

static void build(Huff* h, const u8* len, int n) {
    u16 offs[16];
    for (int i = 0; i < 16; ++i) h->count[i] = 0;
    for (int i = 0; i < n; ++i) h->count[len[i]]++;
    offs[1] = 0;
    for (int i = 1; i < 15; ++i) offs[i + 1] = offs[i] + h->count[i];
    for (int i = 0; i < n; ++i) if (len[i]) h->symbol[offs[len[i]]++] = (u16)i;
}

static int decode(Inf* s, const Huff* h) {
    int code = 0, first = 0, index = 0;
    for (int len = 1; len < 16; ++len) {
        code |= bits(s, 1);
        if (s->err) return -1;
        int count = h->count[len];
        if (code - count < first) return h->symbol[index + (code - first)];
        index += count; first += count;
        first <<= 1; code <<= 1;
    }
    s->err = true;
    return -1;
}

static const u16 LBASE[29] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258};
static const u8  LEXT[29]  = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0};
static const u16 DBASE[30] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577};
static const u8  DEXT[30]  = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13};

static bool codes(Inf* s, const Huff* lc, const Huff* dc) {
    for (;;) {
        int sym = decode(s, lc);
        if (sym < 0) return false;
        if (sym < 256) {
            if (s->pos >= s->cap) return false;
            s->out[s->pos++] = (u8)sym;
        } else if (sym == 256) {
            return true;
        } else {
            sym -= 257;
            if (sym >= 29) return false;
            int len = LBASE[sym] + bits(s, LEXT[sym]);
            int ds = decode(s, dc);
            if (ds < 0 || ds >= 30) return false;
            u32 dist = DBASE[ds] + bits(s, DEXT[ds]);
            if (s->err || dist > s->pos || s->pos + len > s->cap) return false;
            for (int i = 0; i < len; ++i) { s->out[s->pos] = s->out[s->pos - dist]; ++s->pos; }
        }
    }
}

// Raw deflate -> out. Returns bytes written, or 0 on error.
static u32 Inflate(const u8* src, u32 srcLen, u8* out, u32 cap) {
    Inf s = { src, src + srcLen, 0, 0, out, 0, cap, false };
    static Huff lc, dc;   // engine thread only
    int last;
    do {
        last = bits(&s, 1);
        int type = bits(&s, 2);
        if (s.err) return 0;
        if (type == 0) {                                   // stored
            s.bitbuf = 0; s.bitcnt = 0;
            if (s.end - s.src < 4) return 0;
            u32 len = s.src[0] | (s.src[1] << 8);
            s.src += 4;
            if ((u32)(s.end - s.src) < len || s.pos + len > s.cap) return 0;
            for (u32 i = 0; i < len; ++i) s.out[s.pos++] = *s.src++;
        } else if (type == 1) {                            // fixed
            u8 l[320];
            int i = 0;
            for (; i < 144; ++i) l[i] = 8;
            for (; i < 256; ++i) l[i] = 9;
            for (; i < 280; ++i) l[i] = 7;
            for (; i < 288; ++i) l[i] = 8;
            build(&lc, l, 288);
            for (i = 0; i < 30; ++i) l[i] = 5;
            build(&dc, l, 30);
            if (!codes(&s, &lc, &dc)) return 0;
        } else if (type == 2) {                            // dynamic
            static const u8 order[19] = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
            int nlen = bits(&s, 5) + 257, ndist = bits(&s, 5) + 1, ncode = bits(&s, 4) + 4;
            if (s.err || nlen > 286 || ndist > 30) return 0;
            u8 l[320];
            for (int i = 0; i < 19; ++i) l[i] = 0;
            for (int i = 0; i < ncode; ++i) l[order[i]] = (u8)bits(&s, 3);
            build(&lc, l, 19);
            int idx = 0;
            while (idx < nlen + ndist) {
                int sym = decode(&s, &lc);
                if (sym < 0) return 0;
                if (sym < 16) { l[idx++] = (u8)sym; continue; }
                int rep, val = 0;
                if (sym == 16) { if (!idx) return 0; val = l[idx - 1]; rep = 3 + bits(&s, 2); }
                else if (sym == 17) rep = 3 + bits(&s, 3);
                else rep = 11 + bits(&s, 7);
                if (idx + rep > nlen + ndist) return 0;
                while (rep--) l[idx++] = (u8)val;
            }
            build(&lc, l, nlen);
            build(&dc, l + nlen, ndist);
            if (!codes(&s, &lc, &dc)) return 0;
        } else return 0;
    } while (!last);
    return s.pos;
}

// ---------------- bind records ----------------
static int slen(const char* s) { int n = 0; while (s[n]) ++n; return n; }

static const u8* findBytes(const u8* p, const u8* end, const char* needle) {
    int n = slen(needle);
    for (; p + n <= end; ++p) {
        int i = 0; while (i < n && p[i] == (u8)needle[i]) ++i;
        if (i == n) return p;
    }
    return nullptr;
}

// Reads the FString value of the next "NameProperty" after p.
static bool readName(const u8* p, const u8* end, char* out, int cap) {
    const u8* np = findBytes(p, end, "NameProperty");
    if (!np) return false;
    np += 13;                                   // "NameProperty\0"
    np += 8 + 1;                                // size, index, guid flag
    if (np + 4 > end) return false;
    int len = np[0] | (np[1] << 8) | (np[2] << 16) | (np[3] << 24);
    np += 4;
    if (len <= 0 || len > 64 || np + len > end) return false;
    int i = 0;
    for (; i < len - 1 && i < cap - 1; ++i) out[i] = (char)np[i];
    out[i] = 0;
    return true;
}

// Finds an action's key ("F", "MouseScrollDown", ...). Prefers KeyBind1, falls back to KeyBind2.
static bool FindBind(const u8* data, u32 size, const char* action, char* out, int cap) {
    const u8* end = data + size;
    int alen = slen(action);
    for (const u8* p = data; (p = findBytes(p, end, action)) != nullptr; p += alen) {
        if (p + alen >= end || p[alen] != 0) continue;           // whole-string match
        if (p >= data + 4) {                                      // must be an FString value
            int l = p[-4] | (p[-3] << 8);
            if (l != alen + 1) continue;
        }
        const u8* kb1 = findBytes(p, end, "KeyBind1");
        const u8* kb2 = findBytes(p, end, "KeyBind2");
        const u8* nextAction = findBytes(p + alen, end, "ActionName");
        if (!kb1 || (nextAction && kb1 > nextAction)) continue;
        char k[64];
        if (readName(kb1, end, k, 64) && !(k[0] == 'N' && k[1] == 'o' && k[2] == 'n' && k[3] == 'e' && !k[4])) {
            for (int i = 0; i < cap; ++i) { out[i] = k[i]; if (!k[i]) break; }
            return true;
        }
        if (kb2 && (!nextAction || kb2 < nextAction) && readName(kb2, end, k, 64) &&
            !(k[0] == 'N' && k[1] == 'o' && k[2] == 'n' && k[3] == 'e' && !k[4])) {
            for (int i = 0; i < cap; ++i) { out[i] = k[i]; if (!k[i]) break; }
            return true;
        }
    }
    return false;
}

// UE key name -> Windows virtual key (0x0E/0x0F = scroll up/down).
static unsigned KeyToVk(const char* k) {
    int n = slen(k);
    if (n == 1) {
        char c = k[0];
        if (c >= 'A' && c <= 'Z') return (unsigned)c;
        if (c >= 'a' && c <= 'z') return (unsigned)(c - 32);
    }
    if (k[0] == 'F' && n >= 2 && n <= 3 && k[1] >= '1' && k[1] <= '9') {
        int f = k[1] - '0'; if (n == 3) f = f * 10 + (k[2] - '0');
        if (f >= 1 && f <= 24) return 0x70 + f - 1;
    }
    struct { const char* name; unsigned vk; } t[] = {
        {"LeftMouseButton",1},{"RightMouseButton",2},{"MiddleMouseButton",4},
        {"ThumbMouseButton",5},{"ThumbMouseButton2",6},
        {"MouseScrollUp",0x0E},{"MouseScrollDown",0x0F},
        {"Zero",'0'},{"One",'1'},{"Two",'2'},{"Three",'3'},{"Four",'4'},
        {"Five",'5'},{"Six",'6'},{"Seven",'7'},{"Eight",'8'},{"Nine",'9'},
        {"SpaceBar",0x20},{"Tab",0x09},{"Enter",0x0D},{"Escape",0x1B},{"BackSpace",0x08},
        {"CapsLock",0x14},{"LeftShift",0x10},{"RightShift",0x10},{"LeftControl",0x11},
        {"RightControl",0x11},{"LeftAlt",0x12},{"RightAlt",0x12},
        {"Insert",0x2D},{"Delete",0x2E},{"Home",0x24},{"End",0x23},{"PageUp",0x21},{"PageDown",0x22},
        {"Left",0x25},{"Up",0x26},{"Right",0x27},{"Down",0x28},
        {"Semicolon",0xBA},{"Equals",0xBB},{"Comma",0xBC},{"Hyphen",0xBD},{"Period",0xBE},
        {"Slash",0xBF},{"Tilde",0xC0},{"LeftBracket",0xDB},{"Backslash",0xDC},
        {"RightBracket",0xDD},{"Apostrophe",0xDE},
        {"NumPadZero",0x60},{"NumPadOne",0x61},{"NumPadTwo",0x62},{"NumPadThree",0x63},
        {"NumPadFour",0x64},{"NumPadFive",0x65},{"NumPadSix",0x66},{"NumPadSeven",0x67},
        {"NumPadEight",0x68},{"NumPadNine",0x69},
    };
    for (auto& e : t) {
        int i = 0; while (e.name[i] && e.name[i] == k[i]) ++i;
        if (!e.name[i] && !k[i]) return e.vk;
    }
    return 0;
}

// Full pipeline on the raw file bytes. Returns false if the file can't be parsed.
// work must hold the decompressed data (size is stored in the header at +12).
static u32 DecompressedSize(const u8* file, u32 size) {
    if (size < 18 || file[0] != 'E' || file[1] != 'C' || file[2] != 'F' || file[3] != 'D') return 0;
    return file[12] | (file[13] << 8) | (file[14] << 16) | ((u32)file[15] << 24);
}
static u32 Decompress(const u8* file, u32 size, u8* work, u32 cap) {
    // zlib stream right after the 16-byte header: skip its 2-byte header
    for (u32 i = 16; i + 2 < size && i < 64; ++i)
        if (file[i] == 0x78 && (file[i + 1] == 0x01 || file[i + 1] == 0x5E || file[i + 1] == 0x9C || file[i + 1] == 0xDA))
            return Inflate(file + i + 2, size - i - 2, work, cap);
    return 0;
}

} // namespace binds
