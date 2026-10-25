# -*- coding: utf-8 -*-
"""A4 one-page poster (300dpi): Agent + Lean 4 formalization of Euclid's theorem."""
from PIL import Image, ImageDraw, ImageFont, ImageFilter
import numpy as np

W, H = 2480, 3508
S = W / 794.0
FONTDIR = "C:/Windows/Fonts/"

def s(v):
    return v * S

FONTS = {
    "cn": ("msyh.ttc", 0), "cnb": ("msyhbd.ttc", 0), "cnl": ("msyhl.ttc", 0),
    "mono": ("consola.ttf", 0), "monb": ("consolab.ttf", 0), "moni": ("consolai.ttf", 0),
    "sym": ("seguisym.ttf", 0),
}
_c = {}
def F(kind, size):
    key = (kind, int(size))
    if key not in _c:
        fn, idx = FONTS[kind]
        _c[key] = ImageFont.truetype(FONTDIR + fn, int(size), index=idx)
    return _c[key]

SYMS = set("∃∀ℕ∣∧⟨⟩⟹⊆¬≤≠→∈✓∄⇔ℤℝ")
def kind_of(ch, primary):
    if ch in SYMS:
        return "sym"
    if ord(ch) >= 0x2E80 and primary in ("mono", "monb", "moni"):
        return "cn"
    return primary

def runsof(txt, primary):
    out = []
    for ch in txt:
        k = kind_of(ch, primary)
        if out and out[-1][1] == k:
            out[-1][0].append(ch)
        else:
            out.append(([ch], k))
    return [("".join(c), k) for c, k in out]

def tw(txt, primary, size, tracking=0.0):
    w = 0.0
    for t, k in runsof(txt, primary):
        w += F(k, size).getlength(t) + tracking * len(t)
    return w

def text(d, xy, txt, primary, size, fill, tracking=0.0, align="left"):
    x, y = xy
    if align != "left":
        w = tw(txt, primary, size, tracking)
        x = x - w if align == "right" else x - w / 2
    asc = F(primary, size).getmetrics()[0]
    for t, k in runsof(txt, primary):
        f = F(k, size)
        d.text((x, y), t, font=f, fill=fill, anchor="ls")
        x += f.getlength(t) + tracking * len(t)
    return x

def wrap(txt, primary, size, maxw, tracking=0.0):
    lines, cur = [], ""
    for ch in txt:
        cand = cur + ch
        if tw(cand, primary, size, tracking) > maxw and cur:
            cut = cur.rfind(" ") if (ch.isascii() and ch != " ") else -1
            if cut > len(cur) * 0.45:
                lines.append(cur[:cut]); cur = cur[cut + 1:] + ch; continue
            lines.append(cur); cur = ch
        else:
            cur = cand
    lines.append(cur)
    return lines

def para(d, x, ybase, txt, primary, size, fill, maxw, lh, tracking=0.0):
    for ln in wrap(txt, primary, size, maxw, tracking):
        text(d, (x, ybase), ln, primary, size, fill, tracking)
        ybase += lh
    return ybase - lh

def shadow(img, box, r, blur=14, alpha=26, dy=8):
    lay = Image.new("L", (W, H), 0)
    ImageDraw.Draw(lay).rounded_rectangle(
        (box[0], box[1] + dy, box[2], box[3] + dy), radius=r, fill=alpha)
    img.paste(Image.new("RGB", (W, H), (15, 23, 42)), (0, 0),
              lay.filter(ImageFilter.GaussianBlur(blur)))

INK, MUTED, FAINT = (15, 23, 42), (71, 85, 105), (148, 163, 184)
TEAL, TEAL_L, LINE, WHITE = (15, 118, 110), (231, 243, 242), (226, 232, 240), (255, 255, 255)
AMBER, FAINT2 = (180, 83, 9), (203, 213, 225)

MG = s(34)
CW = W - 2 * MG
x0 = MG
TARGET_END = H - s(48)

def background():
    yy = np.linspace(0, 1, H)[:, None]
    top, bot = np.array([252, 253, 254]), np.array([237, 241, 245])
    grad = (top + (bot - top) * (yy ** 1.05)).astype(np.uint8)
    bg = np.repeat(grad, W, axis=1).reshape(H, W, 3)
    im = Image.fromarray(bg, "RGB")
    gx_, gy_ = np.meshgrid(np.arange(W), np.arange(H))
    rad = np.sqrt(((gx_ - W * 1.02) / (W * 0.95)) ** 2 + ((gy_ + H * 0.05) / (H * 0.42)) ** 2)
    glow = np.clip(1 - rad, 0, 1) ** 1.4
    ov = Image.new("RGB", (W, H), (206, 226, 227))
    return Image.composite(ov, im, Image.fromarray((glow * 158).astype(np.uint8)))

CODE = [
    [("import", "kw"), (" Mathlib", "pl")], [],
    [("/-- 对任意 n，存在素数 p > n（Euclid） -/", "cm")],
    [("theorem ", "kw"), ("exists_prime_gt", "ty"), (" (n : ℕ) : ∃ p, p.Prime ∧ n < p ", "pl"), (":= by", "kw")],
    [("  obtain ", "kw"), ("⟨p, hp, hdvd⟩ ", "pl"), (":=", "kw")],
    [("    Nat.exists_prime_and_dvd (", "pl"), ("show", "kw"), (" 1 < n ! + 1 ", "pl"), ("by", "kw")],
    [("      have", "kw"), (" := Nat.factorial_pos n; ", "pl"), ("omega", "op"), (")", "pl")],
    [("  refine ", "kw"), ("⟨p, hp, ?_⟩", "pl")],
    [("  by_contra", "kw"), (" h", "pl")],
    [("  push_neg", "kw"), (" at", "kw"), (" h", "pl")],
    [("  have", "kw"), (" hfac : p ∣ n ! := hp.dvd_factorial.mpr h", "pl")],
    [("  have", "kw"), (" hone : p ∣ 1 := ", "pl"), ("by", "kw")],
    [("    have", "kw"), (" := Nat.dvd_sub hdvd hfac (Nat.le_succ (n !))", "pl")],
    [("    simpa", "op"), (" using", "kw"), (" this", "pl")],
    [("  exact", "kw"), (" hp.not_dvd_one hone", "pl")], [],
    [("#print axioms exists_prime_gt", "cm")],
]
CLR = {"kw": (192, 132, 252), "ty": (94, 234, 212), "op": (125, 211, 252),
       "pl": (226, 232, 240), "cm": (100, 116, 139)}


def build(gap_extra):
    img = background()
    d = ImageDraw.Draw(img)
    n_gap = [0]

    def gap(base):
        nonlocal y
        y += base + gap_extra
        n_gap[0] += 1

    y = s(40)
    # ---------------- header
    d.line((x0, y + s(6), x0 + s(22), y + s(6)), fill=TEAL, width=3)
    text(d, (x0 + s(32), y + s(9)), "AI AGENT × LEAN 4 形式化验证", "cnb", s(10.4), TEAL,
         tracking=s(1.8))
    gap(s(26))
    text(d, (x0, y + s(30)), "用 Lean 证明 ", "cnb", s(36), INK, tracking=-s(0.5))
    w1 = tw("用 Lean 证明 ", "cnb", s(36), -s(0.5))
    text(d, (x0 + w1, y + s(30)), "Euclid 定理", "cnb", s(36), TEAL, tracking=-s(0.5))
    text(d, (x0, y + s(74)), "素数没有上界", "cnb", s(36), INK, tracking=-s(0.5))
    text(d, (W - MG, y + s(8)), "01", "cnb", s(46), FAINT2, tracking=-s(2), align="right")
    text(d, (W - MG, y + s(30)), "A4 / 一页报告", "cn", s(9.2), FAINT, tracking=s(1.4),
         align="right")
    gap(s(112))
    y = para(d, x0, y + s(18),
             "设计一个「生成 + 裁决」的 Agent：LLM 负责构造候选证明，Lean 4 + Mathlib 负责不可辩驳的终审。",
             "cn", s(12), MUTED, s(560), s(20))
    gap(s(30))

    # ---------------- quote
    qh = s(52)
    shadow(img, (x0, y, x0 + CW, y + qh), s(6), blur=10, alpha=16, dy=4)
    d.rounded_rectangle((x0, y, x0 + CW, y + qh), radius=s(6), fill=WHITE, outline=LINE, width=2)
    d.rounded_rectangle((x0, y, x0 + s(4), y + qh), radius=s(2), fill=TEAL)
    text(d, (x0 + s(16), y + s(30)), "题目原文", "cnb", s(9.6), TEAL, tracking=s(1.2))
    qx = x0 + s(16) + tw("题目原文", "cnb", s(9.6), s(1.2)) + s(16)
    para(d, qx, y + s(28.5),
         "设计个 Agent，用 Lean 形式化证明 Euclid's theorem：对任意（随机）的整数 n，都存在素数 p > n。",
         "cn", s(10.8), (51, 65, 85), CW - (qx - x0) - s(16), s(16.5))
    y += qh

    # ---------------- section helper
    def section(y, no, title, en):
        chh = s(21)
        nw = tw(no, "cnb", s(10), s(0.6)) + s(20)
        d.rounded_rectangle((x0, y, x0 + nw, y + chh), radius=s(3), fill=TEAL_L)
        text(d, (x0 + s(10), y + chh / 2 + s(4.4)), no, "cnb", s(10), TEAL,
             tracking=s(0.6))
        text(d, (x0 + nw + s(13), y + chh / 2 + s(5.2)), title, "cnb", s(14.6), INK)
        text(d, (W - MG, y + chh / 2 + s(3.6)), en, "cnb", s(8.8), FAINT2, tracking=s(1.6),
             align="right")
        return y + chh

    # ---------------- section 01
    gap(s(40))
    y = section(y, "01", "命题与数学直觉", "STATEMENT")
    gap(s(14))

    ch1 = s(96)
    wL = int(s(372)); wR = CW - wL - s(12)
    def card(box, label):
        shadow(img, box, s(7), blur=10, alpha=18, dy=4)
        d.rounded_rectangle(box, radius=s(7), fill=WHITE, outline=LINE, width=2)
        text(d, (box[0] + s(16), box[1] + s(22)), label, "cnb", s(9.2), TEAL, tracking=s(1.3))

    card((x0, y, x0 + wL, y + ch1), "形式化命题 / PROPOSITION")
    fy = y + s(56)
    text(d, (x0 + s(16), fy), "∀ n : ℕ, ∃ p, p.Prime ∧ n < p", "cnb", s(16.6), INK)
    text(d, (x0 + s(16), fy + s(24)), "theorem exists_prime_gt (n : ℕ) : ∃ p, p.Prime ∧ n < p",
         "mono", s(6.8), FAINT)

    bx = x0 + wL + s(12)
    card((bx, y, bx + wR, y + ch1), "构造思路 / 三步")
    sy = y + s(46)
    for mk, txt in [("①", "取 N = n! + 1，显然 N > 1，故有素因子 p。"),
                    ("②", "若 p ≤ n，则 p ∣ n!；又 p ∣ N，相减得 p ∣ 1，与 p 为素数矛盾。"),
                    ("③", "故 p > n：素数可任意大，ℕ 中素数无穷多。")]:
        text(d, (bx + s(16), sy), mk, "cnb", s(10.4), TEAL)
        sy = para(d, bx + s(31), sy, txt, "cn", s(10.1), (51, 65, 85), wR - s(48), s(14.8)) + s(20.6)
    y += ch1

    gap(s(16))
    text(d, (x0, y + s(9)),
         "注：n = 4 时 p 可取 5，n = 100 时 p 可取 101 —— 定理只保证存在性，不给出第 k 个素数的显式公式。",
         "cn", s(9.2), FAINT, tracking=s(0.2))
    y += s(14)

    # ---------------- section 02
    gap(s(30))
    y = section(y, "02", "Lean 4 候选证明（Agent 产出）", "CANDIDATE PROOF")
    gap(s(14))

    code_size, line_h, bar_h = s(9.0), s(15.2), s(31)
    pad = s(14)
    panel_h = bar_h + s(15) + len(CODE) * line_h + s(12)
    wCode = int(CW * 0.632)
    wVer = CW - wCode - s(12)

    shadow(img, (x0, y, x0 + wCode, y + panel_h), s(8), blur=18, alpha=34, dy=10)
    d.rounded_rectangle((x0, y, x0 + wCode, y + panel_h), radius=s(8), fill=(15, 23, 42))
    d.line((x0 + 2, y + bar_h, x0 + wCode - 2, y + bar_h), fill=(30, 41, 59), width=2)
    for i, c in enumerate([(248, 113, 113), (251, 191, 36), (52, 211, 153)]):
        cx = x0 + s(15) + i * s(13)
        d.ellipse((cx, y + bar_h / 2 - s(3.6), cx + s(7.2), y + bar_h / 2 + s(3.6)), fill=c)
    text(d, (x0 + s(62), y + bar_h / 2 + s(3.4)), "Euclid/PrimeUnbounded.lean", "mono", s(8.8),
         (110, 125, 148))
    tg = "Lean 4 · Mathlib"
    tgw = tw(tg, "cnb", s(8.0)) + s(14)
    tx2 = x0 + wCode - s(12) - tgw
    d.rounded_rectangle((tx2, y + s(8.5), x0 + wCode - s(12), y + bar_h - s(8.5)),
                        radius=s(3), fill=(12, 46, 45), outline=(32, 78, 74), width=2)
    text(d, (tx2 + tgw / 2, y + bar_h / 2 + s(3.2)), tg, "cnb", s(8.0), (94, 234, 212),
         tracking=s(0.4), align="center")
    cy = y + bar_h + s(18)
    for ln in CODE:
        cx = x0 + pad
        for txt, st in ln:
            cx = text(d, (cx, cy), txt, "moni" if st == "cm" else "mono", code_size, CLR[st])
        cy += line_h

    vx = x0 + wCode + s(12)
    by = y
    bh = s(52)
    shadow(img, (vx, by, vx + wVer, by + bh), s(7), blur=10, alpha=16, dy=4)
    d.rounded_rectangle((vx, by, vx + wVer, by + bh), radius=s(7), fill=(236, 253, 245),
                        outline=(167, 243, 208), width=2)
    r = s(11)
    d.ellipse((vx + s(14), by + bh / 2 - r, vx + s(14) + 2 * r, by + bh / 2 + r), fill=TEAL)
    text(d, (vx + s(14) + r, by + bh / 2 + s(4.6)), "✓", "sym", s(12), WHITE, align="center")
    text(d, (vx + s(46), by + s(24)), "编译通过 · 零 sorry", "cnb", s(12), (6, 95, 70))
    text(d, (vx + s(46), by + s(39)), "NO ERRORS · NO SORRY · NO ADMIT", "cnb", s(7.2),
         (4, 120, 87), tracking=s(0.6))

    by += bh + s(10)
    ah = s(70)
    shadow(img, (vx, by, vx + wVer, by + ah), s(7), blur=10, alpha=14, dy=4)
    d.rounded_rectangle((vx, by, vx + wVer, by + ah), radius=s(7), fill=WHITE, outline=LINE, width=2)
    text(d, (vx + s(14), by + s(20)), "公理依赖 / #PRINT AXIOMS", "cnb", s(8.4), FAINT,
         tracking=s(1.0))
    ay = by + s(36)
    for ln in ["[propext,", " Classical.choice,", " Quot.sound]"]:
        text(d, (vx + s(14), ay), ln, "mono", s(8.4), TEAL)
        ay += s(12.4)

    by += ah + s(10)
    ch2 = y + panel_h - by
    d.rounded_rectangle((vx, by, vx + wVer, by + ch2), radius=s(7), fill=WHITE, outline=LINE, width=2)
    text(d, (vx + s(14), by + s(20)), "验收清单", "cnb", s(8.4), FAINT, tracking=s(1.0))
    cy2 = by + s(38)
    for it in ["命题与原题一致", "编译零错误、零 sorry", "公理集 ⊆ 标准三公理", "一次通过，未经历修正"]:
        text(d, (vx + s(14), cy2), "✓", "sym", s(8.8), TEAL)
        text(d, (vx + s(28), cy2), it, "cn", s(9.8), (51, 65, 85))
        cy2 += s(16.4)
    d.line((vx + s(14), by + ch2 - s(44), vx + wVer - s(14), by + ch2 - s(44)), fill=LINE, width=2)
    text(d, (vx + s(14), by + ch2 - s(24)), "0 error · 0 sorry · 3 axioms", "monb", s(8.0), TEAL)
    y += panel_h

    # ---------------- section 03
    gap(s(30))
    y = section(y, "03", "Agent 架构：生成 + 确定性裁决", "AGENT LOOP")
    gap(s(14))

    boxes = [("S1", "规格化", "自然语言题 → Lean 命题签名"),
             ("S2", "检索", "定位 Mathlib 引理与骨架"),
             ("S3", "生成候选", "LLM 生成可编译脚本"),
             ("S4", "Lean 裁决", "LSP 检查，只认机器结果"),
             ("S5", "修正 · 审计", "错误回灌；合规才交付")]
    baw = s(26)
    bh2 = s(80)
    bwid = (CW - 4 * baw) / 5.0
    for i, (no, ttl, desc) in enumerate(boxes):
        bx2 = x0 + i * (bwid + baw)
        hot = (i == 2)
        shadow(img, (bx2, y, bx2 + bwid, y + bh2), s(6), blur=9, alpha=16, dy=4)
        d.rounded_rectangle((bx2, y, bx2 + bwid, y + bh2), radius=s(6),
                            fill=TEAL if hot else WHITE,
                            outline=TEAL if hot else LINE, width=2)
        text(d, (bx2 + s(12), y + s(20)), no, "monb", s(8.2),
             (153, 246, 228) if hot else FAINT, tracking=s(1.0))
        text(d, (bx2 + s(12), y + s(37)), ttl, "cnb", s(11.2), WHITE if hot else INK)
        para(d, bx2 + s(12), y + s(52), desc, "cn", s(7.9),
             (204, 251, 241) if hot else (100, 116, 139), bwid - s(22), s(11.2))
        if i < 4:
            text(d, (bx2 + bwid + baw / 2, y + bh2 / 2 + s(5)), "›", "cnb", s(15), FAINT,
                 align="center")
    y += bh2

    gap(s(14))
    text(d, (x0, y + s(10)), "LOOP", "monb", s(8.2), AMBER, tracking=s(1.0))
    lx = x0 + s(40)
    lx = text(d, (lx, y + s(10)), "报错 → 附完整代码与错误信息回灌 S3，直至 ", "cn", s(9.6), MUTED)
    lx = text(d, (lx, y + s(10)), "ERRORS = 0", "monb", s(9.6), AMBER)
    text(d, (lx, y + s(10)), " 且公理集 ⊆ 标准三公理（S1–S5 对应课堂演示流程）。", "cn", s(9.6), MUTED)
    y += s(34)
    d.line((x0, y, W - MG, y), fill=LINE, width=2)
    ty = y + s(26)
    text(d, (x0, ty), "结论", "cnb", s(10), TEAL, tracking=s(1.2))
    para(d, x0 + s(38), ty,
         "AI 的价值不在「想得对」，而在把「对」变成可机器检查的事实：人类负责提命题与验收标准，Lean 负责终审。",
         "cn", s(11), (51, 65, 85), CW - s(320), s(17.6))
    for i, m in enumerate(["复核：代码请在本机 Lean 环境复跑确认",
                           "环境：Lean 4.19 + Mathlib　·　页面 A4 210×297 mm"]):
        text(d, (W - MG, ty - s(10) + i * s(13.5)), m, "cn", s(8.0), FAINT, tracking=s(0.2),
             align="right")
    return ty + s(44), n_gap[0], img



_, ng, _im = build(0)
lo, hi = -s(90), s(240)
for _ in range(24):
    mid = (lo + hi) / 2
    yend, _, _i = build(mid)
    if yend > TARGET_END:
        hi = mid
    else:
        lo = mid
yend, ng, img = build(lo)
out = "C:/Users/zhangwenbo/Desktop/课程/ai-math-a4/A4-Euclid-Lean.png"
img.save(out, dpi=(300, 300))
print("gap_extra px:", round(lo, 1), "css:", round(lo / S, 1), "gaps:", ng, "yend:", round(yend), "target:", round(TARGET_END))








