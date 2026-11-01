# -*- coding: utf-8 -*-
"""S7.13 中文落档生成：路2攻防XLII-S7.13-khat_lipschitz真证-S_smooth奇点延拓与L导数件"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.13-khat_lipschitz真证-S_smooth奇点延拓与L导数件.docx"

doc = Document()

# A4 + 2.5cm margins
sec = doc.sections[0]
sec.page_width = Cm(21.0)
sec.page_height = Cm(29.7)
sec.top_margin = Cm(2.5)
sec.bottom_margin = Cm(2.5)
sec.left_margin = Cm(2.5)
sec.right_margin = Cm(2.5)

# page number footer (centered arabic)
footer = sec.footer
fp = footer.paragraphs[0]
fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
run = fp.add_run()
fld1 = OxmlElement('w:fldChar'); fld1.set(qn('w:fldCharType'), 'begin')
instr = OxmlElement('w:instrText'); instr.set(qn('xml:space'), 'preserve'); instr.text = 'PAGE'
fld2 = OxmlElement('w:fldChar'); fld2.set(qn('w:fldCharType'), 'end')
run._r.append(fld1); run._r.append(instr); run._r.append(fld2)
for r in fp.runs:
    r.font.size = Pt(9)

def style_base():
    st = doc.styles['Normal']
    st.font.name = 'Times New Roman'
    st.font.size = Pt(12)
    st._element.rPr.rFonts.set(qn('w:eastAsia'), '宋体')
    pf = st.paragraph_format
    pf.alignment = WD_ALIGN_PARAGRAPH.JUSTIFY
    pf.line_spacing_rule = WD_LINE_SPACING.ONE_POINT_FIVE
    pf.first_line_indent = Cm(0.74)
    pf.space_before = Pt(0)
    pf.space_after = Pt(0)

style_base()

def set_run(run, cn='宋体', en='Times New Roman', size=12, bold=False, color=(0, 0, 0)):
    run.font.name = en
    run.font.size = Pt(size)
    run.font.bold = bold
    run.font.color.rgb = RGBColor(*color)
    rPr = run._element.get_or_add_rPr()
    rFonts = rPr.find(qn('w:rFonts'))
    if rFonts is None:
        rFonts = OxmlElement('w:rFonts')
        rPr.append(rFonts)
    rFonts.set(qn('w:eastAsia'), cn)

def add_title(text):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    p.paragraph_format.space_after = Pt(18)
    p.paragraph_format.first_line_indent = Cm(0)
    r = p.add_run(text)
    set_run(r, cn='黑体', size=18, bold=True)
    return p

def add_meta(text):
    p = doc.add_paragraph()
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    p.paragraph_format.space_after = Pt(12)
    p.paragraph_format.first_line_indent = Cm(0)
    r = p.add_run(text)
    set_run(r, cn='楷体', size=12)
    return p

def add_h1(text):
    p = doc.add_paragraph(style='Heading 1')
    p.paragraph_format.space_before = Pt(14)
    p.paragraph_format.space_after = Pt(6)
    p.paragraph_format.first_line_indent = Cm(0)
    p.paragraph_format.keep_with_next = True
    r = p.add_run(text)
    set_run(r, cn='黑体', size=16, bold=True)
    return p

def add_h2(text):
    p = doc.add_paragraph(style='Heading 2')
    p.paragraph_format.space_before = Pt(11)
    p.paragraph_format.space_after = Pt(5)
    p.paragraph_format.first_line_indent = Cm(0)
    p.paragraph_format.keep_with_next = True
    r = p.add_run(text)
    set_run(r, cn='黑体', size=14, bold=True)
    return p

def add_para(text, indent=True):
    p = doc.add_paragraph()
    if not indent:
        p.paragraph_format.first_line_indent = Cm(0)
    r = p.add_run(text)
    set_run(r, cn='宋体', size=12)
    return p

def add_math_para(text, indent=False):
    p = doc.add_paragraph()
    if not indent:
        p.paragraph_format.first_line_indent = Cm(0)
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    r = p.add_run(text)
    set_run(r, cn='宋体', size=12)
    return p

add_title('路 2 攻防 XLII-S7.13：khat_lipschitz 真证——S_smooth 奇点延拓与 L 导数件')
add_meta('（光滑/导数层件 · 2026-10-30 · 落档 d1 惯例）')

add_h1('1  结论摘要')
add_para('本轮完成 QRH Lean 形式化项目（C:\\proj2\\QRH）光滑层最后一件：命名 axiom khat_lipschitz 由 axiom 降为真证定理，原 axiom 删除。'
         '关键前置口径修正：原 axiom 陈述在 Khat 原闭式下为假——闭式 (sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu))/(√2·sin(1/√2)) '
         '在 u = ±√2/(2π) 处两个正弦项分母为零，Lean 实数除法惯例在该点取 0，而解析延拓应为 1/2，Lipschitz 不等式在该点失效。'
         '修法引入 S_smooth（可去奇点延拓：x = 0 处取 1/2，否则 sin(x/2)/x），Khat 改新闭式；原 axiom khat_lipschitz 删除。')
add_para('显式常数：L = π/(√2·|sin(1/√2)|) ≈ 3.42。证明链 = Core §3b S_smooth 件约 12 条（均值定理三辅助、'
         'S_smooth_hasDerivAt_zero 夹逼 slope 口径、S_smooth_deriv_bound（|deriv S_smooth| ≤ 1/4）、S_smooth_lipschitz_1_4）'
         '+ §3c khat 件 3 条（khat_hasDerivAt 商法则域化简四段、khat_deriv_bound（‖deriv K̂ u‖ ≤ π/(√2·|sin(1/√2)|)）、'
         'khat_lipschitz 组装（Convex.norm_image_sub_le_of_norm_deriv_le））；Stage3 Khat_closed_form 适配新定义（S_smooth 展开两件）。')
add_para('全量 lake build QRH：2704 jobs、exit = 0、0 error、0 warning（dbg_build_khat.txt；Core 单编 core_khat10.txt exit = 0）。'
         '挂账 axiom 净减 1：残余命名 axiom 仅 fourierCos_Khat（连接件，定义一致件）+ bgs5_khat_fourier_supp（积分层窄支撑）；'
         'prime_weight_bounds_Khat 中 M = L·δ + B 的 L 实参现为真证常数，该链条无 axiom 缺口。')

add_h1('2  背景与定位')
add_h2('2.1  khat_lipschitz 在 S7.1 形式化中的角色')
add_para('prime_weight_bounds_Khat（S7.10 降定理）需要素项权重 b_n 的平滑性：|b_n| ≤ M·(√n)⁻¹ 与差分界 |Δb_n| ≤ M·n^(−3/2)，'
         '其中 M = L·δ + B；L 为配对核 K̂ = Khat 的 Lipschitz 常数，B 来自 khat_global_bound（全局一致界 |K̂u| ≤ (√2·|sin(1/√2)|)⁻¹）。'
         '此前 khat_lipschitz 为命名 axiom（陈述 ∃L，0 ≤ L ∧ ∀u v，|Khat u − Khat v| ≤ L·|u−v|），L 由解析式可算但未形式化。')
add_h2('2.2  axiom 积压状态')
add_para('Core §4b 原为三个命名 axiom：fourierCos（载体，2026-10-29 已降为 Bochner 真定义出账）、fourierCos_Khat（连接件：'
         'fourierCos Khat = Khat 闭式）、khat_lipschitz（光滑件）。S7.12 落档后，光滑件为剩余最近攻坚件；本档出账 khat_lipschitz。')
add_h2('2.3  原陈述为假的诊断')
add_para('原 axiom 陈述在 Khat 原闭式下为假。闭式含项 sin((√2−2πu)/2)/(√2−2πu) 与 sin((√2+2πu)/2)/(√2+2πu)：'
         '在 u = ±√2/(2π) 处分母 √2−2πu 与 √2+2πu 分别为零，数学上为正弦基频可去奇点（极限 1/2），'
         '但 Lean 实数除法在分母为零时惯例返回 0，故 Lean 语义下 K̂(±√2/(2π)) = 0，而邻域值趋向 ±(√2·sin(1/√2))⁻¹·(1/2) 附近非零——'
         'Lipschitz 不等式在该点两侧失效，陈述为假。遵循 S7.9/S7.11/S7.12 既定模式：先修口径，再真证。')

add_h1('3  口径修正：S_smooth 奇点延拓')
add_h2('3.1  定义')
add_math_para('S_smooth x = if x = 0 then 1/2 else sin(x/2)/x')
add_math_para('Khat u = (S_smooth (√2−2πu) + S_smooth (√2+2πu)) / (√2·sin(1/√2))')
add_para('S_smooth 为 sin(x/2)/x 的可去奇点延拓：lim_{x→0} sin(x/2)/x = 1/2。Khat 在 u = ±√2/(2π) 处逐项连续化（每项贡献 '
         '1/2·(√2·sin(1/√2))⁻¹），全实轴良定义。', indent=True)
add_h2('3.2  存量件')
add_para('Khat_neg（偶性）、Khat_zero（K̂(0) = 1）、Khat_abs_le（频域衰减三角不等式界，带 h1/h2 非奇点前提）在新定义下改编编译通过；'
         '原 axiom khat_lipschitz 删除。分母良定义件 sin_inv_sqrt2_ne_zero 沿用；√2 非零用 positivity。')

add_h1('4  真证链：Core §3b/§3c')
add_h2('4.1  均值定理三辅助')
add_para('abs_cos_sub_one_le_sq_of_nonneg（|cos t − 1| ≤ t²）、abs_sin_sub_id_le_cube_of_nonneg（|sin t − t| ≤ t³）、'
         'abs_sin_sub_mul_cos_le_sq（|sin t − t·cos t| ≤ t²）：均经 mathlib Convex.norm_image_sub_le_of_norm_deriv_le '
         '在段 [0, s] 上证明；调用参数全命名实参（标量域 ℝ、G := ℝ、f := …、s := Set.Icc 0 s、C := …、x := x、y := y，'
         '标量域参数即 mathlib 的 k 处），点态不等式参数 (fun x _ => hdiff x)，产出方向 |y − x| ≤ … 处一律 '
         'simpa [Real.norm_eq_abs, abs_sub_comm] 归位。导数件一律采用同形声明 + simpa 模式（不用 convert——convert 会带出 typeclass 相等目标）。')
add_h2('4.2  S_smooth_hasDerivAt_zero（夹逼 slope 口径）')
add_para('rw [hasDerivAt_iff_tendsto_slope] 后目标化为 Tendsto (fun y => slope S_smooth 0 y) (nhds[≠0] 0) (nhds 0)（nhds 为 mathlib 邻域滤子记号）。'
         'hbound：‖slope S_smooth 0 y‖ ≤ |y|/8——hslope 改写链 unfold slope + rw [sub_zero] + smul_eq_mul + mul_comm + rfl'
         '（ℝ 上差为 VSub，ring 不可用，必须逐项改写）。上下界用 tendsto_of_tendsto_of_tendsto_of_le_of_le：'
         '下界 tendsto_const_nhds（必须 term 模式带完整类型标注，by 块内 exact 会留 metavar）、上界 hconv（先 nhds 0 上 h1.mul h2，'
         '再 h0.mono_left (inf_le_left : nhds[{0}ᶜ] ≤ nhds 0)），中点函数 norm_nonneg（参数名 a 而非 x，只绑 y 不绑 x ∈ univ）；'
         '最终 exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm。')
add_h2('4.3  S_smooth_deriv_bound 与 S_smooth_lipschitz_1_4')
add_para('|deriv S_smooth x| ≤ 1/4：x = 0 处导数 0（夹逼件）；x ≠ 0 处经 |sin t − t cos t| ≤ t² 得商式导数界。'
         'S_smooth_lipschitz_1_4 由 Convex.norm_image_sub_le_of_norm_deriv_le（全命名实参 + abs_sub_comm）组装。')
add_h2('4.4  khat_hasDerivAt（商法则域化简四段）')
add_para('复合链 hsum = hd1.add hd2（S_smooth ∘ 线性件，导数 d1 = deriv S_smooth (√2−2πu)·(−2π)、d2 = deriv S_smooth (√2+2πu)·(2π)）；'
         '商法则 hsum.div hc hdiv 后目标导数 2π(d2−d1)/c，hc : HasDerivAt (fun _ => c) 0，hdiv : c ≠ 0（c = √2·sin(1/√2)）。'
         '域化简不做 convert，两步行进：h_eq1 为纯 ring 证 2π(d2−d1) = d1·(−2π) + d2·(2π)；'
         'h_eq2 逆元链——hcc : c⁻¹ = c·c⁻¹^2（rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hdiv, one_mul]），'
         '随后 rw [div_eq_mul_inv]、rw [hcc]、rw [← mul_assoc]、rw [show (f′·c − f·0) = f′·c by ring]；'
         '末尾 h_div 独立声明 (f′·c)/c² = (f′·c)·c⁻¹^2（rw [div_eq_mul_inv] + rw [← inv_pow]）——'
         'rw [← inv_pow] 必须作用于独立声明：主目标直接 rw 时 RHS 仍为 /c² 表示，找不到 (?a ^ ?n)⁻¹ 模式。'
         '最后 rw [h_eq1, h_eq2] 后 exact hd。')
add_h2('4.5  khat_deriv_bound')
add_para('‖deriv Khat u‖ ≤ π/(√2·|sin(1/√2)|)：rw [hd.deriv] 后，hpos : 0 < √2·|sin(1/√2)|，'
         '分子经 S_smooth_deriv_bound + norm_mul_le + norm_sub_le 三角收紧至 ≤ π。')
add_h2('4.6  khat_lipschitz 组装')
add_math_para('khat_lipschitz : ∃ L, 0 ≤ L ∧ ∀ u v, |Khat u − Khat v| ≤ L * |u − v|')
add_para('L 取 π/(√2·|sin(1/√2)|)。组装：Convex.norm_image_sub_le_of_norm_deriv_le '
         '（标量域 ℝ、G := ℝ、f := Khat、s := Set.univ、C := π/(√2·|sin(1/√2)|)、x := u、y := v、'
         '(fun x _ => hdiff x)、fun x _ => hb x、convex_univ、trivial、trivial）→ simpa [Real.norm_eq_abs, abs_sub_comm] using hres。')

add_h1('5  Stage3 适配：Khat_closed_form')
add_para('Khat_closed_form（khat_second_order_bound 的闭式件）在 rw [hA, hB]（sin 角替换 (√2±2πu)/2 → √2/2 ± πu）前需先展开 S_smooth：'
         'hsa/hsb 两件（unfold S_smooth + rw [ite_eq_right hd1 / ite_eq_right hd2]，hd1 : √2−2πu ≠ 0、hd2 : √2+2πu ≠ 0）'
         '把 S_smooth (√2±2πu) 换为 sin((√2±2πu)/2)/(√2±2πu)，随后闭式链（field_simp、Real.sin_sub/sin_add、sqrt2_div_two_eq_inv、ring_nf、hsq）零改动。')

add_h1('6  构建验证')
add_para('Core 单编轮次 core_khat1.txt … core_khat10.txt（首插桩约 30 错逐类收口）；core_khat10.txt 空输出 = exit = 0。'
         '全量 lake build QRH：2704 jobs、exit = 0、0 error、0 warning（dbg_build_khat.txt；'
         'Main L1027 与 Stage3 L914 各有一条 ring_nf「Try this」info 提示，非 error/warning，与 S7.10–S7.12 同款）。'
         '弃用清理沿用惯例：if_neg/if_pos/Set.mem_setOf_eq → ite_eq_right/ite_eq_left/Set.mem_ofPred_eq。')

add_h1('7  残余命名 axiom 状态表')
tbl = doc.add_table(rows=9, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('名称', '位置', '状态'),
    ('fourierCos_Khat', 'Core §4b', '连接件：fourierCos Khat = Khat 闭式，定义一致件'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS 引理 5 频域支撑，积分层件'),
    ('siegel_walfisz_chi5', 'Main', 'SW 定理 χ₅ 版，PNT-in-AP 量级'),
    ('landau_explicit_L', 'Main', 'Landau 显式公式 L 版；(L1b) 两件出账'),
    ('N_L_lower_bound', 'Stage3', '结构件，S6 零点计数'),
    ('n2_linkage', 'Stage3', '结构件，S7.4 定理 N2'),
    ('n3_remainder_uniform', 'Stage3', '结构件，S7.5 定理 N3'),
    ('khat_lipschitz', 'Core §4b', '本轮出账；L ≈ 3.42 显式（axiom → theorem）'),
]
widths = [Cm(4.2), Cm(2.6), Cm(9.2)]
for row in tbl.rows:
    for j, cell in enumerate(row.cells):
        cell.width = widths[j]
# header row: tblHeader + bold; all rows: cantSplit
from docx.oxml.ns import qn as _qn
from docx.oxml import OxmlElement as _OE
for i, row in enumerate(data):
    trPr = tbl.rows[i]._tr.get_or_add_trPr()
    cant = _OE('w:cantSplit')
    trPr.append(cant)
    if i == 0:
        th = _OE('w:tblHeader')
        trPr.append(th)
    for j, val in enumerate(row):
        cell = tbl.rows[i].cells[j]
        cell.paragraphs[0].text = ''
        p = cell.paragraphs[0]
        p.paragraph_format.first_line_indent = Cm(0)
        p.paragraph_format.line_spacing_rule = WD_LINE_SPACING.SINGLE
        p.paragraph_format.space_before = Pt(0)
        p.paragraph_format.space_after = Pt(0)
        p.alignment = WD_ALIGN_PARAGRAPH.CENTER if (i == 0 or j == 0) else WD_ALIGN_PARAGRAPH.LEFT
        r = p.add_run(val)
        set_run(r, cn='宋体', size=9.5, bold=(i == 0))

add_para('注：上表为 2026-10-30 快照。fourierCos / fourierCos_scale / f0_sub_feps_L1_bound / prime_weight_bounds_Khat / khat_lipschitz 已出账；'
         'khat_lipschitz 出账后，prime_weight_bounds_Khat 的 M = L·δ + B 全项为真证常数；'
         '残余最近攻坚件为 fourierCos_Khat（连接件）与 bgs5_khat_fourier_supp（积分层窄支撑，挂聚合）。', indent=True)

doc.save(OUT)
print('saved:', OUT)
