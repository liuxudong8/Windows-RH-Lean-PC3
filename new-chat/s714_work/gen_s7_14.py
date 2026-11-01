# -*- coding: utf-8 -*-
"""S7.14 中文落档生成：路2攻防XLII-S7.14-pairCount_L1_bound真证-截断零点集口径修正与axiom降定理"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.14-pairCount_L1_bound真证-截断零点集口径修正与axiom降定理.docx"

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

add_title('路 2 攻防 XLII-S7.14：pairCount_L1_bound 真证——截断零点集口径修正与 axiom 降定理')
add_meta('（配对计数 L¹ 界件 · 2026-10-31 · 落档 d1 惯例）')

add_h1('1  结论摘要')
add_para('本轮完成 QRH Lean 形式化项目（C:\\proj2\\QRH）N2b 组装积分层最后一件：命名 axiom pairCount_L1_bound 由 axiom 降为真证定理，'
         '原 axiom 删除，真证块落于 S7_1_Stage3.lean 第 763 行起。关键前置口径修正（用户拍板方案，遵循项目既定模式“先修口径、再真证”——'
         '与 f0 支撑截断、S7.9、S7.11、S7.13 同款）：原 axiom 陈述存在两处硬伤。')
add_para('硬伤一（零点集）：zerosLChi5 为临界带全零点集（无限）。竖直差带窗口 2πε/logT 内（成对虚部差 |Im z₁ − Im z₂| ≤ 2πε/logT）'
         '配对数为无限多（零点密度 ~ T·logT/(2π) 连续分布），离散和 Σ_{z₁≠z₂} g(δΔ) 在该无限集合上无定义、Summable 为假——根本缺陷。')
add_para('硬伤二（归一化）：原 RHS 为 D·δ·‖g‖₁，其中 δ = logT/(2π) 是配对位移尺度而非零点计数，对 T 的量纲/口径不一致；'
         '文档层 S7.1 §2 中配对常数的归一化 N 即零点数 N_Z(T)。')
add_para('修正四件套：① 截断 Z_T := zerosLChi5UpTo T（有限 → 求和为 Finset 和）；'
         '② 陈述 ∃D ≥ 0, ∀T ≥ T0, Σ_{z₁≠z₂∈Z_T} |g(δ·Δ)| ≤ D·N_Z(T)·‖g‖₁（归一化以零点计数 N_Z 替换 δ）；'
         '③ 新增两条数论结构 axiom：zerosLChi5_bounded_finite（Z_T 有限）、pair_count_bound（(1:ℝ) 计数 ≤ Dcnt·N_L T，门槛 1 < T0）；'
         '④ pair_const_eps_bias 组装归一化同步 N := N_L T、Z := zerosLChi5UpTo T，门槛 1 ≤ T0 → 1 < T0，Bound 仍 = ε。')
add_para('真证链（Stage3）：rcases pair_count_bound → M := (√2|sin(1/√2)|)⁻¹ → hMpos/hM0 → hLpos := normL1_sub_pos → '
         'D := (2·M·Dcnt)/normL1 → hD0 → hfinZ/hfinP（有限支撑）→ hsum_supp/hsum、hcnt_supp/hcnt_sum → hterm（逐项界）→ '
         'hg_sum（Summable.of_norm_bounded）→ hle_sum（Summable.tsum_le_tsum 三参）→ hle2 → hle3（unfold D + le_div_iff₀ + ring）→ '
         '⟨hsum, le_trans hle2 hle3⟩。')
add_para('显式常量：D = 2M·Dcnt/‖f₀−f_ε‖₁，M = (√2·|sin(1/√2)|)⁻¹，Bound 仍 = ε；'
         '其中 ‖f₀−f_ε‖₁ ≤ 2εM 为增量⑤ f0_sub_feps_L1_bound 真证结果。')
add_para('编译证据：单编 stage3_pceb12.txt 空输出 = exit = 0（仅弃用 warning）；'
         '全量 lake build QRH → build_qrh_lake.txt：2719 jobs、exit = 0、0 error（较上一基线 2704 增 15 job：'
         'zerosLChi5UpTo def + 结构 axiom 两件 + 真证件）。')

add_h1('2  背景与定位')
add_h2('2.1  pairCount_L1_bound 在 N2b 组装中的角色')
add_para('pair_const_eps_bias（S7.13 后的增量⑦，2026-10-30 已真证出账）组装配对常数偏差：'
         'pairConstant 展开后 |Σ_{z₁≠z₂} g(δ·Δ)|/N 的求和项可和性与界是最后缺失的积分层桥。'
         '此前 pairCount_L1_bound 为命名 axiom，陈述"离散配对和 ≤ D·δ·normL1"（含可和性三件打包 + D·N·normL1 界，D 对数配对密度）。'
         '本轮完成其 axiom → theorem 出账，不做 axiom→axiom 空换名。')
add_h2('2.2  原 axiom 两处硬伤诊断')
add_para('（i）零点集选择错误：zerosLChi5 为临界带全零点集（无限）。竖直差带窗口 2πε/logT 内配对数为无限多——'
         '零点的竖直密度随高度连续（Riemann–von Mangoldt 密度 ~ (1/2π)·log(T/2π)），固定窗口 2πε/logT 内存在无限多个成对零点，'
         'Σ 在无限集上无定义，Summable 为假。截断至 Z_T := {z ∈ zerosLChi5 | |Im z| ≤ T} 后集合有限，和式良定义。')
add_para('（ii）归一化不一致：δ = logT/(2π) 为配对位移尺度（S7.1 §2 中 A = 1 + Σ K(δΔ)²/N_Z，δ = logT/(2π)，N = 零点数 N_Z）。'
         '原 RHS 写 D·δ·‖g‖₁ 以 δ 充当归一化，对 T 的量级/口径均与文档层不一致；正确归一化为零点计数 N_Z(T)。')
add_h2('2.3  既定模式')
add_para('遵循项目惯例：先修口径、再真证（f0 支撑截断、S7.9 素数项界假命题、S7.11 x=1 边界、S7.13 奇点延拓同款）；'
         '口径修正后真证，不保留改名 axiom。')

add_h1('3  口径修正：截断零点集与归一化')
add_h2('3.1  截断零点集')
add_math_para('Z_T := zerosLChi5UpTo T := {z ∈ zerosLChi5 | |Im z| ≤ T}')
add_para('zerosLChi5UpTo 为新增 def（S7_1_Stage3.lean）；Z_T 为有限集（Finset），求和改为 Finset 和，Summable 自动成立。')
add_h2('3.2  新陈述')
add_math_para('pairCount_L1_bound : (hT0 : 1 < T0) → ∃ D ≥ 0, ∀ T ≥ T0, Σ_{z₁≠z₂∈Z_T} |g(δ·Δ)| ≤ D · N_Z(T) · ‖g‖₁')
add_h2('3.3  新增数论结构 axiom 两条')
add_para('zerosLChi5_bounded_finite（Z_T 有限：零点竖直高度的有界性，承载 RvM 计数）；'
         'pair_count_bound（(1:ℝ) 计数 ≤ Dcnt·N_L T：|Z_T| 的对数零点计数上界，门槛 1 < T0）。'
         '两条均计入残余命名 axiom 清单（数论件，真证挂聚合 mathlib Mathlib.olean）。')
add_h2('3.4  pair_const_eps_bias 组装同步')
add_para('组装点 pair_const_eps_bias 归一化同步：N := N_L T、Z := zerosLChi5UpTo T、门槛 1 ≤ T0 → 1 < T0；'
         'C₁ = 4M²·Dcnt（沿用增量⑦口径修正），Bound 仍 = ε。链：pairConst_sub_pairL1 → (2M/(N_L T))·tsg → hcnt → field_simp → '
         'f0_sub_feps_L1_bound → ring。')

add_h1('4  真证链（Stage3，行 763 起）')
add_h2('4.1  常量与可和性打包')
add_para('rcases pair_count_bound → Dcnt；M := (√2·|sin(1/√2)|)⁻¹；hMpos/hM0（M > 0 / 0 ≤ M，sin_inv_sqrt2_ne_zero 沿用）；'
         'hLpos := normL1_sub_pos（‖f₀−f_ε‖₁ > 0）；D := (2·M·Dcnt)/normL1；hD0（D ≥ 0）。')
add_h2('4.2  有限支撑件')
add_para('hfinZ/hfinP（支撑包含；可和性用 summable_of_finite_support——v4.34 中 Summable.of_finite_support 不存在，'
         '全文件替换，仅 deprecation warning 不阻断）；hsum_supp → hsum；hcnt_supp/hcnt_sum（计数项可和性）。')
add_h2('4.3  逐项界 hterm')
add_para('支撑内（|x| ∈ supp f₀）|f₀−f_ε| ≤ 2M（继承全局界，f_eps_abs_le/f0_abs_le）且计数项 = (1:ℝ)；'
         '支撑外 f₀/f_ε 为 0（f_eps_support/f0 截断），先证 (1/2) < δ|…| 再降 f₀、f_ε 为 0；'
         '计数 0/1 分支显式 rw [if_pos hz]/rw [if_neg hz] + change，hcnt1/hcnt0 显式声明。')
add_h2('4.4  hg_sum（Summable.of_norm_bounded）')
add_para('逐项界：|·| ≤ |a| + |b| + |c| 三项和——abs_of_nonneg (abs_nonneg _) 化掉外层嵌套 abs，'
         '结合/交换由 linarith 直接线性闭（第七轮唯一残留 error 的修复：原 calc 第二步 rw [← add_assoc] 报'
         '“Did not find an occurrence of the pattern ?a + (?b + ?c)”——结合方向判定错误，rw 匹配不上目标形态 '
         '|diff| ≤ |a| + |b| + |diff|；改 linarith 后闭合）。')
add_h2('4.5  组装：hle_sum / hle2 / hle3')
add_para('hle_sum（Summable.tsum_le_tsum 三参 (h)(hf)(hg)——v4.34 需第三个可和性实参）；'
         'hcnt_le（计数界挂钩）；hle2（tsum_mul_left + mul_le_mul_of_nonneg_left，补 (mul_nonneg (by norm_num : 0 ≤ 2) hM0)）；'
         'hle3（unfold D + hform（D 代回 (2·M·Dcnt)/normL1）+ le_div_iff₀ hLpos（v4.34：le_div_iff/le_div_iff\' 为 submodule/filter 引理，'
         '实数除法用 le_div_iff₀ (hc : 0 < c) : a ≤ b/c ↔ a·c ≤ b）+ ring_nf + exact le_rfl）；'
         '最终 exact ⟨hsum, le_trans hle2 hle3⟩。')
add_h2('4.6  常量明细')
add_math_para('D = 2M·Dcnt / ‖f₀−f_ε‖₁,  M = (√2·|sin(1/√2)|)⁻¹,  Bound = ε')
add_para('‖f₀−f_ε‖₁ ≤ 2εM 为增量⑤ f0_sub_feps_L1_bound 真证结果（‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹）。')

add_h1('5  v4.34 引理名勘误（本轮新踩）')
add_para('import 路径：Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic（v4.34 目录拆分后旧全名不存在）+ 补 MeasureTheory.Measure.Restrict。')
add_para('Continuous.max / Continuous.min（continuous.max 不存在；Topology/Order/OrderClosed.lean:696 protected）——w_eps 连续性构造（行 731 助手）。')
add_para('Set.uIoo（intervalIntegral.uIoo 不存在）——uIoo 切回 Ioo：simpa [Set.uIoo, min_eq_left, max_eq_left]（行 743–744）。')
add_para('MeasureTheory.Measure.restrict_le_self（namespace Measure，MeasureTheory/Measure/Restrict.lean:141）。')
add_para('le_div_iff₀（Algebra/Order/GroupWithZero/Basic.lean:1130，(hc : 0 < c) : a ≤ b/c ↔ a·c ≤ b）；'
         'le_div_iff / le_div_iff\' 用于 submodule/filter，不是实数除法引理。')
add_para('MeasureTheory.integral_mono_measure 为 3 显式参引理（Bochner/Basic.lean:588，(hle : μ ≤ ν) (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν)）；'
         'hsub 处 hfi 落在 volume（hLHSint 收尾），原 .restrict 落错测度（753:6 类型不匹配即此），第三分支同步删除。')
add_para('Summable.of_finite_support → summable_of_finite_support（deprecation 警告非阻断）；'
         '计数项类型 ℕ → ℝ：then (1 : ℝ) else 0 全文件替换。')
add_para('N_L / N_L_lower_bound 前向引用（约 60 错群）→ 两条 axiom 定义块前移到 N2b 挂钩区之前，原位置留“定义已前移”注释。')

add_h1('6  构建验证')
add_para('单编轮次 stage3_pceb1.txt … stage3_pceb12.txt（多轮"单编 → 修错 → 再单编"逐类收口，含 import/前向引用/命名引理/组装四类）；'
         'stage3_pceb12.txt 空输出 = exit = 0，仅弃用 warning（if_pos → ite_eq_left、if_neg → ite_eq_right、'
         'summable_of_finite_support → summable_of_hasFiniteSupport，沿用惯例不阻断）。'
         '全量 lake build QRH → build_qrh_lake.txt：2719 jobs、exit = 0、0 error（较 2704 增 15 job：'
         'zerosLChi5UpTo def + 结构 axiom zerosLChi5_bounded_finite/pair_count_bound + 真证件）。')

add_h1('7  残余命名 axiom 状态表')
tbl = doc.add_table(rows=12, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('名称', '位置', '状态'),
    ('fourierCos_Khat', 'Core §4b', '连接件：fourierCos Khat = Khat 闭式，定义一致件'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS 引理 5 频域支撑，积分层件'),
    ('siegel_walfisz_chi5', 'Main', 'SW 定理 χ₅ 版，PNT-in-AP 量级'),
    ('landau_explicit_L', 'Main', 'Landau 显式公式 L 版；(L1b) 两件出账'),
    ('N_L', 'Stage3', '数论件：对数零点计数（S6/S7.1 §2 N_Z）'),
    ('N_L_lower_bound', 'Stage3', '数论件：计数下界'),
    ('zerosLChi5_bounded_finite', 'Stage3', '数论结构件（本轮新增）：Z_T 有限'),
    ('pair_count_bound', 'Stage3', '数论结构件（本轮新增）：(1:ℝ) 计数 ≤ Dcnt·N_L T'),
    ('n2_linkage', 'Stage3', '结构件，S7.4 定理 N2'),
    ('n3_remainder_uniform', 'Stage3', '结构件，S7.5 定理 N3'),
    ('pairCount_L1_bound', 'Stage3 N2b', '本轮出账；D = 2M·Dcnt/‖f₀−f_ε‖₁（axiom → theorem）'),
]
widths = [Cm(4.2), Cm(2.6), Cm(9.2)]
for row in tbl.rows:
    for j, cell in enumerate(row.cells):
        cell.width = widths[j]
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

add_para('注：上表为 2026-10-31 快照。pairCount_L1_bound 出账后，pair_const_eps_bias 组装（增量⑦）的全部积分层输入为真证定理'
         '（f0_sub_feps_L1_bound 增量⑤ / khat_lipschitz 增量⑥ / pair_const_eps_bias 增量⑦ / pairCount_L1_bound 增量⑧）；'
         '残余最近攻坚件为 fourierCos_Khat（连接件）与 bgs5_khat_fourier_supp（积分层窄支撑，挂聚合），Stage3 数论件六条（含本轮新增两条结构 axiom）。', indent=True)

doc.save(OUT)
print('saved:', OUT)
