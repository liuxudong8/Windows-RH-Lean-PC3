# -*- coding: utf-8 -*-
"""S7.15 中文落档生成：路2攻防XLII-S7.15-n2_linkage真证-ε-λ联动与axiom降定理"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.15-n2_linkage真证-ε-λ联动与axiom降定理.docx"

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

add_title('路 2 攻防 XLII-S7.15：n2_linkage 真证——ε–λ 联动与 axiom 降定理')
add_meta('（ε–λ 联动件 · 2026-10-31 · 落档 d1 惯例）')

add_h1('1  结论摘要')
add_para('本轮完成 QRH Lean 形式化项目（C:\\proj2\\QRH）S7.4 定理 N2(iii)（ε–λ 联动）的最后一环：命名 axiom n2_linkage 由 axiom '
         '降为真证定理，原 axiom 删除，真证块落于 S7_1_Stage3.lean（theorem n2_linkage，现第 610 行；新增辅助件块约第 434–640 行）。'
         '陈述：对 λ=(logT)^q、a=(logT)^{−q}、ε=c·(logT)^{−q}，fourierCos 对 f_ε 与 f₀ 的积分偏差以 O((logT)^{−q}) 收口，'
         '显式常数为 C=2cM，其中 M=(√2·|sin(1/√2)|)⁻¹。')
add_para('数学链（三段）：(i) 化归——cos(2π·0·x)=1，fourierCos 在 z=0 处退化为 Bochner 全空间积分 ∫f'
         '（fourierCos 真定义 Core:699 + 引理 cos_zero，smooth 核 K 之 Fourier 变换在原点即 ∫K·f，见 S7.12 缩放律 fourierCos_scale 的真证背景）；'
         '(ii) 偏差控制——|∫(f_ε−f₀)| ≤ ‖f₀−f_ε‖₁，即 MeasureTheory.norm_integral_le_integral_norm（v4.34 全空间 Bochner 积分绝对界）'
         '配合 integral_sub 与三角不等式；可积性由本轮新增四个辅助件供足；'
         '(iii) ε–λ 收口——‖f₀−f_ε‖₁ ≤ 2εT·M 为增量⑤ f0_sub_feps_L1_bound 真证结果，εT := c·exp(−q·log(logT))，'
         '代入并展开（unfold εT C M + ring）得 |偏差| ≤ 2εT·M = 2cM·(logT)^{−q} = C·(logT)^{−q}。')
add_para('本轮未改任何口径，纯出账：n2_linkage 为 N2 组装积分层的收口件，其输入（f0_sub_feps_L1_bound 增量⑤ / khat_lipschitz 增量⑥ / '
         'pair_const_eps_bias 增量⑦ / pairCount_L1_bound 增量⑧）此前均已真证，故本轮零新 axiom、零口径修正。')
add_para('编译证据：单编 stage3_n2.txt 空输出 = exit = 0（仅历史既有 warning：if_pos/if_neg→ite_eq、unnecessarySimpa、ring→ring_nf 等 info 类，'
         '沿用惯例不阻断）；全量 lake build → build_qrh_lake.txt：7690 jobs、exit = 0、0 error（Build completed successfully (7690 jobs)，'
         '含 C:\\proj2 整个工程，不限于 QRH 模块；日志 4103 行，error: 0）。')
add_para('账目更新：S7_1_Stage3.lean 末尾击破清单（约第 2070–2102 行）将 n2_linkage 移出 axiom 桶入真证栏，'
         '残余命名 axiom 六件→五件（n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound），'
         '顺带修正 f0_sub_feps_L1_bound 项状态与实际不符；QRH_summary.md / QRH_summary_en.md 增量⑨已落（中英各三处：头部增量块、§5 挂账清单、'
         '下一步条目），真证出账 13→14 件；task #75 完成。')

add_h1('2  背景与定位')
add_h2('2.1  n2_linkage 在 N2 组装中的角色')
add_para('S7.4 定理 N2（ε–λ 联动）陈述：正则化撑宽 ε 与有效核宽 λ 之间存在标度律——λ=(logT)^q，a=(logT)^{−q}，ε=c·(logT)^{−q}，'
         '在此标度下 Fourier 变换层的总偏差以 (logT)^{−q} 衰减。n2_linkage 原为命名 axiom，打包可积性、绝对界与 ε–λ 显式常量三件事；'
         '此前的组装输入（fourierCos 真定义 Core:699、缩放律 fourierCos_scale 真证、L¹ 界 f0_sub_feps_L1_bound）已就绪，'
         '缺口仅在 n2_linkage 自身的可积性构造与偏差链。')
add_h2('2.2  原 axiom 的三件打包')
add_para('原 axiom 陈述含三件：① |∫(f_ε−f₀)| 的绝对界存在；② 相关函数 Bochner 可积；③ Bound 形式 |偏差| ≤ C·f(T) 的显式常量。'
         '本轮全部转为真证，无 axiom→axiom 空换名。')
add_h2('2.3  既定模式')
add_para('延续项目惯例：先修口径、再真证；真证只降级、不保留改名 axiom。本轮口径已在前置增量全部闭合（f0 支撑截断、pairCount 截断零点集、'
         'khat 奇点延拓），故 n2_linkage 直接出账。')

add_h1('3  真证链（Stage3，theorem n2_linkage 现 :610）')
add_h2('3.1  签名与前提')
add_math_para('n2_linkage : (T0 c q : ℝ) → (_hT0 : 1 < T0) → (_hq : 0 < q) → (hc : 0 < c) → Bound 件')
add_para('hT0/hq 未在证明中引用，已改名下划线前缀（_hT0、_hq）消警告；hc 驱动 εT 的严格正性。')
add_h2('3.2  主链（calc 三段）')
add_math_para('|∫(f_ε−f₀)| ≤ ‖f₀−f_ε‖₁ ≤ 2εT·M = C·(logT)^{−q}')
add_para('C := 2·c·M；εT := c·Real.exp(−q·Real.log(Real.log T))；Bound 首件 0 ≤ C := mul_nonneg (by positivity) hMpos.le；'
         'calc 末端 unfold εT C M + ring 闭合。M=(√2·|sin(1/√2)|)⁻¹（f0_abs_le 真实 RHS，乘积 inv 形）。')
add_h2('3.3  第一步：z=0 化归')
add_para('fourierCos 在 z=0 处 cos(2π·0·x)=1，积分化为 ∫ K(x)·f(x) dx（Bochner 意义）；'
         'have hz : 2*Real.pi*0*x = 0 := by ring; rw [hz, cos_zero]。此步将 Fourier 变换层对 ε 的偏差归约为 f 层差分的积分偏差。')
add_h2('3.4  第二步：全空间积分绝对界')
add_para('|∫(f_ε−f₀)| ≤ ∫|f₀−f_ε| = ‖f₀−f_ε‖₁：MeasureTheory.norm_integral_le_integral_norm（v4.34，全空间 Bochner，无附加参数；'
         '注意 abs_integral_le_integral_abs 仅适用于区间积分 IntervalIntegral/Basic.lean:1395，不可用于全空间）+ integral_sub。'
         '可积性（Bochner 全空间）：f0_integrable（紧支撑有界）、f0_sub_feps_abs_integrable、f0_sub_feps_integrable'
         '（由 f0_sub_feps_L1_bound 的 L¹ 界压制），四辅助件块见 3.6。')
add_h2('3.5  第三步：ε–λ 收口')
add_math_para('‖f₀−f_ε‖₁ ≤ 2εT·M，  εT = c·exp(−q·log(logT)) = c·(logT)^{−q}')
add_para('f0_sub_feps_L1_bound 真证结果 ‖f₀−f_ε‖₁ ≤ 2ε·(√2·|sin(1/√2)|)⁻¹；代入 ε=εT、展开对数层（unfold εT C M + ring）'
         '得 2εT·M = 2cM·(logT)^{−q}。')
add_h2('3.6  新增辅助件四件（块约第 434–640 行）')
add_para('f0_integrable：f0 紧支撑（|x|≤1/2 之外为 0）且有界，Bochner 可积；核心构造 hMint := IntegrableOn (indicator I M) I'
         '（v4.34 中 IntegrableOn 展开 = Integrable f0 (volume.restrict I)，由 integrableOn_const + IntegrableOn.congr_fun + '
         'isClosed_Icc.measurableSet；强可测 f0_measurable.aestronglyMeasurable.restrict）。')
add_para('f0_sub_feps_abs_integrable / f0_sub_feps_integrable：f₀−f_ε 的绝对可积与可积，由可测性构造'
         '（f0_measurable.mul/sub、w_eps_continuous.measurable、aestronglyMeasurable_iff_aemeasurable）+ Integrable.mono'
         '（(hRHSint)(hLHSmeas) + filter_upwards 点界）承接 L¹ 界；hfeint 用 convert hsub using 1; ext x; change …; ring 化归。')
add_para('fourierCos_sub_f0_feps_abs_le：主链第一步与第二步之间的绝对界组装，全部沿用 f0_sub_feps_L1_bound 证明块模式逐字复用'
         '（hfepsm/hdiffm/hLHSmeas/hRHSint/hLHSint、indicator_Icc_integral、f0_abs_le、integrableOn_iff_integrable_of_support_subset）。')
add_para('插入点后旧行号整体 +~200（pair_const_eps_bias 原 1125→现约 1325）；插入点前不变：w_eps_continuous 137、'
         'indicator_Icc_integral 158、f0_sub_feps_abs_le 167、f0_sub_feps_L1_bound 261、f_eps_abs_le 474。')

add_h1('4  八轮单编修复记账（v4.34 引理勘误）')
add_para('轮 1：abs_le_iff 未知 → 改 le_abs_self / neg_le 手工拆绝对界；Function.support 为成员函数型'
         '（exact hy hy0，无 mem_support.mpr）；Integrable.of_norm 不存在 → 用 Integrable.mono。')
add_para('轮 2：f0_integrable 的 hMint 构造落定（IntegrableOn 展开口径 + 强可测 restrict）；hfeint 用 convert hsub using 1; ext x; change …; ring。')
add_para('轮 3：Set.indicator_of_mem / notMem 需显式第二参数；mem_support.mpr 未知 → 直用 hsupp hne。')
add_para('轮 4：rw [Real.norm_eq_abs] 不匹配 → 改 calc 链手工展开；轮 5：simpa 同不匹配。')
add_para('轮 6（本轮唯一硬卡点）：误把 M 定义改错方向——先按直觉写成逐因子 inv 形 (√2)⁻¹·|sin(1/√2)|⁻¹，'
         'Grep S7_1_Core.lean:658 确认 f0_abs_le 真实 RHS 为 (sqrt 2 * |sin (1 / sqrt 2)|)⁻¹（乘积 inv 形，非逐因子 inv 形），'
         'M 改回同形后类型匹配恢复。')
add_para('轮 7：calc 链定型——‖f0 x‖=|f0 x| := rfl；|f0 x| ≤ M := f0_abs_le x；M=|M| := rw [abs_of_nonneg hMpos.le]；'
         '|M|=‖M‖ := rfl；‖M‖=‖indicator‖ := rw [hxM]。')
add_para('轮 8：exit=0。末轮（注释更新后）重跑单编仍 0 error。')

add_h1('5  构建验证')
add_para('单编：lake build QRH.S7_1_Stage3 → stage3_n2.txt：2717 jobs、Build completed successfully、0 error'
         '（仅历史既有 warning：if_pos/if_neg→ite_eq、unnecessarySimpa、ring→ring_nf info 类，沿用惯例不阻断）。')
add_para('全量：lake build → build_qrh_lake.txt：7690 jobs 全绿（含整个 C:\\proj2 工程，不限于 QRH 模块；'
         'Build completed successfully (7690 jobs)；日志 4103 行，error: 0）。注释更新后单编已重跑覆盖，最新文件状态 0 error。')

add_h1('6  残余命名 axiom 状态表')
tbl = doc.add_table(rows=11, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('名称', '位置', '状态'),
    ('fourierCos_Khat', 'Core §4b', '连接件：fourierCos Khat = Khat 闭式，定义一致件'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS 引理 5 频域支撑，积分层件'),
    ('siegel_walfisz_chi5', 'Main', 'SW 定理 χ₅ 版，PNT-in-AP 量级'),
    ('landau_explicit_L', 'Main', 'Landau 显式公式 L 版；(L1) 长线攻坚中'),
    ('N_L', 'Stage3', '数论件：对数零点计数（S6 / S7.1 §2 N_Z）'),
    ('N_L_lower_bound', 'Stage3', '数论件：计数下界'),
    ('zerosLChi5_bounded_finite', 'Stage3', '数论结构件（增量⑧新增）：Z_T 有限'),
    ('pair_count_bound', 'Stage3', '数论结构件（增量⑧新增）：(1:ℝ) 计数 ≤ Dcnt·N_L T'),
    ('n3_remainder_uniform', 'Stage3', '结构件，S7.5 定理 N3'),
    ('n2_linkage', 'Stage3', '本轮出账：S7.4 定理 N2(iii)，C=2cM，M=(√2|sin(1/√2)|)⁻¹（axiom → theorem）'),
]
widths = [Cm(4.2), Cm(2.6), Cm(9.2)]
for row in tbl.rows:
    for j, cell in enumerate(row.cells):
        cell.width = widths[j]
for i, row in enumerate(data):
    trPr = tbl.rows[i]._tr.get_or_add_trPr()
    cant = OxmlElement('w:cantSplit')
    trPr.append(cant)
    if i == 0:
        th = OxmlElement('w:tblHeader')
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

add_para('注：上表为 2026-10-31 快照。n2_linkage 出账后，S7.4 定理 N2 的 ε–λ 联动链全输入为真证定理'
         '（f0_sub_feps_L1_bound 增量⑤ / khat_lipschitz 增量⑥ / pair_const_eps_bias 增量⑦ / pairCount_L1_bound 增量⑧ / n2_linkage 增量⑨）；'
         '残余最近攻坚件为 fourierCos_Khat（连接件）与 bgs5_khat_fourier_supp（积分层窄支撑，挂聚合），'
         'Stage3 数论件五条（n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound）。', indent=True)

doc.save(OUT)
print('saved:', OUT)
