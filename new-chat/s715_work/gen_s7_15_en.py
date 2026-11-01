# -*- coding: utf-8 -*-
"""S7.15 English archive generation: n2_linkage true proof - the eps-lambda linkage and axiom demotion"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.15-n2_linkage-true-proof-eps-lambda-linkage-EN.docx"

doc = Document()
sec = doc.sections[0]
sec.page_width = Cm(21.0)
sec.page_height = Cm(29.7)
sec.top_margin = Cm(2.5)
sec.bottom_margin = Cm(2.5)
sec.left_margin = Cm(2.5)
sec.right_margin = Cm(2.5)

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

def add_math_para(text):
    p = doc.add_paragraph()
    p.paragraph_format.first_line_indent = Cm(0)
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    r = p.add_run(text)
    set_run(r, cn='宋体', size=12)
    return p

add_title('Offensive XLII-S7.15: n2_linkage true proof — the ε–λ linkage and axiom demotion')
add_meta('(ε–λ linkage item · 2026-10-31 · d1 archive convention)')

add_h1('1  Summary of conclusions')
add_para('This round closes the last link of Theorem N2(iii) (the ε–λ linkage) of S7.4 in the QRH Lean formalization project (C:\\proj2\\QRH): '
         'the named axiom n2_linkage is demoted from axiom to a true theorem, the original axiom is deleted, and the proof block lands in '
         'S7_1_Stage3.lean (theorem n2_linkage, now line 610; the new auxiliary block about lines 434–640). '
         'Statement: for λ=(logT)^q, a=(logT)^{−q}, ε=c·(logT)^{−q}, the integral deviation of the Fourier transform of f_ε against f₀ '
         'closes at O((logT)^{−q}) with the explicit constant C=2cM, where M=(√2·|sin(1/√2)|)⁻¹.')
add_para('Mathematical chain (three steps): (i) reduction — cos(2π·0·x)=1, so fourierCos at z=0 degenerates to the full-space Bochner integral ∫f '
         '(the true definition of fourierCos Core:699 + the lemma cos_zero, against the background of the true proof of the scaling law '
         'fourierCos_scale, S7.12); (ii) deviation bound — |∫(f_ε−f₀)| ≤ ‖f₀−f_ε‖₁, i.e. MeasureTheory.norm_integral_le_integral_norm '
         '(the v4.34 full-space Bochner absolute bound) together with integral_sub and the triangle inequality; integrability is supplied by '
         'four new auxiliary items of this round; (iii) ε–λ closure — ‖f₀−f_ε‖₁ ≤ 2εT·M is the increment ⑤ true proof f0_sub_feps_L1_bound, '
         'with εT := c·exp(−q·log(logT)); substituting and expanding (unfold εT C M + ring) gives |deviation| ≤ 2εT·M = 2cM·(logT)^{−q} = C·(logT)^{−q}.')
add_para('No convention was changed this round; this is a pure clearing: n2_linkage is the closing item of the N2 assembly integral layer, '
         'and all its inputs (f0_sub_feps_L1_bound increment ⑤ / khat_lipschitz increment ⑥ / pair_const_eps_bias increment ⑦ / '
         'pairCount_L1_bound increment ⑧) were already true proofs, so this round adds zero axioms and zero convention fixes.')
add_para('Build evidence: solo build stage3_n2.txt empty output = exit = 0 (only the historical existing warnings: '
         'if_pos/if_neg→ite_eq, unnecessarySimpa, ring→ring_nf and similar info-class warnings, following the non-blocking convention); '
         'full build lake build → build_qrh_lake.txt: 7690 jobs, exit = 0, 0 errors (Build completed successfully (7690 jobs), '
         'covering the whole C:\\proj2 project, not only the QRH module; 4103 log lines, error: 0).')
add_para('Ledger update: the attack list at the end of S7_1_Stage3.lean (about lines 2070–2102) moves n2_linkage out of the axiom bucket into '
         'the true-proof column, and the residual named axioms drop from six to five '
         '(n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound); '
         'the status of the f0_sub_feps_L1_bound entry, which was inconsistent with the facts, is corrected in the same pass; '
         'QRH_summary.md / QRH_summary_en.md increment ⑨ is in place (three sites each in Chinese and English: header increment block, '
         '§5 outstanding ledger, next-step item), true-proof clearing 13→14 items; task #75 done.')

add_h1('2  Background and positioning')
add_h2('2.1  Role of n2_linkage in the N2 assembly')
add_para('Theorem N2 of S7.4 (the ε–λ linkage) states the scaling law between the regularization width ε and the effective kernel width λ: '
         'λ=(logT)^q, a=(logT)^{−q}, ε=c·(logT)^{−q}, under which the total deviation of the Fourier-transform layer decays like (logT)^{−q}. '
         'n2_linkage was originally a named axiom packing three items: integrability, the absolute bound, and the explicit ε–λ constant. '
         'The assembly inputs (the true definition of fourierCos Core:699, the true proof of fourierCos_scale, the L¹ bound f0_sub_feps_L1_bound) '
         'were already in place; the only gap was the integrability construction and the deviation chain of n2_linkage itself.')
add_h2('2.2  The three packed items of the original axiom')
add_para('The original axiom statement packed three items: ① the absolute bound of |∫(f_ε−f₀)|; ② Bochner integrability of the involved '
         'functions; ③ the explicit constant of the Bound form |deviation| ≤ C·f(T). This round converts all three into true proofs; '
         'no vacuous axiom→axiom renaming.')
add_h2('2.3  Established pattern')
add_para('Continuing the project convention: fix the convention first, then prove; a true proof only demotes, never keeps a renamed axiom. '
         'Since all conventions were already closed in the previous increments (f0 support truncation, pairCount truncated zero set, '
         'khat singularity extension), n2_linkage is cleared directly.')

add_h1('3  True-proof chain (Stage3, theorem n2_linkage now :610)')
add_h2('3.1  Signature and premises')
add_math_para('n2_linkage : (T0 c q : ℝ) → (_hT0 : 1 < T0) → (_hq : 0 < q) → (hc : 0 < c) → Bound item')
add_para('hT0/hq are not referenced in the proof and were renamed with an underscore prefix (_hT0, _hq) to suppress the warnings; '
         'hc drives the strict positivity of εT.')
add_h2('3.2  Main chain (three-step calc)')
add_math_para('|∫(f_ε−f₀)| ≤ ‖f₀−f_ε‖₁ ≤ 2εT·M = C·(logT)^{−q}')
add_para('C := 2·c·M; εT := c·Real.exp(−q·Real.log(Real.log T)); first Bound item 0 ≤ C := mul_nonneg (by positivity) hMpos.le; '
         'the calc closes with unfold εT C M + ring. M=(√2·|sin(1/√2)|)⁻¹ (the exact RHS of f0_abs_le, product-inverse form).')
add_h2('3.3  First step: the z=0 reduction')
add_para('At z=0, cos(2π·0·x)=1 and the integral becomes ∫ K(x)·f(x) dx in the Bochner sense; '
         'have hz : 2*Real.pi*0*x = 0 := by ring; rw [hz, cos_zero]. This step reduces the ε-deviation of the Fourier-transform layer to '
         'the integral deviation of the f-layer difference.')
add_h2('3.4  Second step: full-space integral absolute bound')
add_para('|∫(f_ε−f₀)| ≤ ∫|f₀−f_ε| = ‖f₀−f_ε‖₁: MeasureTheory.norm_integral_le_integral_norm (v4.34, full-space Bochner, no extra argument; '
         'note that abs_integral_le_integral_abs applies only to interval integrals, IntervalIntegral/Basic.lean:1395, not to the full space) '
         '+ integral_sub. Integrability (full-space Bochner): f0_integrable (compact-support bounded), f0_sub_feps_abs_integrable, '
         'f0_sub_feps_integrable (dominated by the L¹ bound of f0_sub_feps_L1_bound); the four auxiliary items live in block 3.6.')
add_h2('3.5  Third step: the ε–λ closure')
add_math_para('‖f₀−f_ε‖₁ ≤ 2εT·M,  εT = c·exp(−q·log(logT)) = c·(logT)^{−q}')
add_para('f0_sub_feps_L1_bound (true proof) gives ‖f₀−f_ε‖₁ ≤ 2ε·(√2·|sin(1/√2)|)⁻¹; substituting ε=εT and expanding the log layer '
         '(unfold εT C M + ring) yields 2εT·M = 2cM·(logT)^{−q}.')
add_h2('3.6  The four new auxiliary items (block about lines 434–640)')
add_para('f0_integrable: f0 has compact support (0 outside |x|≤1/2) and is bounded, hence Bochner integrable; the core construction is '
         'hMint := IntegrableOn (indicator I M) I (in v4.34 IntegrableOn unfolds to Integrable f0 (volume.restrict I), via '
         'integrableOn_const + IntegrableOn.congr_fun + isClosed_Icc.measurableSet; strong measurability via f0_measurable.aestronglyMeasurable.restrict).')
add_para('f0_sub_feps_abs_integrable / f0_sub_feps_integrable: absolute and plain integrability of f₀−f_ε, by the measurability construction '
         '(f0_measurable.mul/sub, w_eps_continuous.measurable, aestronglyMeasurable_iff_aemeasurable) + Integrable.mono '
         '((hRHSint)(hLHSmeas) + filter_upwards pointwise bound) carrying the L¹ bound; hfeint reduces via convert hsub using 1; ext x; change …; ring.')
add_para('fourierCos_sub_f0_feps_abs_le: the absolute-bound assembly between the first and second steps of the main chain, reusing the '
         'proof-block pattern of f0_sub_feps_L1_bound verbatim '
         '(hfepsm/hdiffm/hLHSmeas/hRHSint/hLHSint, indicator_Icc_integral, f0_abs_le, integrableOn_iff_integrable_of_support_subset).')
add_para('After the insertion point, old line numbers shift by about +200 (pair_const_eps_bias 1125 → about 1325); before it they are unchanged: '
         'w_eps_continuous 137, indicator_Icc_integral 158, f0_sub_feps_abs_le 167, f0_sub_feps_L1_bound 261, f_eps_abs_le 474.')

add_h1('4  Eight solo-build rounds (v4.34 lemma corrections)')
add_para('Round 1: abs_le_iff unknown → split the absolute bound by hand with le_abs_self / neg_le; Function.support is a member-function type '
         '(exact hy hy0, no mem_support.mpr); Integrable.of_norm does not exist → use Integrable.mono.')
add_para('Round 2: the hMint construction of f0_integrable settled (IntegrableOn unfolding convention + strong-measurability restrict); '
         'hfeint via convert hsub using 1; ext x; change …; ring.')
add_para('Round 3: Set.indicator_of_mem / notMem need the explicit second argument; mem_support.mpr unknown → use hsupp hne directly.')
add_para('Round 4: rw [Real.norm_eq_abs] does not match → switch to a calc chain unfolding by hand; Round 5: simpa likewise does not match.')
add_para('Round 6 (the only hard blocker of this round): the definition of M was first changed in the wrong direction — intuited as the '
         'factor-wise inverse form (√2)⁻¹·|sin(1/√2)|⁻¹; Grep at S7_1_Core.lean:658 confirmed the true RHS of f0_abs_le is '
         '(sqrt 2 * |sin (1 / sqrt 2)|)⁻¹ (product-inverse form, not factor-wise), and M was changed back to the same shape.')
add_para('Round 7: the calc chain finalized — ‖f0 x‖=|f0 x| := rfl; |f0 x| ≤ M := f0_abs_le x; M=|M| := rw [abs_of_nonneg hMpos.le]; '
         '|M|=‖M‖ := rfl; ‖M‖=‖indicator‖ := rw [hxM].')
add_para('Round 8: exit=0. After the comment update, the solo build was rerun and still reports 0 errors.')

add_h1('5  Build verification')
add_para('Solo build: lake build QRH.S7_1_Stage3 → stage3_n2.txt: 2717 jobs, Build completed successfully, 0 errors '
         '(only the historical existing warnings: if_pos/if_neg→ite_eq, unnecessarySimpa, ring→ring_nf and similar info-class warnings, '
         'following the non-blocking convention).')
add_para('Full build: lake build → build_qrh_lake.txt: 7690 jobs all green (the whole C:\\proj2 project, not only the QRH module; '
         'Build completed successfully (7690 jobs); 4103 log lines, error: 0). The solo build was rerun after the comment update, '
         'covering the latest file state with 0 errors.')

add_h1('6  Outstanding named axiom table')
tbl = doc.add_table(rows=11, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('Name', 'Location', 'Status'),
    ('fourierCos_Khat', 'Core §4b', 'connector: fourierCos Khat = Khat closed form, consistency item'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS Lemma 5 frequency support, integral-layer item'),
    ('siegel_walfisz_chi5', 'Main', 'SW theorem for χ₅, PNT-in-AP scale'),
    ('landau_explicit_L', 'Main', 'Landau explicit formula L-version; (L1) long-line attack in progress'),
    ('N_L', 'Stage3', 'number-theory item: logarithmic zero count (S6 / S7.1 §2 N_Z)'),
    ('N_L_lower_bound', 'Stage3', 'number-theory item: lower bound of the count'),
    ('zerosLChi5_bounded_finite', 'Stage3', 'number-theory structure item (new, increment ⑧): Z_T finite'),
    ('pair_count_bound', 'Stage3', 'number-theory structure item (new, increment ⑧): count (1:ℝ) ≤ Dcnt·N_L T'),
    ('n3_remainder_uniform', 'Stage3', 'structural item, S7.5 Theorem N3'),
    ('n2_linkage', 'Stage3', 'cleared this round: S7.4 Theorem N2(iii), C=2cM, M=(√2|sin(1/√2)|)⁻¹ (axiom → theorem)'),
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

add_para('Note: the table is a 2026-10-31 snapshot. After n2_linkage, every input of the ε–λ linkage chain of S7.4 Theorem N2 is a true theorem '
         '(f0_sub_feps_L1_bound increment ⑤ / khat_lipschitz increment ⑥ / pair_const_eps_bias increment ⑦ / pairCount_L1_bound increment ⑧ / '
         'n2_linkage increment ⑨); the closest remaining items are fourierCos_Khat (connector) and bgs5_khat_fourier_supp '
         '(integral-layer narrow support, pending aggregate), plus the five Stage3 number-theory items '
         '(n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound).')

doc.save(OUT)
print('saved:', OUT)
