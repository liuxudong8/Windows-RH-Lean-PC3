# -*- coding: utf-8 -*-
"""S7.13 English archive generation: khat_lipschitz true proof - S_smooth extension"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.13-khat_lipschitz-true-proof-S_smooth-extension-EN.docx"

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

add_title('Offensive XLII-S7.13: khat_lipschitz true proof — S_smooth singularity extension and the L-derivative item')
add_meta('(smoothness/derivative-layer item · 2026-10-30 · d1 archive convention)')

add_h1('1  Summary of conclusions')
add_para('This round completes the last smoothness-layer item of the QRH Lean formalization project (C:\\proj2\\QRH): the named axiom khat_lipschitz is demoted from axiom to a true theorem, and the original axiom is deleted. '
         'The essential prior convention fix: the original axiom statement is false under the original closed form of Khat — '
         '(sin((√2−2πu)/2)/(√2−2πu) + sin((√2+2πu)/2)/(√2+2πu))/(√2·sin(1/√2)) has denominator zero at u = ±√2/(2π) in both sine terms; '
         'the Lean real-division convention returns 0 there, whereas the analytic extension is 1/2, so the Lipschitz inequality fails at those points. '
         'The fix introduces S_smooth (removable-singularity extension: 1/2 at x = 0, else sin(x/2)/x) and rewrites Khat with the new closed form; the original axiom khat_lipschitz is deleted.')
add_para('Explicit constant: L = π/(√2·|sin(1/√2)|) ≈ 3.42. Proof chain = Core §3b S_smooth items, about 12 (mean-value triples, '
         'S_smooth_hasDerivAt_zero by the sandwich slope convention, S_smooth_deriv_bound with |deriv S_smooth| ≤ 1/4, S_smooth_lipschitz_1_4) '
         '+ §3c khat items, 3 (khat_hasDerivAt with the four-step quotient-rule domain simplification, khat_deriv_bound with ‖deriv K̂ u‖ ≤ π/(√2·|sin(1/√2)|), '
         'khat_lipschitz assembled via Convex.norm_image_sub_le_of_norm_deriv_le); Stage3 Khat_closed_form adapted to the new definition (two S_smooth expansion items).')
add_para('Full build: lake build QRH — 2704 jobs, exit = 0, 0 errors, 0 warnings (dbg_build_khat.txt; Core solo build core_khat10.txt exit = 0). '
         'Axiom count decreases by 1: the only remaining named axioms are fourierCos_Khat (connector; consistency item) + bgs5_khat_fourier_supp (integral-layer narrow support); '
         'in prime_weight_bounds_Khat the L argument of M = L·δ + B is now a proven constant, so that chain has no axiom gap.')

add_h1('2  Background and positioning')
add_h2('2.1  Role of khat_lipschitz in the S7.1 formalization')
add_para('prime_weight_bounds_Khat (S7.10 demotion) needs smoothness of the prime-weight coefficients b_n: |b_n| ≤ M·(√n)⁻¹ and the difference bound |Δb_n| ≤ M·n^(−3/2), '
         'with M = L·δ + B; L is the Lipschitz constant of the pairing kernel K̂ = Khat and B comes from khat_global_bound (global uniform bound |K̂u| ≤ (√2·|sin(1/√2)|)⁻¹). '
         'Previously khat_lipschitz was a named axiom (statement: ∃L, 0 ≤ L ∧ ∀u v, |Khat u − Khat v| ≤ L·|u−v|); L is computable from the closed form but was not formalized.')
add_h2('2.2  Axiom backlog')
add_para('Core §4b originally held three named axioms: fourierCos (carrier; demoted to a Bochner true definition on 2026-10-29), fourierCos_Khat (connector: fourierCos Khat = Khat closed form), '
         'khat_lipschitz (smoothness). After S7.12, the smoothness item was the closest outstanding one; this document clears khat_lipschitz.')
add_h2('2.3  Diagnosis: the original statement is false')
add_para('The original axiom statement is false under the original closed form of Khat. The closed form contains sin((√2−2πu)/2)/(√2−2πu) and sin((√2+2πu)/2)/(√2+2πu): '
         'at u = ±√2/(2π) the denominators √2−2πu and √2+2πu vanish respectively; mathematically these are removable base-frequency singularities (limit 1/2), '
         'but Lean real division returns 0 at a zero denominator, so in Lean semantics K̂(±√2/(2π)) = 0 while neighbouring values tend to the nonzero ±(√2·sin(1/√2))⁻¹·(1/2) — '
         'the Lipschitz inequality fails across those points, so the statement is false. Following the established pattern of S7.9/S7.11/S7.12: fix the convention first, then prove.')

add_h1('3  Convention fix: S_smooth singularity extension')
add_h2('3.1  Definitions')
add_math_para('S_smooth x = if x = 0 then 1/2 else sin(x/2)/x')
add_math_para('Khat u = (S_smooth (√2−2πu) + S_smooth (√2+2πu)) / (√2·sin(1/√2))')
add_para('S_smooth is the removable-singularity extension of sin(x/2)/x: lim_{x→0} sin(x/2)/x = 1/2. Khat is continued termwise at u = ±√2/(2π) '
         '(each term contributes 1/2·(√2·sin(1/√2))⁻¹), well defined on the whole real axis.')
add_h2('3.2  Existing items')
add_para('Khat_neg (evenness), Khat_zero (K̂(0) = 1) and Khat_abs_le (frequency-decay triangle-inequality bound, with the h1/h2 non-singularity premises) '
         'are adapted and compile under the new definition; the original axiom khat_lipschitz is deleted. The denominator well-definedness item sin_inv_sqrt2_ne_zero is reused; √2 ≠ 0 by positivity.')

add_h1('4  True-proof chain: Core §3b/§3c')
add_h2('4.1  Mean-value triples')
add_para('abs_cos_sub_one_le_sq_of_nonneg (|cos t − 1| ≤ t²), abs_sin_sub_id_le_cube_of_nonneg (|sin t − t| ≤ t³), '
         'abs_sin_sub_mul_cos_le_sq (|sin t − t·cos t| ≤ t²): each is proved on the segment [0, s] via mathlib Convex.norm_image_sub_le_of_norm_deriv_le, '
         'with all arguments fully named (scalar field ℝ, G := ℝ, f := …, s := Set.Icc 0 s, C := …, x := x, y := y; the scalar-field parameter is mathlib\'s k), '
         'the pointwise inequality argument (fun x _ => hdiff x), and the output direction |y − x| ≤ … always closed by simpa [Real.norm_eq_abs, abs_sub_comm]. '
         'All derivative items use the same-shape-declaration + simpa pattern (not convert — convert drags out typeclass equality goals).')
add_h2('4.2  S_smooth_hasDerivAt_zero (sandwich slope convention)')
add_para('After rw [hasDerivAt_iff_tendsto_slope] the goal becomes Tendsto (fun y => slope S_smooth 0 y) (nhds[≠0] 0) (nhds 0) (nhds is the mathlib neighbourhood-filter notation). '
         'hbound: ‖slope S_smooth 0 y‖ ≤ |y|/8 — the hslope rewrite chain is unfold slope + rw [sub_zero] + smul_eq_mul + mul_comm + rfl '
         '(the difference on ℝ is VSub, so ring is unusable; the rewrite must be item-by-item). '
         'Upper/lower bounds via tendsto_of_tendsto_of_tendsto_of_le_of_le: the lower bound tendsto_const_nhds (must be in term mode with the full type annotation; exact inside a by block leaves a metavariable), '
         'the upper bound hconv (first h1.mul h2 on nhds 0, then h0.mono_left (inf_le_left : nhds[{0}ᶜ] ≤ nhds 0)); '
         'the midpoint function is norm_nonneg (argument name a, not x; it binds only y, not x ∈ univ). Finally exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm.')
add_h2('4.3  S_smooth_deriv_bound and S_smooth_lipschitz_1_4')
add_para('|deriv S_smooth x| ≤ 1/4: at x = 0 the derivative is 0 (sandwich item); for x ≠ 0 the quotient derivative bound follows from |sin t − t cos t| ≤ t². '
         'S_smooth_lipschitz_1_4 is assembled by Convex.norm_image_sub_le_of_norm_deriv_le (fully named arguments + abs_sub_comm).')
add_h2('4.4  khat_hasDerivAt (four-step quotient-rule domain simplification)')
add_para('The composite chain is hsum = hd1.add hd2 (S_smooth ∘ linear items, derivatives d1 = deriv S_smooth (√2−2πu)·(−2π) and d2 = deriv S_smooth (√2+2πu)·(2π)); '
         'after the quotient rule hsum.div hc hdiv the target derivative is 2π(d2−d1)/c, with hc : HasDerivAt (fun _ => c) 0 and hdiv : c ≠ 0 (c = √2·sin(1/√2)). '
         'The domain simplification avoids convert and proceeds in two steps: h_eq1 is a pure-ring proof of 2π(d2−d1) = d1·(−2π) + d2·(2π); '
         'h_eq2 is an inverse chain — hcc : c⁻¹ = c·c⁻¹^2 via rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hdiv, one_mul], '
         'then rw [div_eq_mul_inv], rw [hcc], rw [← mul_assoc], rw [show (f′·c − f·0) = f′·c by ring]; '
         'finally h_div is declared separately as (f′·c)/c² = (f′·c)·c⁻¹^2 (rw [div_eq_mul_inv] + rw [← inv_pow]) — '
         'rw [← inv_pow] must act on the separate declaration: on the main goal directly the RHS still displays as /c², so the pattern (?a ^ ?n)⁻¹ is not found. '
         'Finally rw [h_eq1, h_eq2] then exact hd.')
add_h2('4.5  khat_deriv_bound')
add_para('‖deriv Khat u‖ ≤ π/(√2·|sin(1/√2)|): after rw [hd.deriv], with hpos : 0 < √2·|sin(1/√2)|, the numerator is tightened to ≤ π '
         'by S_smooth_deriv_bound + norm_mul_le + norm_sub_le triangle inequalities.')
add_h2('4.6  khat_lipschitz assembly')
add_math_para('khat_lipschitz : ∃ L, 0 ≤ L ∧ ∀ u v, |Khat u − Khat v| ≤ L * |u − v|')
add_para('Take L = π/(√2·|sin(1/√2)|). Assembly: Convex.norm_image_sub_le_of_norm_deriv_le '
         '(scalar field ℝ, G := ℝ, f := Khat, s := Set.univ, C := π/(√2·|sin(1/√2)|), x := u, y := v, '
         'fun x _ => hdiff x, fun x _ => hb x, convex_univ, trivial, trivial) → simpa [Real.norm_eq_abs, abs_sub_comm] using hres.')

add_h1('5  Stage3 adaptation: Khat_closed_form')
add_para('In Khat_closed_form (the closed-form item of khat_second_order_bound), before rw [hA, hB] (the sine-angle replacement (√2±2πu)/2 → √2/2 ± πu) one must first expand S_smooth: '
         'two items hsa/hsb (unfold S_smooth + rw [ite_eq_right hd1 / ite_eq_right hd2], hd1 : √2−2πu ≠ 0, hd2 : √2+2πu ≠ 0) '
         'rewrite S_smooth (√2±2πu) to sin((√2±2πu)/2)/(√2±2πu); the rest of the closed-form chain (field_simp, Real.sin_sub/sin_add, sqrt2_div_two_eq_inv, ring_nf, hsq) is untouched.')

add_h1('6  Build verification')
add_para('Core solo-build rounds core_khat1.txt … core_khat10.txt (about 30 errors at first instrumentation, closed category by category); core_khat10.txt empty output = exit = 0. '
         'Full build: lake build QRH — 2704 jobs, exit = 0, 0 errors, 0 warnings (dbg_build_khat.txt; '
         'Main L1027 and Stage3 L914 each carry one ring_nf "Try this" info suggestion, not an error/warning, same as S7.10–S7.12). '
         'Deprecation cleanup follows the established convention: if_neg/if_pos/Set.mem_setOf_eq → ite_eq_right/ite_eq_left/Set.mem_ofPred_eq.')

add_h1('7  Outstanding named axiom table')
tbl = doc.add_table(rows=9, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('Name', 'Location', 'Status'),
    ('fourierCos_Khat', 'Core §4b', 'connector: fourierCos Khat = Khat closed form, consistency item'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS Lemma 5 frequency support, integral-layer item'),
    ('siegel_walfisz_chi5', 'Main', 'SW theorem for χ₅, PNT-in-AP scale'),
    ('landau_explicit_L', 'Main', 'Landau explicit formula L-version; (L1b) two items cleared'),
    ('N_L_lower_bound', 'Stage3', 'structural item, S6 zero counting'),
    ('n2_linkage', 'Stage3', 'structural item, S7.4 Theorem N2'),
    ('n3_remainder_uniform', 'Stage3', 'structural item, S7.5 Theorem N3'),
    ('khat_lipschitz', 'Core §4b', 'cleared this round; explicit L ≈ 3.42 (axiom → theorem)'),
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

add_para('Note: the table is a 2026-10-30 snapshot. fourierCos / fourierCos_scale / f0_sub_feps_L1_bound / prime_weight_bounds_Khat / khat_lipschitz are cleared; '
         'after khat_lipschitz, the M = L·δ + B of prime_weight_bounds_Khat is fully made of proven constants; '
         'the closest remaining items are fourierCos_Khat (connector) and bgs5_khat_fourier_supp (integral-layer narrow support, pending aggregate).')

doc.save(OUT)
print('saved:', OUT)
