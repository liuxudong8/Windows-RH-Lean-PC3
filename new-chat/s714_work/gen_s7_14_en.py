# -*- coding: utf-8 -*-
"""S7.14 English archive generation: pairCount_L1_bound true proof - truncated zero set convention"""
import docx
from docx import Document
from docx.shared import Pt, Cm, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_LINE_SPACING
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

OUT = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\en\路2攻防XLII-S7.14-pairCount_L1_bound-true-proof-truncated-zero-set-convention-EN.docx"

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

add_title('Offensive XLII-S7.14: pairCount_L1_bound true proof — truncated zero-set convention and axiom demotion')
add_meta('(pairing-count L¹-bound item · 2026-10-31 · d1 archive convention)')

add_h1('1  Summary of conclusions')
add_para('This round completes the last integration-layer item of the N2b assembly in the QRH Lean formalization project (C:\\proj2\\QRH): '
         'the named axiom pairCount_L1_bound is demoted from axiom to a true theorem, the original axiom is deleted, and the proof block lands at line 763 of S7_1_Stage3.lean. '
         'The essential prior convention fix (user-approved plan, following the project pattern "fix the convention first, then prove" — '
         'the same pattern as the f0 support truncation, S7.9, S7.11 and S7.13): the original axiom statement had two flaws.')
add_para('Flaw (i) — zero set: zerosLChi5 is the full critical-strip zero set (infinite). The vertical-difference band window 2πε/logT '
         '(pairs with |Im z₁ − Im z₂| ≤ 2πε/logT) contains infinitely many pairings (the zero density ~ T·logT/(2π) is continuously distributed), '
         'so the discrete sum Σ_{z₁≠z₂} g(δΔ) is undefined on that infinite set and Summable is false — a fundamental defect.')
add_para('Flaw (ii) — normalization: the original RHS was D·δ·‖g‖₁, where δ = logT/(2π) is the pairing displacement scale rather than the zero count, '
         'inconsistent in magnitude/convention with respect to T; in the document layer S7.1 §2 the pairing-constant normalization N is the zero count N_Z(T).')
add_para('Four-part convention fix: ① truncate Z_T := zerosLChi5UpTo T (finite → the sum is a Finset sum); '
         '② statement ∃D ≥ 0, ∀T ≥ T0, Σ_{z₁≠z₂∈Z_T} |g(δ·Δ)| ≤ D·N_Z(T)·‖g‖₁ (normalization by the zero count N_Z replaces δ); '
         '③ two new number-theory structure axioms: zerosLChi5_bounded_finite (Z_T finite) and pair_count_bound (count (1:ℝ) ≤ Dcnt·N_L T, threshold 1 < T0); '
         '④ the pair_const_eps_bias assembly is synchronized to N := N_L T, Z := zerosLChi5UpTo T, threshold 1 ≤ T0 → 1 < T0, Bound still = ε.')
add_para('True-proof chain (Stage3): rcases pair_count_bound → M := (√2|sin(1/√2)|)⁻¹ → hMpos/hM0 → hLpos := normL1_sub_pos → '
         'D := (2·M·Dcnt)/normL1 → hD0 → hfinZ/hfinP (finite support) → hsum_supp/hsum, hcnt_supp/hcnt_sum → hterm (termwise bound) → '
         'hg_sum (Summable.of_norm_bounded) → hle_sum (Summable.tsum_le_tsum, three arguments) → hle2 → hle3 (unfold D + le_div_iff₀ + ring) → '
         '⟨hsum, le_trans hle2 hle3⟩.')
add_para('Explicit constants: D = 2M·Dcnt/‖f₀−f_ε‖₁, M = (√2·|sin(1/√2)|)⁻¹, Bound still = ε; '
         'here ‖f₀−f_ε‖₁ ≤ 2εM is the increment ⑤ true proof f0_sub_feps_L1_bound.')
add_para('Build evidence: solo build stage3_pceb12.txt empty output = exit = 0 (deprecation warnings only); '
         'full build lake build QRH → build_qrh_lake.txt: 2719 jobs, exit = 0, 0 errors (15 jobs above the previous baseline 2704: '
         'the def zerosLChi5UpTo + two structure axioms + the true-proof item).')

add_h1('2  Background and positioning')
add_h2('2.1  Role of pairCount_L1_bound in the N2b assembly')
add_para('The pair_const_eps_bias assembly (increment ⑦, cleared to a true proof on 2026-10-30) bounds the pairing-constant bias: '
         'after the pairConstant expansion, summability and bound of the term |Σ_{z₁≠z₂} g(δ·Δ)|/N are the last missing integration-layer bridge. '
         'Previously pairCount_L1_bound was a named axiom stating "discrete pairing sum ≤ D·δ·normL1" (summability triple packed + D·N·normL1 bound, '
         'D the logarithmic pairing density). This round clears its axiom → theorem demotion; no vacuous axiom→axiom renaming.')
add_h2('2.2  Diagnosis: two flaws of the original axiom')
add_para('(i) Wrong zero-set choice: zerosLChi5 is the full critical-strip zero set (infinite). The vertical-difference band window 2πε/logT contains infinitely many pairs — '
         'the vertical zero density is continuous in height (Riemann–von Mangoldt density ~ (1/2π)·log(T/2π)), so a fixed window 2πε/logT contains infinitely many zero pairs; '
         'the Σ over an infinite set is undefined and Summable is false. Truncating to Z_T := {z ∈ zerosLChi5 | |Im z| ≤ T} makes the set finite and the sum well defined.')
add_para('(ii) Inconsistent normalization: δ = logT/(2π) is the pairing displacement scale (S7.1 §2: A = 1 + Σ K(δΔ)²/N_Z, δ = logT/(2π), N = zero count N_Z). '
         'The original RHS D·δ·‖g‖₁ used δ as the normalization, inconsistent in magnitude/convention with the document layer; the correct normalization is the zero count N_Z(T).')
add_h2('2.3  Established pattern')
add_para('Following the project convention: fix the convention first, then prove (same as the f0 support truncation, S7.9 prime-term false proposition, '
         'S7.11 x=1 boundary, S7.13 singularity extension); after the convention fix, prove, without keeping a renamed axiom.')

add_h1('3  Convention fix: truncated zero set and normalization')
add_h2('3.1  Truncated zero set')
add_math_para('Z_T := zerosLChi5UpTo T := {z ∈ zerosLChi5 | |Im z| ≤ T}')
add_para('zerosLChi5UpTo is a new def in S7_1_Stage3.lean; Z_T is finite (Finset), the sum becomes a Finset sum, and Summable holds automatically.')
add_h2('3.2  New statement')
add_math_para('pairCount_L1_bound : (hT0 : 1 < T0) → ∃ D ≥ 0, ∀ T ≥ T0, Σ_{z₁≠z₂∈Z_T} |g(δ·Δ)| ≤ D · N_Z(T) · ‖g‖₁')
add_h2('3.3  Two new number-theory structure axioms')
add_para('zerosLChi5_bounded_finite (Z_T finite: boundedness of zero height, carrying the RvM counting); '
         'pair_count_bound (count (1:ℝ) ≤ Dcnt·N_L T: an upper bound for |Z_T| in terms of the logarithmic zero count, threshold 1 < T0). '
         'Both enter the outstanding-axiom ledger (number-theory items; proofs pending the aggregate mathlib Mathlib.olean).')
add_h2('3.4  pair_const_eps_bias assembly synchronization')
add_para('The assembly point pair_const_eps_bias is synchronized: N := N_L T, Z := zerosLChi5UpTo T, threshold 1 ≤ T0 → 1 < T0; '
         'C₁ = 4M²·Dcnt (keeping the increment ⑦ convention fix), Bound still = ε. Chain: pairConst_sub_pairL1 → (2M/(N_L T))·tsg → hcnt → field_simp → '
         'f0_sub_feps_L1_bound → ring.')

add_h1('4  True-proof chain (Stage3, from line 763)')
add_h2('4.1  Constants and summability packing')
add_para('rcases pair_count_bound → Dcnt; M := (√2·|sin(1/√2)|)⁻¹; hMpos/hM0 (M > 0 / 0 ≤ M, reusing sin_inv_sqrt2_ne_zero); '
         'hLpos := normL1_sub_pos (‖f₀−f_ε‖₁ > 0); D := (2·M·Dcnt)/normL1; hD0 (D ≥ 0).')
add_h2('4.2  Finite-support items')
add_para('hfinZ/hfinP (support inclusion; summability via summable_of_finite_support — in v4.34 Summable.of_finite_support does not exist; '
         'replaced file-wide, deprecation warning only, not blocking); hsum_supp → hsum; hcnt_supp/hcnt_sum (count-term summability).')
add_h2('4.3  Termwise bound hterm')
add_para('In support (|x| ∈ supp f0): |f₀−f_ε| ≤ 2M (inherited global bound via f_eps_abs_le/f0_abs_le) and the count term = (1:ℝ); '
         'outside support f₀/f_ε are 0 (f_eps_support/f0 truncation): first prove (1/2) < δ|…| then reduce f₀, f_ε to 0; '
         'the count 0/1 branches use explicit rw [if_pos hz]/rw [if_neg hz] + change with explicit hcnt1/hcnt0 declarations.')
add_h2('4.4  hg_sum (Summable.of_norm_bounded)')
add_para('Termwise bound: |·| ≤ |a| + |b| + |c| — abs_of_nonneg (abs_nonneg _) removes the nested outer abs, '
         'and associativity/commutativity is closed directly by linarith (this is the fix of the only remaining error of round seven: '
         'the calc second step rw [← add_assoc] reported "Did not find an occurrence of the pattern ?a + (?b + ?c)" — the association direction was wrong, '
         'the rw could not match the target shape |diff| ≤ |a| + |b| + |diff|; linarith closes it).')
add_h2('4.5  Assembly: hle_sum / hle2 / hle3')
add_para('hle_sum (Summable.tsum_le_tsum with three arguments (h)(hf)(hg) — v4.34 needs the third summability argument); '
         'hcnt_le (count-bound hookup); hle2 (tsum_mul_left + mul_le_mul_of_nonneg_left, supplemented by (mul_nonneg (by norm_num : 0 ≤ 2) hM0)); '
         'hle3 (unfold D + hform (substituting D = (2·M·Dcnt)/normL1) + le_div_iff₀ hLpos (v4.34: le_div_iff / le_div_iff\' are submodule/filter lemmas; '
         'for real division use le_div_iff₀ (hc : 0 < c) : a ≤ b/c ↔ a·c ≤ b) + ring_nf + exact le_rfl); '
         'finally exact ⟨hsum, le_trans hle2 hle3⟩.')
add_h2('4.6  Constants in detail')
add_math_para('D = 2M·Dcnt / ‖f₀−f_ε‖₁,  M = (√2·|sin(1/√2)|)⁻¹,  Bound = ε')
add_para('‖f₀−f_ε‖₁ ≤ 2εM is the increment ⑤ true proof f0_sub_feps_L1_bound (‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹).')

add_h1('5  v4.34 lemma-name corrections (newly hit this round)')
add_para('Import path: Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic (the old full name does not exist after the v4.34 directory split) + added MeasureTheory.Measure.Restrict.')
add_para('Continuous.max / Continuous.min (continuous.max does not exist; Topology/Order/OrderClosed.lean:696 protected) — w_eps continuity construction (line 731 helper).')
add_para('Set.uIoo (intervalIntegral.uIoo does not exist) — back from uIoo to Ioo: simpa [Set.uIoo, min_eq_left, max_eq_left] (lines 743–744).')
add_para('MeasureTheory.Measure.restrict_le_self (namespace Measure, MeasureTheory/Measure/Restrict.lean:141).')
add_para('le_div_iff₀ (Algebra/Order/GroupWithZero/Basic.lean:1130, (hc : 0 < c) : a ≤ b/c ↔ a·c ≤ b); '
         'le_div_iff / le_div_iff\' are for submodule/filter, not real division.')
add_para('MeasureTheory.integral_mono_measure is a 3-explicit-argument lemma (Bochner/Basic.lean:588, (hle : μ ≤ ν) (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν)); '
         'at hsub the hfi sits on volume (closed by hLHSint); the original .restrict placed it on the wrong measure (the 753:6 type mismatch), '
         'and the redundant third branch was removed in the same round.')
add_para('Summable.of_finite_support → summable_of_finite_support (deprecation warning, not blocking); '
         'count-term type ℕ → ℝ: then (1 : ℝ) else 0 replaced file-wide.')
add_para('N_L / N_L_lower_bound forward references (about 60-error group) → the two axiom definition blocks moved before the N2b hookup region, '
         'with a "definition moved forward" comment left at the old site.')

add_h1('6  Build verification')
add_para('Solo-build rounds stage3_pceb1.txt … stage3_pceb12.txt (multiple "solo build → fix error → rebuild" rounds, closed category by category: '
         'imports / forward references / named lemmas / assembly); stage3_pceb12.txt empty output = exit = 0, deprecation warnings only '
         '(if_pos → ite_eq_left, if_neg → ite_eq_right, summable_of_finite_support → summable_of_hasFiniteSupport, '
         'following the established non-blocking convention). '
         'Full build lake build QRH → build_qrh_lake.txt: 2719 jobs, exit = 0, 0 errors (15 jobs above 2704: '
         'the def zerosLChi5UpTo + the structure axioms zerosLChi5_bounded_finite/pair_count_bound + the true-proof item).')

add_h1('7  Outstanding named axiom table')
tbl = doc.add_table(rows=12, cols=3)
tbl.style = 'Table Grid'
tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
data = [
    ('Name', 'Location', 'Status'),
    ('fourierCos_Khat', 'Core §4b', 'connector: fourierCos Khat = Khat closed form, consistency item'),
    ('bgs5_khat_fourier_supp', 'Main', 'BGS Lemma 5 frequency support, integral-layer item'),
    ('siegel_walfisz_chi5', 'Main', 'SW theorem for χ₅, PNT-in-AP scale'),
    ('landau_explicit_L', 'Main', 'Landau explicit formula L-version; (L1b) two items cleared'),
    ('N_L', 'Stage3', 'number-theory item: logarithmic zero count (S6 / S7.1 §2 N_Z)'),
    ('N_L_lower_bound', 'Stage3', 'number-theory item: lower bound of the count'),
    ('zerosLChi5_bounded_finite', 'Stage3', 'number-theory structure item (new this round): Z_T finite'),
    ('pair_count_bound', 'Stage3', 'number-theory structure item (new this round): count (1:ℝ) ≤ Dcnt·N_L T'),
    ('n2_linkage', 'Stage3', 'structural item, S7.4 Theorem N2'),
    ('n3_remainder_uniform', 'Stage3', 'structural item, S7.5 Theorem N3'),
    ('pairCount_L1_bound', 'Stage3 N2b', 'cleared this round; D = 2M·Dcnt/‖f₀−f_ε‖₁ (axiom → theorem)'),
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

add_para('Note: the table is a 2026-10-31 snapshot. After pairCount_L1_bound, every integration-layer input of the pair_const_eps_bias assembly (increment ⑦) is a true theorem '
         '(f0_sub_feps_L1_bound increment ⑤ / khat_lipschitz increment ⑥ / pair_const_eps_bias increment ⑦ / pairCount_L1_bound increment ⑧); '
         'the closest remaining items are fourierCos_Khat (connector) and bgs5_khat_fourier_supp (integral-layer narrow support, pending aggregate), '
         'plus the six Stage3 number-theory items (including the two new structure axioms of this round).')

doc.save(OUT)
print('saved:', OUT)
