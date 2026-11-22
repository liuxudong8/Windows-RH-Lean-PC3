# -*- coding: utf-8 -*-
"""Bring both A5CharQ5 summaries up to the 2026-11-16 completed state."""
import io

CN = r'C:\proj2\A5CharQ5\A5CharQ5_summary.md'
EN = r'C:\proj2\A5CharQ5\A5CharQ5_summary_en.md'

def load(p):
    with io.open(p, encoding='utf-8') as f:
        return f.read()

def save(p, s):
    with io.open(p, 'w', encoding='utf-8', newline='') as f:
        f.write(s)

# ---------------------------------------------------------------- Chinese
cn = load(CN)

cn_banner = r'''# A5CharQ5：A₅ 三维不可约特征标的特征标域 = Q(√5)（层 2 定理形式化）

> **当前状态（2026-11-16）：项目完成，全库零 sorry。**
>
> `lake build A5CharQ5` → **3509 jobs，EXIT=0**；最后一条 `icosahedral_simple` 已真证。
>
> 数学链条（全部真证）：`ρG.ker = ⊥` → cycle type 分类 → 5-循环双分裂（α ≠ 1/2）
> → 三类共轭（∅ / {3} / {2,2}）→ 类大小（1 + 20 + 15 + 12 + 12 = 60）
> → 分组求和 60 → 特征标范数判据 `simple_iff_char_is_norm_one`。
>
> 下文 §1–§7 是施工期记录，保留原样供追溯（其中 §2 的 #4 行、§1 的"1 个 sorry"等
> 措辞已属历史口径）；第 4 步（二）、（三）两节在文件末尾，是最终闭合过程。
'''

cn = cn.replace(
    '# A5CharQ5：A₅ 三维不可约特征标的特征标域 = Q(√5)（层 2 定理形式化）\n',
    cn_banner, 1)

# §1 character body row
cn = cn.replace(
    r'| 特征标主体 | `A5CharQ5/CharValues.lean`（**1 个 sorry**：`icosahedral_simple`） |',
    r'| 特征标主体 | `A5CharQ5/CharValues.lean`（**零 sorry**：`icosahedral_simple` 已于 2026-11-16 真证） |',
    1)

# §1 build status row
cn = cn.replace(
    r'| 编译状态 | **exit=0，编译清零**（2026-11-02，日志 `build_step3o.txt`） |',
    r'| 编译状态 | **exit=0，3509 jobs**（2026-11-16，日志 `build_step12.txt`） |',
    1)

# §2 item #4 row
cn = cn.replace(
    r'| #4 | `icosahedral_simple`（不可约性） | ⬜ **唯一剩余 sorry**（CharValues.lean:59）；技术障碍与施工路线见 §5 |',
    r'| #4 | `icosahedral_simple`（不可约性） | ✅ **已闭合**（2026-11-16，CharValues.lean:64）：`simple_iff_char_is_norm_one` ← `icosahedral_char_sum`（五段求和 = 60）← 共轭类分类。施工期困难见 §5 |',
    1)

save(CN, cn)
print('CN updated')

# ---------------------------------------------------------------- English
en = load(EN)

en_banner = r'''# A5CharQ5: The Character Field of the 3-Dimensional Irreducible Character of A₅ is Q(√5) (Formalization of "Layer 2")

> **Current status (2026-11-16): complete, zero `sorry` across the library.**
>
> `lake build A5CharQ5` → **3509 jobs, EXIT=0**; the last surviving `icosahedral_simple` is now fully proved.
>
> Proof chain (all real proofs): `ρG.ker = ⊥` → cycle-type classification → 5-cycle double
> splitting (α ≠ 1/2) → three-class conjugacy (∅ / {3} / {2,2}) → class sizes
> (1 + 20 + 15 + 12 + 12 = 60) → grouped sum 60 → character-norm criterion
> `simple_iff_char_is_norm_one`.
>
> Sections 1–7 below are the construction-period record, kept verbatim for traceability
> (the "#4 sorry" row in §2 and the "3 remaining sorrys" wording in §1 are historical);
> the Step-4 (ii) and (iii) sections at the end of the file document the final closure.
'''

en = en.replace(
    '# A5CharQ5: The Character Field of the 3-Dimensional Irreducible Character of A₅ is Q(√5) (Formalization of "Layer 2")\n',
    en_banner, 1)

en = en.replace(
    r'| Main source | `A5CharQ5/A5Defs.lean` (~1570 lines, 24 coset-action lemmas fully proved, **zero sorry**) |',
    r'| Main source | `A5CharQ5/A5Defs.lean` (1786 lines, 24 coset-action lemmas, 5 character values + #5/#6, **zero sorry**) |',
    1)

en = en.replace(
    r'| Character body | `A5CharQ5/CharValues.lean` (3 remaining `sorry`s) |',
    r'| Character body | `A5CharQ5/CharValues.lean` (**zero sorry**: `icosahedral_simple` proved 2026-11-16) |',
    1)

en = en.replace(
    r'| Build status | **exit=0, clean compile** (2026-11-02, log `build_step3o.txt`) |',
    r'| Build status | **exit=0, 3509 jobs** (2026-11-16, log `build_step12.txt`) |',
    1)

en = en.replace(
    r'| #4 | `icosahedral_simple` (irreducibility) | ⬜ sorry (CharValues.lean, untouched) |',
    r'| #4 | `icosahedral_simple` (irreducibility) | ✅ **closed** (2026-11-16, CharValues.lean:64): `simple_iff_char_is_norm_one` ← `icosahedral_char_sum` (five-segment sum = 60) ← conjugacy-class classification |',
    1)

en = en.replace(
    r'| #5 | `exists_five_order_char_phi` | ⬜ sorry (CharValues.lean, untouched) |',
    r'| #5 | `exists_five_order_char_phi` | ✅ proved in `A5Defs.lean` (g = sG², `orderOf_pow` + `char_sG_sq`) |',
    1)

en = en.replace(
    r'| #6 | Five golden lemmas + `char_values_in_Q5` | ⬜ algebraic skeleton done; body untouched |',
    r'| #6 | Five golden lemmas + `char_values_in_Q5` | ✅ proved in `A5Defs.lean` (nested ∃ quintuple 3/φ̄/0/φ/−1) |',
    1)

en_tail = r'''

## Step 4 (ii): Five-Segment Sum (2026-11-16, completed)

`f g := χ(g) * χ(g⁻¹)`, `χ = icosahedralRep.character`.

| Theorem | Segment (`Finset.univ.filter`) | Size | Value per element | Segment sum |
|---|---|---|---|---|
| `sum_zero_class` | `cycleType = 0` | 1 | 9 | **9** |
| `sum_three_class` | `cycleType = {3}` | 20 | 0 | **0** |
| `sum_two_two_class` | `cycleType = {2,2}` | 15 | 1 | **15** |
| `sum_five_a` | `{5} ∧ IsConj g sG` | 12 | ᾱ² = 2−α | **12(2−α)** |
| `sum_five_b` | `{5} ∧ IsConj g sG²` | 12 | α² = 1+α | **12(1+α)** |

Total: `9 + 0 + 15 + 12(2−α) + 12(1+α) = 24 + 12·3 = 24 + 36 = 60 = |A₅|`
(uses `α² + ᾱ² = 3`).

Supporting lemmas: `G_isConj_cycleType`, `sG_pow_eq_one`, `sG_inv_eq_pow_four`,
`sG_val_cycleType`, `sG_sq_val_cycleType`, `sG_sq_inv_eq_cube`, plus `IsConj_inv`
and `char_sG_cube` (χ(sG³) = α).

Class-size spectrum: 1 + 20 + 15 + 12 + 12 = 60, from `G_threeCycle_set_card`,
`G_twoTwo_set_card`, `G_class_fiveCycle_set_card` + `G_fiveCycle_isConj_sG`.

Six pitfalls of this batch:
1. The `∑ g in s, f g` notation is unusable in this file — write `Finset.sum s (fun g => ...)`.
2. A `Finset.filter` whose predicate mentions `IsConj` fails even in the *statement*;
   `attribute [local instance] Classical.propDecidable` must be placed **after all imports**.
3. `simp only [Set.mem_ofPred_eq]` unfolds `IsConj` into `∃ c, SemiconicBy ...`; use `change`
   to keep `IsConj` intact.
4. Direction of `IsConj.symm`: pass `hc` itself to `G_isConj_cycleType`.
5. `12 + 12 * alpha = 12 * (1 + alpha)` needs `ring`; `norm_num` is not enough.
6. `native_decide` does work on `(sG ^ 2).val.cycleType = {5}` (Perm-level `Fintype` is mathlib's own).

## Step 4 (iii): Assembly — `icosahedral_char_sum` and `icosahedral_simple` (2026-11-16, zero sorry library-wide)

| Theorem | Statement | Location |
|---|---|---|
| `icosahedral_char_sum` | `∑ g : ↥G, χ(g)χ(g⁻¹) = 60` | end of `ConjClasses.lean` |
| `icosahedral_simple` | `Simple icosahedralRep` (**the last sorry**) | `CharValues.lean:64` |

Assembly: five `rw [← Finset.sum_filter_add_sum_filter_not]` splits peel `univ.sum` into five
segments; four bridges `hb2..hb5` (`filter_filter` + `filter_congr`) map the accumulated
filters back to bare filters; `hempty` closes the tail using `G_cycleType_cases`
(branch order 0 / {3} / {5} / {2,2}) together with `G_fiveCycle_isConj_sG`; then
`rw [five segment theorems]` + `ring`.

Closing: `rw [FDRep.simple_iff_char_is_norm_one]` → `rw [card_G]` → `exact icosahedral_char_sum`.

Six pitfalls of the assembly step:
1. `filter_filter` stacked twice or more yields a **right-associated** `∧`:
   `¬p1 ∧ (¬p2 ∧ p3)`, so take p3 as `h.2.2`, p4 as `h.2.2.2`, p5 as `h.2.2.2.2`;
   build in the same right-nested shape `⟨h1, ⟨h2, h3⟩⟩`.
2. But `simp only [Finset.mem_filter]` over the accumulated filters yields a
   **left-associated** `∧`: `((¬p1 ∧ ¬p2) ∧ ¬p3) ∧ ¬p4`, so the projections are
   `hg.1.1.1.1`, `hg.1.1.1.2`, `hg.1.1.2`, `hg.1.2`, `hg.2`. Both association
   directions coexist in the same proof — do not apply one rule everywhere.
3. A `by ...; tactic` block inside `⟨...⟩` must be parenthesized:
   `⟨(by rw [h]; decide), h⟩`, otherwise the `by` block swallows `, h` and Lean reports
   `Invalid ⟨...⟩ notation: expected type (cy = 0 → False) is not an inductive type`.
4. After `intro h0` the goal is `False`, and `decide` cannot prove it (it proves that
   "False is false"). Do not `intro`: `rw [h]` first to reduce the `¬` goal to
   `¬ {3} = 0`, then `decide`.
5. `Finset.eq_empty_iff_forall_notMem` (capital M), not `..._not_mem`.
6. The `rcases G_cycleType_cases` branch order is 0 / {3} / {5} / {2,2}; writing
   0 / {3} / {2,2} / {5} feeds `hc : cy = {5}` to `¬ cy = {2,2}`.

Import pitfall: `FDRep.simple_iff_char_is_norm_one` requires `IsAlgClosed ℂ`, whose
instance lives in `Mathlib.Analysis.Complex.Polynomial.Basic` (plain
`Mathlib.Analysis.Complex.Polynomial` has no olean).

Final status: `lake build A5CharQ5` → 3509 jobs, EXIT=0; real `sorry` count is 0 across
`A5Defs.lean`, `ConjClasses.lean`, `CharValues.lean` and the root module; breakdown
item #4 is closed.
'''

en = en.rstrip('\n') + '\n' + en_tail
save(EN, en)
print('EN updated')
