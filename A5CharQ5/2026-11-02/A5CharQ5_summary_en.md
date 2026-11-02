# A5CharQ5: The Character Field of the 3-Dimensional Irreducible Character of A₅ is Q(√5) (Formalization of "Layer 2")

> **Theorem goal (Layer 2)**: The 3-dimensional irreducible character of A₅ takes the value (1±√5)/2 on elements of order 5, and all character values lie in Q(√5).

**Mathematical background**: A₅ ≅ PSL(2,5) ≅ the icosahedral rotation group. Its 3-dimensional irreducible representation is the icosahedral representation; the character field Q(√5) arises from the golden ratio φ = (1+√5)/2, and the character values on order-5 elements are exactly the conjugate pair of 2cos(2π/5).

---

## 1. Project Layout and Build Environment

| Item | Value |
| --- | --- |
| Project root | `C:\proj2` (lake project, toolchain `leanprover/lean4:v4.34.0-rc2`) |
| Library | `A5CharQ5` (registered in lakefile.toml, depends on `mathlib4` → symlink `C:\proj\mathlib4-master`) |
| Main source | `A5CharQ5/A5Defs.lean` (~1570 lines, 24 coset-action lemmas fully proved, **zero sorry**) |
| Character body | `A5CharQ5/CharValues.lean` (3 remaining `sorry`s) |
| Aggregate entry | `A5CharQ5.lean` (imports both) |
| Build command (authoritative) | `Set-Location C:\proj2; $env:PATH = "C:\Users\shtcl\.elan\bin;..."; lake env lean A5CharQ5\A5Defs.lean` |
| Build status | **exit=0, clean compile** (2026-11-02, log `build_step3o.txt`) |

---

## 2. Six-Item Breakdown Status

| # | Item | Status |
| --- | --- | --- |
| #1 | `goldenToComplex` (GoldenInt → ℂ algebra embedding) | ✅ no sorry |
| #2 | Generators s=(12345), t=(123), closure{s,t} = A₅ | ✅ no sorry |
| #3 | `icosahedralRep` / `finrank` | ✅ **done**: #3a/#3b/#3c complete (24 coset-action lemmas proved → coset layer of presentation completeness closed); #3d `icosahedralRep = FDRep.of ρG`, `finrank_icosahedralRep = 3` proved |
| #4 | `icosahedral_simple` (irreducibility) | ⬜ sorry (CharValues.lean, untouched) |
| #5 | `exists_five_order_char_phi` | ⬜ sorry (CharValues.lean, untouched) |
| #6 | Five golden lemmas + `char_values_in_Q5` | ⬜ algebraic skeleton done; body untouched |

---

## 3. Established Lean Results (all without sorry)

### 3.1 #1 Golden Ratio Embedding (A5Defs.lean 58–99)
- `alpha : ℂ := (1 + √5)/2`; `alpha_sq : alpha·alpha = 1 + alpha` (φ² = φ+1)
- `goldenToComplex : GoldenInt →ₐ[ℤ] ℂ`, with five lemmas: φ ↦ alpha, φ̄ ↦ 1-alpha, 3 ↦ 3, 0 ↦ 0, -1 ↦ -1

### 3.2 #2 Generators and A₅ (124–263)
- `s := (12345)` (5-cycle), `t := (123)` (3-cycle); `sG`, `tG` ∈ A₅ (sign = 1)
- `orderOf_sG = 5`, `orderOf_tG = 3`; `card_G : Nat.card G = 60`
- `closure_eq_top : closure {sG, tG} = ⊤` (route: 3∣|SGen|, 5∣|SGen|, 15∣|SGen| → divisor argument + index ≤ 4 exclusion)

### 3.3 #3a Presentation (368–406)
- `rels = {a⁵, b³, (a²b)²}` (FreeGroup(Fin 2)); `P := PresentedGroup rels`
- `s2t_sq : (sG²·tG)² = 1`; `φ : P →* G` (a ↦ s, b ↦ t); `φ_range_top : φ.range = ⊤` (surjective)

### 3.4 #3b Explicit Matrix Representation (434–525)
- Constants: `c5 = (√5−1)/4`, `g5 = (1+√5)/4`, `h = 1/2`; √5 power lemmas sqrt5_sq/cube/four/five
- `icosahedralS`, `icosahedralT`: S⁵ = T³ = (S²T)² = I
- `unitS`, `unitT`, `icosahedralPsi : P →* GL(3,ℂ)` (relator verification → well-definedness)

### 3.5 #3c Presentation Completeness |P| = 60 (549–641 + coset layer)
mathlib has no Todd-Coxeter tool, so |P|=60 is obtained by hand coset enumeration (12 left cosets of H = ⟨a⟩ = the 12 vertices of the icosahedron):

- `orderOf_a = 5`, `orderOf_b = 3`, `orderOf_a2b = 2` (forward via `one_of_mem`; reverse via contradiction / `by decide`)
- `pA`, `pB`, `cosetRep : Fin 12 → P` (12 shortest-word representatives)
- `pA_pow_five`, `pB_pow_three`, `pA2B_pow_two` (direct relator-proof pattern)
- Action lemmas `coset_a_0..11`, `coset_b_0..11` (∃k, g·cᵢ = cⱼ·aᵏ) — **all 24 fully proved**

**Python numeric verification (tc_check.py)**: the presentation ⟨a,b | a⁵=b³=(a²b)²=1⟩ generates exactly 60 elements (=A₅); the 12 left cosets of a=(12345); action table and shortest words fully determined.

### 3.6 #3c Completed: the 24 Coset-Action Lemmas (clean compile 2026-11-02)

**Audit**: all 24 declarations in place; 20 original proof bodies compiled; 4 genuinely broken = `coset_a_11` (k=4), `coset_b_7` (k=4), `coset_b_8` (k=2), `coset_b_11` (k=1). `coset_b_8` had been fixed earlier; the closing round handled a_11 / b_7 / b_11 plus 3 peripheral errors at end of file:

| Peripheral error | Fix | Location |
| --- | --- | --- |
| φ left inverse (hbij.2 direction) | `hg.symm → hg` (direction is `x = φ_preimage g`) | ~A5Defs.lean:1534 |
| ψ map_mul' | `congrArg2` (ASCII name absent) → `congr 1` + two `(Classical.choose_spec (φ_surjective gᵢ)).symm` | ~:1564 |
| `icosahedralRep` | hand-written V/ρ type mismatch → `FDRep.of ρG` (mathlib official `of {V} (ρ) : FDRep R G`, `of_ρ' : (of ρ).ρ = ρ`) | :1563 |

**Compile-round convergence** (judged by full error-line lists; lesson: never trust a tail-only reading — build_step3i was misread as "1 left"):

| Log | Errors | Note |
| --- | --- | --- |
| build_step3f/3g/3h | 13 | batch1/2/3 baseline |
| build_step3i | misread as 1 | tail-only, untrustworthy |
| build_step3j | 7 | post-batch4 authoritative |
| build_step3k | 2 | symmetric-equation `← pow_add` deadlock + show missing parens |
| build_step3l | 1 | wrong `pow_add` direction |
| build_step3m | 1 | `a^(2+2)` not normalized |
| build_step3n | 1 | redundant `rfl` |
| **build_step3o** | **0** | **exit=0, clean compile** |

---

## 4. Todd-Coxeter Action Table (12 cosets, H=⟨a⟩)

`a·cᵢ = cⱼ·aᵏ` (i: a→j | b→j):

```
 0: a→0 | b→1    4: a→6  | b→8    8: a→10 | b→6
 1: a→2 | b→3    5: a→7  | b→9    9: a→5  | b→2
 2: a→3 | b→5    6: a→1  | b→4   10: a→9  | b→11
 3: a→4 | b→0    7: a→8  | b→10  11: a→11 | b→7
```

Shortest words: `0:1, 1:b, 2:ab, 3:bb, 4:abb, 5:bab, 6:aabb, 7:abab, 8:babb, 9:bbab, 10:ababb, 11:bababb`.

Exponent table (j,k) for the 24 actions (each corresponds to one Lean lemma `∃k, g·cᵢ = cⱼ·aᵏ`):

```
a actions:            b actions:
a·c0=c0·a¹  a·c6=c1·a²   b·c0=c1·a⁰  b·c6=c4·a³
a·c1=c2·a⁰  a·c7=c8·a¹   b·c1=c3·a⁰  b·c7=c10·a⁴
a·c2=c3·a³  a·c8=c10·a⁰  b·c2=c5·a⁰  b·c8=c6·a²
a·c3=c4·a⁰  a·c9=c5·a²   b·c3=c0·a⁰  b·c9=c2·a⁰
a·c4=c6·a⁰  a·c10=c9·a²  b·c4=c8·a⁰  b·c10=c11·a⁰
a·c5=c7·a⁰  a·c11=c11·a⁴ b·c5=c9·a⁰  b·c11=c7·a¹
```

Commutation lemmas (A5Defs.lean 697–837): `b_a2_comm` (pB·pA² = pA³·pB²), `a2_b_comm` (pA²·pB = pB²·pA³), `pB_pow_four` (pB⁴; mathlib has no `pow_four`), `a2_b_a2_eq_b2`, `b_a2_b_eq_a3`, `a_b_a_eq_a4_b2_a4`, `b2_a2_b2_eq_b_a3_b`; auxiliaries `pA_pow_five`, `pB_pow_three`, `pA2B_pow_two`, `pA_pow_mod`, `pA_pow_add_fin`, `pA_inv`, `pB_inv`; later `hba`, `hbab4`. BFS word-path evidence: a_11 all 12 RHS one-step reachable; b_11 all 9 one-step; b_7 first 4 pairs one-step fwd, tail R4→R9 depth-3 unique path.

---

## 5. Current State and Next Steps

**Current state**: A5Defs.lean **zero sorry, clean compile** (`lake env lean A5CharQ5\A5Defs.lean` exit=0); auxiliary files `A5CharQ5.lean` (top-level) and `CharValues.lean` compile with exit=0 (the latter with 3 `sorry` warnings). The coset layer of presentation completeness #3 is fully closed.

**Next steps (Layer 2 main line)**: break the three `sorry`s in CharValues.lean one by one:

1. `icosahedral_simple` (:30): irreducibility of icosahedralRep ← `FDRep.simple_iff_char_is_norm_one` + norm-60 computation
2. `exists_five_order_char_phi` (:34): ∃g, orderOf g = 5 ∧ χ(g) = φ ← trace = 1 + 2cos(2π/5) on classes 5A/5B
3. `char_values_in_Q5` (:40): all character values ∈ Q(√5) ← matrix entries (cos/sin combinations) as images of GoldenInt

---

## 6. Key Debugging Experience (Confirmed Pitfalls and Patterns)

- **Matrix definitions** use `!![...]` (not `![]`); power expansion via `change` + `rw [pow_succ]` chains, exactly one `simp` per multiplication layer
- **√5 polynomial closure**: `ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num`; repeated simp reports "made no progress"
- **Presented group orders**: `PresentedGroup.mk (x^5)` needs explicit `rels`; relator lemmas safest via `one_of_mem` + `simpa [rels]`
- **Power lemmas**: `simpa [orderOf_x] using pow_orderOf_eq_one` over-simplifies to True → use `have h := pow_orderOf_eq_one` + `rw [orderOf_x] at h` + `exact h`, or directly `one_of_mem`
- **Existential exponents**: `∃ k : Fin 5, ... ^ k` needs `k.val` (Fin 5 is not Nat); introduce with `use (k : Fin 5)`
- **Associativity direction**: right-associated `x·(y·z)` needs `rw [← mul_assoc]` (`mul_assoc` forward matches only left-associated forms)
- **Subgroup multiplication in G**: deep whnf via `congrArg Subtype.val` times out → use `by decide`
- **Build feedback**: `lake build` swallows error details; use `lake env lean A5CharQ5\A5Defs.lean` for single files; redirect logs with `Out-File -Encoding utf8`; judge by full error-line lists, never tail-only
- **New mechanics (from the coset-lemma fight)**:
  1. `nth_rewrite_lhs` does not exist in this mathlib → `nth_rewrite <n> [...]`; bare `rw [h]` **recursively rewrites all matches** (root of "over-splitting/repeated lines"); to touch exactly one occurrence use `nth_rewrite 1`
  2. A left-associated tail `(…·b)·b` is not a `b·b` subtree, so `rw [← pow_two]` cannot match → first `group` into a `(b·b)` block
  3. `pow_add` has LHS `a^(m+n)`: to compose `a²·a²→a⁴` use `← pow_add`; `rw` auto-normalizes `(2+2)→4` and closes, while `nth_rewrite 1` leaves `a^(2+2)` unsolved
  4. In a symmetric equation, `rw [← pow_add]` matches both sides and cancels → use `rw [show 单项 = 目标 by rw [← pow_add]]` (show LHS must be the current target shape)
  5. `group` does not unfold `^2`; `congrArg2` (ASCII name) absent → `congr 1` + per-item `exact (Classical.choose_spec (φ_surjective gᵢ)).symm`
  6. After a calc step is closed, extra rw/show lines report `No goals to be solved`

---

## 7. Relation to the Three Main Lines (QRH/BSD/RH)

This theorem is one piece of the "readable proof" route: instead of a 43M-line monolith, we formalize classical finite group facts (icosahedral group, presentation completeness, character field) in small, commented, human-readable steps. The character field Q(√5) is homological with the pentagon/golden-ratio structures from the user's early knot-theory notes (one of the convergence points of the three research lines). The A5CharQ5 project is mirrored to GitHub (liuxudong8/Windows-RH-Lean-PC2) as `A5CharQ5\<date>` snapshots via push.ps1.
