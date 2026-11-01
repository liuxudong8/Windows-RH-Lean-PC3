# A5CharQ5: The Character Field of the 3-Dimensional Irreducible Character of A₅ is Q(√5) (Formalization of "Layer 2")

> **Theorem goal (Layer 2)**: The 3-dimensional irreducible character of A₅ takes the value (1±√5)/2 on elements of order 5, and all character values lie in Q(√5).

**Mathematical background**: A₅ ≅ PSL(2,5) ≅ the icosahedral rotation group. Its 3-dimensional irreducible representation is the icosahedral representation; the character field Q(√5) arises from the golden ratio φ = (1+√5)/2, and the character values on order-5 elements are exactly the conjugate pair of 2cos(2π/5).

---

## 1. Project Layout and Build Environment

| Item | Value |
| --- | --- |
| Project root | `C:\proj2` (lake project, toolchain `leanprover/lean4:v4.34.0-rc2`) |
| Library | `A5CharQ5` (registered in lakefile.toml, depends on `mathlib4` → symlink `C:\proj\mathlib4-master`) |
| Main source | `A5CharQ5/A5Defs.lean` (~650 lines, 63 declarations) |
| Character body | `A5CharQ5/CharValues.lean` (3 remaining `sorry`s) |
| Aggregate entry | `A5CharQ5.lean` (imports both) |
| TC numeric check | `A5CharQ5/tc_check.py` |
| Build command | `$env:PATH = "C:\Users\shtcl\.elan\bin;..."`; `lake build A5CharQ5` (3085 jobs) |

---

## 2. Six-Item Breakdown Status

| # | Item | Status |
| --- | --- | --- |
| #1 | `goldenToComplex` (GoldenInt → ℂ algebra embedding) | ✅ no sorry |
| #2 | Generators s=(12345), t=(123), closure{s,t} = A₅ | ✅ no sorry |
| #3 | `icosahedralRep` / `finrank` | ⏳ #3a/#3b done; #3c in progress; `icosahedralRep`/`finrank` still sorry |
| #4 | `icosahedral_simple` (irreducibility) | ⬜ sorry (untouched) |
| #5 | `exists_five_order_char_phi` | ⬜ sorry (untouched) |
| #6 | Five golden lemmas + `char_values_in_Q5` | ✅ algebraic skeleton done; `char_values_in_Q5` body ⬜ |

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

### 3.5 #3c Presentation Completeness |P| = 60 (549–641)
mathlib has no Todd-Coxeter tool, so |P|=60 is obtained by hand coset enumeration (12 left cosets of H = ⟨a⟩ = the 12 vertices of the icosahedron):

- `orderOf_a = 5`, `orderOf_b = 3`, `orderOf_a2b = 2` (forward direction via `one_of_mem`; reverse via contradiction / `by decide`)
- `pA`, `pB`, `cosetRep : Fin 12 → P` (12 shortest-word representatives)
- `pA_pow_five`, `pB_pow_three`, `pA2B_pow_two` (direct relator-proof pattern)
- Sample action lemmas `coset_a_0`, `coset_b_3` (pattern ∃k, g·cᵢ = cⱼ·aᵏ established)

**Python numeric verification (tc_check.py)**: the presentation ⟨a,b | a⁵=b³=(a²b)²=1⟩ generates exactly 60 elements (=A₅); the 12 left cosets of a=(12345); action table and shortest words fully determined.

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

Commutation table: the only two-letter form is `b·a² = a³·b²`; `b·a`, `b·a³`, `b·a⁴` need longer words (each action lemma reduced independently).

---

## 5. Current State and Next Steps

**Current main line: #3c** (presentation completeness). The sample proof pattern is established (`use k` + `simp [cosetRep]` + `rw [← mul_assoc]` + `change` + power lemma). To do:

1. Commutation lemmas (derived from `pA2B_pow_two`, try the `group` tactic)
2. Prove the 24 action lemmas one by one (all data numerically determined)
3. Coset coverage → surjectivity `P →* A₅` → injectivity → |P| = 60
4. **#3d**: `icosahedralRep : FDRep ℂ G` (`FDRep.of` needs a `Representation` on all of G, descend via `QuotientGroup.kerLift`/`quotientKerEquivOfSurjective`) + `finrank = 3`
5. **#4/#5/#6**: the three `sorry`s in CharValues.lean (`icosahedral_simple`, `exists_five_order_char_phi`, `char_values_in_Q5`)

---

## 6. Key Debugging Experience (Confirmed Pitfalls and Patterns)

- **Matrix definitions** use `!![...]` (not `![]`); power expansion via `change` + `rw [pow_succ]` chains, exactly one `simp` per multiplication layer
- **√5 polynomial closure**: `ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num`; repeated simp reports "made no progress"
- **Presented group orders**: `PresentedGroup.mk (x^5)` needs explicit `rels`; relator lemmas safest via `one_of_mem` + `simpa [rels]`
- **Power lemmas**: `simpa [orderOf_x] using pow_orderOf_eq_one` over-simplifies to True → use `have h := pow_orderOf_eq_one` + `rw [orderOf_x] at h` + `exact h`, or directly `one_of_mem`
- **Existential exponents**: `∃ k : Fin 5, ... ^ k` needs `k.val` (Fin 5 is not Nat); introduce with `use (k : Fin 5)`
- **Associativity direction**: right-associated `x·(y·z)` needs `rw [← mul_assoc]` (`mul_assoc` forward matches only left-associated forms)
- **Subgroup multiplication in G**: deep whnf via `congrArg Subtype.val` times out → use `by decide`
- **Build feedback**: `lake build` swallows error details; use `lake env lean A5CharQ5\A5Defs.lean` for single files; redirect logs with `Out-File -Encoding utf8`

---

## 7. Relation to the Three Main Lines (QRH/BSD/RH)

This theorem is one piece of the "readable proof" route: instead of a 43M-line monolith, we formalize classical finite group facts (icosahedral group, presentation completeness, character field) in small, commented, human-readable steps. The character field Q(√5) is homological with the pentagon/golden-ratio structures from the user's early knot-theory notes (one of the convergence points of the three research lines).
