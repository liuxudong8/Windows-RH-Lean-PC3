# Stage 4 Summary — RH/K-GRH Spectral Duality Framework

| Item | Value |
|------|-----|
| Generated | 2026-11-22 (includes 11/21–11/22: archive audit, Sylvester-inertia port, explicit A-matrix) |
| Lean version | v4.34.0-rc2 |
| mathlib | `C:\proj\mathlib4-master`, HEAD `f8d25bb` (8407 .lean files, 6952 compiled oleans) |
| Project path | `C:\proj2` (library `OrderPreservingBijection`, plus lean_libs `BSD`/`QRH`/`A5CharQ5`) |
| Build | per-file: `lake env lean <file> -o <olean>`; `stage_4.lean` 2600–2700 jobs, 0 error; `StatementAlign.lean` 0 error |
| Archive counterpart | `F:\F\BSD_GRH_RH\RH_14` (174,793 `.lean`, 14 volumes, 239,275,554 B) |

---

## Project status overview (measured 2026-11-22)

| Item | Value |
|------|------|
| `.lean` files under `OrderPreservingBijection\` | 115 (incl. ~22 `test_*.lean` probes, non-deliverable) |
| `sorry`/`admit` textual hits (active files, comments included) | 148 |
| of which `stage_4.lean` | 52 textual hits (38 at statement level; the rest in docstrings) |
| `SylvesterInertia.lean` / `EllipticClasses.lean` hits | 2 / 2, **all inside docstrings; no sorry in proof bodies** |
| Custom `axiom` (active files) | **0** (only two test files keep `axiom intervalIndicator_mellinTransform`) |
| `opaque` declarations (active files) | **7** (5 in `stage_4.lean` + `MollifiedFunction.ellipticWeight` + `HeatKernelConvolution.sphericalPoint`) |
| `#print axioms riemann_hypothesis` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| **Main-chain custom axiom** | **0** |
| Archive static audit | `axiom 0 / constant 0 / opaque 0 / unsafe 0 / sorry 0 / admit 0 / native_decide 0` |

---

## Project goal and mathematical framework (decision 2026-09-30, unchanged)

**Current formalization target: K-GRH (local GRH for Q(√5))** — every nontrivial zero of ζ_K(s) = ζ(s)L(χ₅,s) satisfies Re(ρ)=1/2, derived from the spectral-duality bridge (Arthur trace + order-preserving bijection + JL unitary equivalence + explicit formula).

**RH (for Riemann ζ) is the long-term goal**: needs a paper-level bridge "ζ_K zero side → ζ zero side" (K-GRH does not imply RH: zeros of ζ ⊂ zeros of ζ_K). All three source papers use K=Q(√5) (Γ=PSL₂(𝒪_K)); **no F=Q setting**; Paper 3 abandons "Z_M(s)=ζ(s) global analytic identity".

```
Arthur trace formula (spectral side Σf(λ) = geometric side ΣW(γ)f(ℓ(γ)) + elliptic + Cont)
    ↓  order-preserving bijection Φ:𝒢↔I_prim (Paper 2, ℓ=log Nm, h_K=1)
Jacquet-Langlands unitary equivalence (split primes w_p=1/2, unitary normalization)
    ↓
K prime-ideal weighted sum ↔ ζ_K explicit formula (after A2 fix; NOT the ζ explicit formula)
    ↓  real spectrum (self-adjoint spectral theorem + JL unitary equivalence)
λ = 1/4 + t², t∈ℝ ⟹ ρ = 1/2 + it ⟹ Re(ρ) = 1/2
    ↓
K-GRH (current) → (bridge needed) → RH (long-term)
```

---

## Completed main work

### 1. Infrastructure layer

`BasicInfrastructure` / `MellinInfrastructure` / `ManifoldInfrastructure` (ℍ³/ℍ², `L2Function`, `gammaAction`) / `HyperbolicMeasure` / `HeatKernel` / `HeatKernelSemigroup` / `HeatKernelConvolution` / `MollifiedFunction`.

New in this round:

| Module | Content |
|------|------|
| `EllipticClasses.lean` (11/21) | elliptic conjugacy-class matrix layer: `GoldenMatrix`/`IsEllipticMatrix`/`ellipticClassLengths` + finiteness theorem, replacing `opaque` + `by sorry` |
| `HyperbolicLaplacian.lean` | `hyperbolicLaplacian`, spectral bottom 1 (3D) / 1/4 (2D) |
| `LaplacianBeltrami.lean` (11/21) | genuine 3D Laplace–Beltrami (orthonormal frame `eX,eY,eT`), replacing `Classical.arbitrary` |
| `LaplacianBeltramiX.lean` (11/21) | 2D version + `casimir_two_dimensional` |

### 2. Inertia-law layer (11/21, ported from the archive)

`SylvesterInertia.lean`: 356 lines / 30 declarations / olean 1.06 MB. Nine main theorems all have axiom set `[propext, Classical.choice, Quot.sound]`, zero warnings.

| Theorem | Content |
|------|------|
| `hasSignature_fst_unique` | unique positive part of a signature (verbatim from archive, 101 lines) |
| `sylvester_le` | injective subspace with `Q ≤ 0` has dimension ≤ q |
| `hasSignature_of_frame` | `Qᴴ J Q = Jpq p q` ⟹ signature `(p,q)` |
| `hasSignature_fromBlocks` | `diag(A₁,A₂)` signature is additive |
| own additions | `card_eq_of_hasSignature`, `hasSignature_unique` (negative part via total dimension), `card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature`, `Jpq_eq_diagonal_elim_one_neg_one` |

**Engineering note (must remember)**: `import Mathlib` makes Lake decide to rebuild all of mathlib (1455 modules never compiled); around 8761/8800 about 30 modules report `failed to read .olean` — the files are actually there, it is a spurious failure from 32 concurrent lean processes. The only safe recipe: narrow imports to concrete modules, then `lake env lean <file> -o <olean> -i <ilean>`.

### 3. Main theorem layer (`stage_4.lean`, 6206 lines)

`riemann_hypothesis (f : MollifiedTestFunction)` remains the final theorem (statement kept as placeholder, target K-GRH). New in this round: the A-matrix signature interface (6 theorems) and the explicit Weil Gram matrix section (3 theorems); the trailing `#print axioms` audit list grew from 13 to **16** entries.

---

## Work in the previous round (2026-09-28 ~ 09-30, historical)

A. Axiom batch downgrade (~28) → `lemma ... := by sorry`; snapshots into `c:\proj2\archive\` (49 files); deleted `stage_4_m.lean`.

B. Main-chain custom axiom zeroed: `nontrivialZero_im_ne_zero` proved via Dirichlet-eta bridge.

C. ZetaZeros refactor: `zeroMultiplicity` opaque→def; symmetry lemma with hypotheses.

D. mathlib bridges: `riemannZeta_conj`, `second_moment_gaussian_integral`, `cauchy_theorem_contour`.

E. `CompletedZeta.lean`: `xi_one_sub` fully proved.

F. `zeroMultiplicity_symmetry` closed (functional equation + Γℝ nonzero + local multiplicity chain).

G. `eta_eq_mul_riemannZeta` on Re s>1.

H. `riemannZeta_neg_on_Ioo` (ζ negative on (0,1)): paired series + identity theorem over `etaDomain`; `nontrivialZero_im_ne_zero` settled.

I. `ContourIntegral :109` rewritten to `contourIntegral = zetaZeroSide f − farZeroContribution f`; `:115` filled.

J. ZetaZeros: `contourZeroFinset_finite`, `contourZeroFinset`, `farZeroContribution`, split `nontrivialZeroSum`.

K. Weil-exact refactor: `weil_explicit_formula_exact` (admit), `weyl_far_error_pairing` (theorem).

L. Three-paper audit + target downgrade (★): A2 inert primes (critical), A1 setting mismatch (compact vs noncompact), A3 continuity claim; target K-GRH now, RH long-term.

---

## Work in this round (2026-11-21 ~ 11-22)

### M. Archive RH_14 download + static full scan

14 volumes into `F:\F\BSD_GRH_RH\RH_14`, **239,275,554 B**, expanded into **174,793 `.lean`** files.

Text-level static scan: `axiom 0 / constant 0 / opaque 0 / unsafe 0 / sorry 0 / admit 0 / native_decide 0`; only 2 `partial def` and 38 `Lean.Elab.Tactic` shells. **"No hidden opaque whitewashing" is answered at text level.**

Pin: toolchain `leanprover/lean4:v4.33.1`, mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474`, `moreLeanArgs=["--tstack=400000"]`, `maxHeartbeats=4000000`. **246 archive files** use `HasSignature` — the inertia law is their shared low-level component.

News check (two self-media screenshots): Levent Alpöge's announcement exists but is **self-declared, not independently verified**; the "250k pages + Lean formalization" detail corresponds to their published Lean archive.

### N. Theorem-level `#print axioms` unreachable → statement-level build as substitute

`#print axioms riemannHypothesis` needs a closure of 175,133/175,187 modules, peak 6.4–7.8 GB per process, above the local commit limit of 39.7 GB ⟹ **unreachable**. Recorded in `Build_Feasibility.md`.

Substitute: build only `Statements` (depends on Mathlib only) → the 4 defs have axiom set `[propext, Classical.choice, Quot.sound]`; `RiemannHypothesis` equals `RiemannZetaZerosOnLine` by `rfl` (**no weakening at statement level**); artifact `stmtbuild\Statements.olean` 20,784 B.

### O. Porting four inertia-law items (→ `SylvesterInertia.lean`)

1. The only dependencies are `cT` (:13), `Jpq` (:104), `HasSignature` (:483) in `Formalism/SatakeDualWeyl/Statement.lean` (463 lines, `import Mathlib` only) — copied verbatim.
2. The archive proves only the positive part; the negative part is recovered from `card n = p + q` via `omega`, yielding the needed `hasSignature_unique`.
3. The non-trivial step in `hasSignature_fromBlocks` is the reindexer `σ = (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)`; **three or more blocks require a fresh `⊕` reindexer, no recursion**.

### P. `sorryAx` provenance, real operator, S0-a setting contradiction

1. Six named `sorryAx` sources; after fixing the E chain (new `EllipticClasses.lean`) **6 → 5**.
2. Replacing `laplacian_M` (`Classical.arbitrary`) with the genuine Laplace–Beltrami exposed a setting contradiction: `ManifoldM` is the covering space ℍ³, not a compact quotient ℍ³/Γ; with `dxdydt/t³` we get `∫t²/t³ = ∫dt/t` divergence ⟹ point spectrum on L²(ℍ³) is empty ⟹ **the original axiom is literally false**.
3. Decision S0-a: `opaque CocompactQuotientHypothesis : Prop` + `theorem cocompactQuotientHypothesis := by sorry`, splitting "self-adjoint ∧ discrete spectrum" into two. 2D version `LaplacianBeltramiX.lean` added. Whole library: 3856 jobs pass.
4. **Accounting rule (must be stated)**: the gain of A1 is **removing junk, not reducing sorry counts** — the count is unchanged. `cocompactQuotientHypothesis` shows only `[sorryAx]` in the axiom set; S0-a's auditability lives in the type signature, not the axiom set.
5. **One self-correction (do not repeat)**: the earlier claim "mathlib has not even a self-adjoint notion" was wrong; the root cause was `Select-String -Path "Mathlib\**\*.lean"` where `**` matches one level only. Recursive re-check (8407 files): `IsSelfAdjoint` 73 hits; but `EssentiallySelfAdjoint` / `UnboundedOperator` / `ClosedOperator` / `BorelFunctionalCalculus` are **0** — the chain still does not close, now for the reason "notions stop at the bounded/finite level".

### Q. `stage_4.lean`: A-signature interface + explicit Weil Gram matrix

A-signature interface (6 theorems, all clean): `aSignature_wellDefined`, `aSignature_dim`, `aSignature_fromBlocks`, `aSignature_of_frame`, `aNegativeDim_le`, `aSignature_fst_unique`.

Explicit Weil Gram matrix: `weilGramMatrix hz hp = Matrix.diagonal hz - hp`; `weilGram_conjTranspose` (`Aᴴ = A`), `weilGram_quadratic` (`star x ⬝ᵥ (A *ᵥ x) = Σ_j hz_j |x_j|² − star x ⬝ᵥ (hp *ᵥ x)`), `weilGram_negativeDim_le` — all clean.

**Caliber (must not be omitted)**: there is no Lean representation of `φ̂_j(ρ)`, so the zero side keeps **diagonal only** and drops the `j ≠ k` cross terms; the object written is the **diagonal-truncation model**, not the Weil quadratic form itself.

**One correction**: the axiom output of `weil_explicit_formula_trivial_terms_cancel` and `nontrivial_zero_sum_pair_separation` was line-wrapped; the earlier inference "possibly no sorryAx" was wrong — both contain `sorryAx`.

### R. `WeilGramConcrete.lean`: computable prime side + analytic bound on ‖φ̂‖²

New module, 256 lines, 13 theorems, 0 error / 0 warning, olean 248,384 B. Both abstract inputs became objects:

1. **Prime side**: `localGram p φ ψ = ∫₀¹ e^{-x log p} φ(x) \overline{ψ(x)} dx`; `weilPrimeGram N φ j k = Σ_{p ∈ Nat.primesBelow N} (log p)·localGram p (φ j) (φ k)`; hermiticity proved pointwise and matrix-wise (the key step pushes `star` through the interval integral and shows the real weight `p^{-x}` is `star`-invariant).
2. **Zero-side bound**: `phiHat φ ρ = ∫₀¹ φ(x) e^{iρx} dx`; `‖φ̂(ρ)‖ ≤ e^{‖ρ‖}∫₀¹‖φ‖`; `‖φ̂‖² ≤ (e^{T})²(∫‖φ‖)²` for `‖ρ‖ ≤ T`; `weilZeroDiag S φ j = Σ_{ρ∈S} ‖φ̂_j(ρ)‖²` with `hz_j ≤ card S·(e^{T})²(∫‖φ_j‖)²`.
3. **Assembly**: `weilGramConcrete S N φ = weilGramMatrix (weilZeroDiag S φ) (weilPrimeGram N φ)`; `Aᴴ = A`, quadratic expansion, and `weilGramConcrete_negativeDim_le` (`card k ≤ q` under a signature hypothesis).
4. **Hard boundaries (three, do not overstate)**:
   - Genuine `⟨φ_j,φ_k⟩_p` is a Haar integral over ℚ_p^*; mathlib has `Padic` but no p-adic Haar measure interface, so the explicit weight `p^{-x}` (Archimedean rendering of the multiplicative absolute value `p^{-v}`) is used — **not the Haar measure itself**.
   - Prime side is finitely truncated at `N`; zero side is a finite set `S` plus diagonal only.
   - Prime enumeration and `log` are genuinely computable, but the local inner product is an interval integral (classically non-computable), so the chain is "explicit definitions, entries exist" — **not `#eval`-able numerics**.
   - The signature `(p,q)` remains a hypothesis (`hSig`): "entries exist + Hermitian + bounds" is done; "we know A's signature" is still empty.

---

## Remaining `sorry`/`admit` distribution (measured 2026-11-22, textual hits, comments included)

| File | Hits | Note |
|------|------|------|
| `stage_4.lean` | 52 | main-chain estimates + core duality admit (38 at statement level) |
| `HeatKernel.lean` | 14 | heat-kernel HS estimates |
| `ManifoldInfrastructure.lean` | 11 | manifold analysis |
| `MellinInfrastructure.lean` | 9 | Mellin estimates |
| `HeatKernelConvolution.lean` | 8 | convolution |
| `Interpolation.lean` | 8 | interpolation |
| `BijectionPhi\Basic.lean` | 8 | duality map |
| `stage_3.lean` | 6 | stage-3 bridge |
| `ZetaZeros.lean` | 3 | `nontrivialZeroEnum_exists` (S infinite, kept) etc. |
| `HeckeBridge.lean` | 3 | |
| `ContourIntegral.lean` | 1 | `:1699` prime-Dirichlet `CircleIntegrable` (`:115` filled) |
| `MollifiedFunction.lean` | 1 | mollifier |
| `EllipticClasses.lean` / `SylvesterInertia.lean` | 2 / 2 | **all in docstrings; no sorry in bodies** |
| `test_*.lean` | ~22 | probes (non-deliverable) |

## Remaining `opaque` (7, active files)

5 in `stage_4.lean` (`CocompactQuotientHypothesis`, `scatteringMatrixLogDerivative`, `shimuraKernel`, `jlSpectrumMap`, `transferOperator`), plus `MollifiedFunction.ellipticWeight` and `HeatKernelConvolution.sphericalPoint`.

Custom `axiom`: **0** in active files; only `test_interval_indicator.lean` / `test_det_factor.lean` keep `axiom intervalIndicator_mellinTransform` (probes).

---

## Known real gaps (mathlib `f8d25bb`, recursive scan of 8407 files)

1. **Unbounded self-adjoint chain**: `EssentiallySelfAdjoint` 0, `UnboundedOperator` 0, `ClosedOperator` 0, `BorelFunctionalCalculus` 0; `IsSelfAdjoint` has 73 hits but only at the bounded/finite level.
2. **Compact resolvent**: `Rellich` 0, `Kondrachov` 0, `CompactEmbedding` 0; `SpectralTheorem` 0 (only `hasEigenvalue_or_mem_resolventSet`, 1 hit).
3. **Multidimensional integration by parts**: 0 hits.
4. **p-adic Haar measure**: `Padic` exists, no measure-theory interface.
5. **General residue theorem**: absent (first blueprint step of `ContourIntegral :109`).
6. **S infinite (Weyl/Hardy)**: `nontrivialZeroEnum_exists` kept as sorry.
7. **Dolgopyat exponential mixing**: geometric fallback only.
8. **Full Arthur trace / JL unitary equivalence formalization**: representation theory, admit-level.
9. **A2 inert-prime handling (paper level)**: decides whether the K-GRH bridge holds.

---

## Verified dead ends (do not retry)

- `lake build -j24` / `LAKE_JOBS`: unsupported by this Lake version
- `lake exe cache get`: missing git and github unreachable
- `gitee.com/mirrors/mathlib4`: `Unauthorized`; `mathlib.cache.azure.net`: all FAIL
- Theorem-level `#print axioms riemannHypothesis` on the archive: peak memory above the local commit limit
- `lake build` on files with `import Mathlib`: full rebuild + ~30 spurious module read failures (use `lake env lean -o`)

---

## Next steps

1. **Wire `WeilGramConcrete` into the main audit list**: the 16 trailing `#print axioms` in `stage_4.lean` still do not include the 13 new theorems (cross-file; needs a separate audit entry point).
2. **Numerics for A**: replace `S` with the critical-line zero set controlled by `N(T)` (mathlib has no zero enumeration; needs a counting layer), or build an `n = 2` prime-side matrix with `Nat.primesBelow 100` so that "definitions run" becomes "the matrix computes".
3. **Justify the `hz` caliber**: whether the diagonal truncation (dropping `j ≠ k`) needs an explicit error bound.
4. **K-GRH landing**: switch zero infrastructure from Riemann ζ to ζ_K (needs Dedekind zeta / L(χ₅) / K-prime von Mangoldt — mathlib lacks them).
5. Progressively discharge the 38 statement-level assumptions in `stage_4.lean`; unbounded self-adjointness of `laplacian_M`/`laplacian_X` remains `admit` pending mathlib.
