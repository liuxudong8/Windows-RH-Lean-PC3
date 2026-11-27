# Anatomy of the Main Chain: From RH to proposition_size_bound

This note records the layer-by-layer dissection of the main chain in the Alpöge–Claude Lean library. The purpose is not to judge it right or wrong, but first to see exactly what it rests on, and then to decide what our own QRH project should learn and what it must change.

## Correction, 2026-11-27

This note was written on 11-26, before the machine measurements of notes 17–20 and 23. The body is kept unchanged as an evidence record, but four points must be restated:

1. **§0's "the chain is type-closed end to end, with zero `sorry` and zero `axiom`"** becomes "statically no `sorry`/`axiom` gap in source; machine-verified: not verified". The closure of `Main.lean` is 175,191 files and 1.03 GB of source; the local build holds 175 oleans (0.0999%); the top level was never compiled. A dense build of 245 artifact-missing files gives 189 pass and 56 fail (3 root errors, 53 cascades, amplification 1 : 54).
2. **"Nine layers" against the L1–L16 table** was an internal contradiction in the Chinese edition only; this file already reads sixteen, and the Chinese text has been unified to 16.
3. **The conclusion of §5.2 is upgraded**: the gap is not hidden strength but failure to compile to the bottom. The strength suspicion (`aAtG`, `irrC`, `zL`, `tie` in `HypsAlt`, still not compared line by line) stays on the books but is no longer the main contradiction.
4. **§3.4's "only nine empty slots"** holds only for `: Prop := True` and is no evidence of compilability.

The three retractions in §4 (`SizeWindows` is not an island; `Green` is not an external parameter; `TLift_k` does not rely on `swFull`) **still stand**; they are source-level conclusions and are unaffected.

The successor to this note is No. 26, *The Alpöge–Claude Library Main Chain: A Two-Ledger Summary*, which carries the two-ledger table, the five-stage compression and all measured numbers.

## §0 Executive Summary

**In one sentence**: the chain is type-closed end to end, with zero `sorry` and zero `axiom`; the only genuine mathematical load sits in `ch_core` (about 100 lines) and the `proposition_size_bound` it invokes (86 lines). And the final source of `1/2` is an **assumption**: the conjunct `hm1 : x^(1/2-ε) ≤ m` inside `SizeWindows`.

Four hard findings:

1. The main chain has sixteen layers, every one a `theorem` with a proof body, not a placeholder.
2. `1/2` is neither a derived result nor a free parameter; it is one conjunct of `SizeWindows`, entering the conclusion through a single step of `hxX` in `proposition_size_bound`.
3. `ZeroFreeAll`, once unfolded, is GRH-L itself; the `1/2` is hard-coded inside `ZeroFreeOn`.
4. Of the fourteen fields of `Tools_k`, constructing `TLift_k` consumes exactly one, namely `pairEx`; `swFull` and twelve others never appear in the derivation.

Three earlier judgments that must be retracted (evidence given below):

1. `SizeWindows` is not an island — `ch_core:367` constructs and uses it.
2. `Green` is not an external hypothesis — it grows out of `P.greenRegularCharacters`.
3. The strength of `TLift_k` does not rest on `swFull` — it rests on `pairEx` plus a string of "existence of lift" statements.

## §1 Skeleton

Top to bottom, each layer with file and line.

| Layer | Theorem / Definition | Location | Role |
| --- | --- | --- | --- |
| L1 | `riemannHypothesis` | `Main.lean:4` | top-level target |
| L2 | `rhOfAll` | `Supplements/Kernels/MainTheorems.lean:9` | reduces to `rh_of_every` |
| L3 | `rh_of_every` | `Formalism/GammaFactorNonvanishing/CritLine.lean:29` | sets χ=1, L becomes ζ |
| L4 | `EveryCharacter` | `CharacterBoxes/EveryCharacter.lean:13` | definition of GRH-L |
| L5 | `everyCharacter_of_row` | `CharacterBoxes/MainConclusion.lean:7` | three-piece assembly |
| L6 | `every_character_of_literature_of_vWin` | `ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810` | seven-slot assembly |
| L7 | `every_character_of_theta_integrals_local_matching` | `ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69` | six-argument closing |
| L8 | `every_character_of_green_v_win` | `ThirdPlaceSeries/TopPlug.lean:16` | `imprimitive` to GRH-L |
| L9 | `zero_free_all_of_green_v_win` | `ThirdPlaceSeries/TopPlug.lean:12` | emits `ZeroFreeAll` |
| L10 | `zeroFreeOn_of_tiedWin_cyc` | `TotientGaloisClasses/TopWin.lean:90` | where `1/2` is hard-coded |
| L11 | `level_of_tiedWin` | `TotientGaloisClasses/TopWin.lean:68` | the `θ → 1/2 + δ` trick |
| L12 | `FormBAt` | `TotientGaloisClasses/Window.lean:30` | window width `la` |
| L13 | `windowInequality_of_artinInputs` | `PrimitiveCosets/WindowInequalityOfArtinInputs.lean:17` | reduces to `core_gm` |
| L14 | `core_gm` | `PrimitiveCosets/CoreGm.lean:12` | `Gm ≤ x^(1/2+(eD+eL+7)ε)` |
| L15 | `ch_core` | `DedekindLFunctions/LandauTheorems/ChCore.lean:343` | the three-part load-bearing step |
| L16 | `proposition_size_bound` | `ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507` | 86 lines, all arithmetic |

Mathematics begins at L15. L1 through L14 are interface transport.

## §2 Layer-by-Layer

### 2.1 L3: `rh_of_every` is three lines

```lean
theorem rh_of_every (h : EveryCharacter) : RiemannHypothesis :=
  rh_of_right (fun s hs => h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inl (by simp)))
```

Take `N = 1` and `χ = 1`, then use `LFunction_modOne_eq` to replace the L-function by ζ. **All the weight of RH falls on `EveryCharacter`; this step carries no content.**

### 2.2 L4: the definition of `EveryCharacter`

```lean
def EveryCharacter : Prop :=
  ∀ N [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0
```

This is GRH-L verbatim.

### 2.3 L9 exit: `ZeroFreeAll` equals GRH-L

This is the most important definition-level discovery of this round. From `ExplicitFormulaErrorOfHostConditions.lean:11-18`:

```lean
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True
```

Unfolded:

\[
\text{ZeroFreeAll} \;=\; \forall \psi\, \forall s,\; \tfrac{1}{2} < \operatorname{Re} s \;\Rightarrow\; L(\psi.\chi, s) \neq 0
\]

**The `1/2` is not a parameter; it sits inside the body of `ZeroFreeOn`.** Hence any theorem that outputs `ZeroFreeAll` must already have secured zero-freeness for `Re s > 1/2`; the type checker refuses any "take θ then limit" shortcut.

### 2.4 L10: the signature of `zeroFreeOn_of_tiedWin_cyc`

```lean
theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
    (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ))
    (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
    (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q
```

Note `hla : 1 < la`. This `la` is easily misread as the zero-free abscissa θ; it is not.

### 2.5 L12: `la` is a window width, not θ

From `Window.lean:7-8` and `:30-31`:

```lean
def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S

def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ
```

`HasWindows S la` says: there is a stretch `[Y, Y^la]` lying entirely inside `S`. **`la > 1` means the window is wider than `[Y, Y]`; it is a width exponent.**

In `FormBAt la`, the `θ` is the zero-free abscissa, ranging over `(0, 1)`, independent of `la`. **So "`la > 1` but passing `θ ≈ 1/2`" is not a contradiction; it is the design.**

### 2.6 L11: the `θ → 1/2 + δ` trick

```lean
theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ...) (hB : Λ.FormBAt la)
    (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel := by
  ...
  refine hB (1 / 2 + min (s.re - 1 / 2) (1 / 2) / 2) (by linarith) (by linarith) ... ψ hψ s (by linarith)
```

Given `s.re > 1/2`, set

\[
\theta \;=\; \frac{1}{2} + \frac{\min(\operatorname{Re} s - 1/2,\; 1/2)}{2}
\]

so that `θ ∈ (1/2, s.re)`. `ZeroFreeAbove θ` covers `s.re > θ`, hence covers this `s`. **This is standard and non-circular: we never need `θ = 1/2`, only some `θ` strictly below the abscissa of each point to be covered.**

**So `ZeroFreeAbove(1/2)` is actually propped up by `ZeroFreeAbove(1/2+δ)` for every `δ > 0`. This step is legitimate.**

### 2.7 L14: the conclusion of `core_gm`

From `CoreGm.lean:12-15`:

```lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1,
      ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)
```

And the definition of `Gm` (`ExplicitFormulaErrorOfHostConditions.lean:38`):

```lean
def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re
```

\[
G_m(y) \;=\; G_z(y) \;+\; \sum_{\psi}\;\Lambda.wt(\psi)\cdot \operatorname{Re} g_\chi(\psi.\chi, y)
\]

`Gz` is the zero-counting term. Hence `core_gm` says: **the growth of the zero count is controlled by `x^(1/2+(eD+eL+7)·ε)`, for arbitrarily small `ε`.**

This is one of the equivalent forms of RH (the zero-density form). Its hypotheses are only the two host conditions `EAtH` and `CoreAtH`, both supplied by `HypsAlt`.

### 2.8 L15: the three-part assembly of `ch_core`

`ChCore.lean:343-351` is the signature; `:352-442` is the proof. Four key lines:

```lean
:419  have hone := CharacterBalanceMoves.one_char ... (ρ := |M| * x ^ (-1 + ε)) (Ko := |Ko|) (L := |CE| * Real.log x) ... r1 r2 r3
:426  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x
:440  have hc' := CharacterBalanceMoves.core A0 D S hHost ell N TT T2 a w hx3 hb hS hThin hCost hT2 hTop hY
:441  have hz := proposition_size_bound _ _ _ _ _ _ _ _ _ _ _ G hW hc'
:442  linarith
```

**Note `:426`: `G := GmA − SigA`.** The `+ SigA` in the conclusion is not an unabsorbed error term; it is the result of moving the term across. This part is clean.

At `:367-370` the same proof constructs `SizeWindows`:

```lean
have hW : SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE
    (x ^ (C * ε) * errorBracketSizeWindows x ε ...) :=
  (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, hε, hC, ...⟩
```

**Two inputs are used here: `hSize` (that is, `RestSize`), together with `hm` (`m ≤ x^(1/2+ε/2)`) and `hxm` (`x*m ≤ k`).**

The rest of the `ch_core` proof body is elementary estimation (`Real.log_le_rpow_div`, `mul_le_mul_of_nonneg_left`, `linarith`, at `:375-418`), plus the three bounds `r1 r2 r3` supplied by `one_char` (`:403-425`).

### 2.9 L16: the 86 lines of `proposition_size_bound`

From `LipschitzWeightAndMinimum.lean:507-509`:

```lean
theorem proposition_size_bound : GrowthSizeBound := by
  intro C ε x n nT nT2 m b k aE Err Gx hW hT
  obtain ⟨hx3, hε, hC, hn, hb, haE0, haE, hnT, hd2, hnT2,
          hm1, hm2, hk1, hk2, hErr, hbig⟩ := hW
```

**The sixteen components extracted from `hW` are exactly the sixteen conjuncts of `SizeWindows`, no more and no fewer.**

The only entrance for `1/2` is at `:522-526`:

```lean
have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m := by
  have e : x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) = x := by ...
  calc x = x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) := e.symm
    _ ≤ x ^ ((1 : ℝ) / 2 + ε) * m := mul_le_mul_of_nonneg_left hm1 (pos _).le
```

**Only `hm1 : x^(1/2-ε) ≤ m` is used. `hm2` never appears in this proof.**

The shape of `hT` (`:551`):

```lean
have hT' : Q * ((nT2 : ℝ) / n / 2) * (Gx - 4 * X) ≤ Err + 2 * Q / x
```

The remaining steps:

| Lines | Content | Technique |
| --- | --- | --- |
| `:527-530` | `SZ.T1`–`SZ.T4` | four size lemmas |
| `:531-546` | `Err ≤ 10·P·Y·Q` | `ring` + `linarith` |
| `:553-560` | `δ := nT2/n`, `x^ε·δ ≥ 1` | `rpow` multiplication |
| `:561-569` | `δ·(Gx − 4X) ≤ 22·P·Y` | divide both sides by `Q` |
| `:570-579` | `Gx − 4X ≤ 22·P·Y·x^ε` | multiply by `x^ε` |
| `:580-585` | `P·Y·x^ε = x^(1/2+(C+21/8)ε)` | `ring_nf` |
| `:587-592` | `Gx ≤ 26·Y' ≤ x^(3ε/8)·Y'` | `hbig` absorbs 26 |

After moving terms:

\[
G_x \;\le\; 4x^{1/2+\varepsilon} \;+\; 22\,P\,Y\,x^{\varepsilon}
\]

The leading term is `4x^(1/2+ε)`; the constant 4 comes from the `one_char` side, not from inside these 86 lines. **These 86 lines are tautological arithmetic; nowhere do they invoke a zero fact.**

## §3 Three Structural Facts

### 3.1 `swFull` is never used

`GalTPDefs.lean:27-41` defines the fourteen fields of `Tools_k`; `:141-177` is the proof body of `tLift_of_k`. Verbatim check:

| Field | Used inside `tLift_of_k` |
| --- | --- |
| `pairEx` | yes (`T.pairEx` at `:158`) |
| `swFull`, `boxSec`, `dbl`, `stab2`, `cpt`, `basic`, `polSch`, `unfold0`, `split`, `vacFix`, `acts`, `lie1`, `lie2` | no |

The type of `swFull` (`ThkBaseStmtX.lean:33-42`) is the Siegel–Weil identity:

```lean
def SWFullX_k : Prop :=
  ∀ ... , ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧
    (((d : ℂ) - n) / 2) ∈ U ∧
    ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (...) ∂μ
```

The Eisenstein series is analytic at `s = (d−n)/2` and its value equals the theta integral averaged over a fundamental domain. **This is the Siegel 1935 / Weil 1964 identity: no zero information, and it is not even used in the derivation.**

### 3.2 `IsLift` is merely structural matching

From `SchurStep.lean:103-112`:

```lean
def IsLiftWt {n d : ℕ} (lam : DomWeight n) (mX mW : ℤ) (lam' : DomWeight d) : Prop :=
  ∀ k : Fin d, 2 * lam'.w k = (if h : (k : ℕ) < n then 2 * lam.w ⟨k, h⟩ - d - mW else 0) + n + mX

structure IsLift ... (U : Submodule ℂ (UA E n → ℂ)) (U' : Submodule ℂ (UA E d → ℂ)) : Prop where
  aut : IsAutRepU U'
  wt  : ∀ w, ∃ lam' : DomWeight d, HasWeightAt U' (B.emb w).1 lam' ∧ IsLiftWt (lam w) (mX w) (mW w) lam'
  loc : ∀ v t τ τ', CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' → LocPair t χX χW τ τ'
```

Three fields: automorphy, weight shift, local pairing. **The weight formula is the standard Ikeda-type lift form, again with no zero content.**

### 3.3 The 196 wrappers are an alias layer

Using `linnik_of_literature` as a specimen, four layers of nesting:

```
Layer 1  linnik_of_literature (O) : Published.Linnik := UpperTheory.Lit.linnik      EveryCharacterOfLiteratureOfVWin.lean:455
Layer 2  linnik : Published.Linnik := by                                             Linnik.lean:142-154 (4 lines)
Layer 3  exists_prime_modEq_le_rpow_of_primesRel : Lin.PrimesRel → ∃ A ...            Linnik.lean:40-140 (100 lines)
Layer 4  primesInProgressions_relativeError : Lin.PrimesRel := by                    PrimesInProgressionsRelativeErrorStatement.lean:8-9 (4 lines)
Layer 5  primesRel_holds : Lin.PrimesRel := by                                       PrimesInProgressionsRelativeError.lean:22-51 (30 lines)
```

The proof body of Layer 4 is:

```lean
first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
```

**`first | A | B | C` is a three-way trial match, not a chain of reasoning.** This is the trace of an interface matched by guessing.

Layer 5 is the real brick, resting on three upstream theorems: `exceptionalDirichletZero_unique_zeroFreeRegion` (Landau–Page type), `chebyshevPsiProgression_relative_error`, and `primeCount_relative_error_of_psi_relative_error`.

**The strength ceiling of this chain is the Landau–Page unique exceptional zero plus one class of zero-free region, i.e. Linnik's theorem (1944).**

### 3.4 Only nine empty slots

The entire library contains nine occurrences of `: Prop := True`, spread over eight files:

```
SatakeParameters/SwOn.lean:1
TypeConditions/TrivialLocalCondition.lean:2      (UnusedSlot55, NoCondition)
LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:1   (UnusedSlot72)
ProjectiveLattices/ValSetAlgSubset.lean:1
ProjectiveLattices/RegPFree.lean:1
HeightDefect/OrderValuation.lean:1
LatticeFrames/NotInhAbsOfGamLe.lean:1
LatticeFrames/IsScaleWithBoundedGamma.lean:1
```

The one inside `EveryCharacterOfLiteratureOfVWin.lean:505-506`:

```lean
theorem siegel_eisenstein_simple_pole (O) : GlobalTheory.Published.UnusedSlot72 :=
  trivial
```

with its definition at `DiscreteSpectrumResidualClassification.lean:7`:

```lean
abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True
```

**These are openly declared empty slots, very few in number, and do not amount to a scale of "smuggling hypotheses".** Among the 196 wrappers, exactly one is `:= trivial` (the case above).

## §4 Three Retractions

### 4.1 `SizeWindows` is not an island

`ChCore.lean:367-370` explicitly constructs and uses `SizeWindows`, and `ch_core` is on the main chain (`core_gm` calls it). **Therefore `SizeWindows` is on the main chain.**

But the `SizeWindowBrackets` directory has two layers that must be separated:

- **The core** (`SizeWindows` plus `proposition_size_bound`): alive, used by the main chain;
- **The shell** (`GrowthBoundGivesRiemannHypothesis`, `GrowthInequalityDataExists`, `RiemannHypothesisOfBalanceAndGrowthData`): still `def : Prop`, neither proved nor used by the main chain.

### 4.2 `Green` is not an external parameter

From `SiegelEisensteinSecondTermHypotheses.lean:72`:

```lean
UpperTheory.Top.every_character_of_green_v_win
  (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters)
  hV
  (UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL ...)
```

`Green` is generated from `P.greenRegularCharacters`, where `P` is slot 1 filled by the 196 wrappers. **Hence all three arguments of `plugWin` are derivable from the literature heap; none is an extra hypothesis.**

### 4.3 The strength of `TLift_k` does not rest on `swFull`

See §3.1. It rests on `pairEx` (existence of a pair) together with a string of "existence of lift" statements: `BrEx`, `RealPair`, `NonVan`, `LiftAut`, `ProjEx`, `ReadLift`. **These are existing structures of theta correspondence, not RH-level.**

## §5 Strength Ledger: the whole proof reduces to one statement

Compress the sixteen layers and only one proposition remains:

\[
G_x \;\le\; x^{\,1/2+\varepsilon}\quad (\forall \varepsilon > 0)
\]

The relation among `Gx`, `Gm` and `Gz` is `Gm = Gz + Σ wt·gChi`, with `Gx` being the character-family version of `Gm`.

The step from here to RH is performed by `ChebyshevGrowthImpliesZeroFree` (`ExplicitFormulaErrorOfHostConditions.lean:40-41`):

```lean
def ChebyshevGrowthImpliesZeroFree : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y0 : ℝ, (∀ y ≥ y0, Λ.Gm y ≤ y ^ θ) → Λ.ZeroFreeAbove θ
```

**"Growth of `Gm` controlled by `y^θ` implies a zero-free region `Re s > θ`". This is the Landau-type explicit-formula method, and the conversion is mathematically correct.**

So the whole chain is equivalent to:

1. proving `Gm(y) ≤ y^(1/2+ε)` for every `ε > 0` (done by `core_gm`, under `EAtH`/`CoreAtH`);
2. using the Landau conversion to tighten the zero-free region from `1/2+ε` to `1/2` (done by `level_of_tiedWin`).

**Step 1 is an equivalent form of RH; step 2 is a tautological trick. Hence all the weight is in step 1, and step 1 lands on `core_gm` → `ch_core` → `proposition_size_bound`.**

### 5.1 Full provenance of `1/2`

`1/2` is neither an input nor a "derived result"; it is an assumption that floats, after arithmetic, into the position of a constant in the conclusion:

1. `SizeWindows`'s `hm1 : x^(1/2-ε) ≤ m` (an assumption);
2. `hxX` in `proposition_size_bound`: from `hm1` get `x ≤ x^(1/2+ε)·m` (`:522-526`);
3. elementary inequalities carry this single `1/2` into `Gx ≤ x^(1/2+(C+3)ε)`;
4. `core_gm` turns it into `Gm ≤ x^(1/2+(eD+eL+7)ε)`;
5. `level_of_tiedWin` uses `θ → 1/2+δ` to compress it to `ZeroFreeAbove(1/2)`.

This is structurally identical to our own `proposition_size_bound_alpha`: the threshold `α ≥ 1/2` comes from `1 ≤ 2α + 3ε/2`, and the side `α = 1/2` is precisely `hm1`.

**Conclusion: `m` is not constrained to √x by arithmetic; it is pinned there by one conjunct of `SizeWindows`.** So supplying a different value (not 1/2) does yield a "different RH" — that is, a different zero-free abscissa constant. On this point the original intuition was correct.

### 5.2 Why there is no trace

The brick list contains Landau (1918), Page (1935), Linnik (1944), Vinogradov (1958), Siegel (1935), Weil (1964), Deligne (1974), Fargues (2010s). **Not one item is new mathematics after 1944.**

Formalizing old theorems leaves no trace in the mathematical world; it leaves engineering volume in the Lean community. So "ninety years without a trace" is not an anomaly but an **inevitability**: the bricks were old to begin with.

**But this yields an unavoidable corollary: if every brick's strength ceiling sits in 1944, they cannot imply RH. Hence if the chain really outputs RH, some point must carry strength above the bricks.**

Three suspects, by position:

1. **The `hθ` branch of `primesRel_holds`** (`PrimesInProgressionsRelativeError.lean:36-40`) — checked; it takes the weak branch, not a relaxation.
2. **The seven hypotheses of `ch_core`** (`HostFactsS`, `SizesA`, `ThinScales`, `CostWindows`, `RestSize`, `CharsA`, the `gapA` bound) — **the prime suspect, not yet checked**.
3. **The forty fields of `HypsAlt`** (`Hyps.lean:22-90`) — of type `Type 1`, holding data plus conditions, with no occurrence of "zero", but the actual strength of `aAtG`, `irrC`, `zL`, `tie` remains unchecked.

**Note that `:419` extracts a component of `HostFactsS` as `hS.2.2.2.2.2.1` — five levels of nesting followed by a projection.** That notation indicates a deeply nested data packet, fields taken positionally. **Such structures are the easiest place to hide strength: if any one component at any level is wider than the literature statement, nobody can see it.**

## §6 What to Learn, What to Change

### 6.1 Three things to learn

**First, interface discipline.** `ZeroFreeOn` writes `1/2` into its definition body, so any producer of `ZeroFreeAll` must genuinely secure `Re s > 1/2`. This idiom is clean: it leaves no room for a "take the limit" bypass. If we formalize our own chain, we should follow it: **put the constant to be proved inside the definition, not in a parameter.**

**Second, the assembly technique of struct filling plus a single closing call.** 196 wrappers → 6 packages → one `Nonempty Hyps` → three arguments feeding `plugWin`. This way of organizing -- multi-layer structure filling, one closing invocation -- is the only feasible architecture for a large formalization.

**Third, the correct use of the Landau conversion.** `ChebyshevGrowthImpliesZeroFree` is a legitimate "growth control implies zero-freeness" step, and it quantifies over all `θ ∈ (0,1)` without presupposing RH. This is a usable tool theorem.

### 6.2 Three things to change

**First, the position of `hm1`.** In their chain, "`m` is of order √x" is an assumption; in QRH it must be **derived**. If our scheme can compute the order of `m` rather than choose it, that is the genuine point of difference.

**Second, do not treat `1/2` as an endpoint.** Their `α = 1/2` is a threshold lower bound (`1 ≤ 2α + 3ε/2`), so `α` can only be `≥ 1/2`, and larger values give a weaker conclusion. **For QRH to stand alone, it must supply a mechanism in which `1/2` arises from intrinsic structure**, not from "choosing a parameter close to 1/2".

**Third, avoid the overlap zone with Alpöge.** They occupy the highway "automorphic + theta lift + Landau conversion". If we take the theta route too, we merely become a weak version of the same framework. **The independent target for QRH remains that one: exhibit inside `SizeWindows` a tuple $(m,k,n,nT,nT2,b,a_E)$ with $Gz(x) \le x^{1/2+\varepsilon}$, where the order of `m` is determined by arithmetic rather than stipulated.**

**But honesty is required: that target is still phrased as "exhibit a witness", not "prove a theorem".** The difference: they assume `m ~ √x` and then carry out the entire derivation; what we must do is **first prove that `m` must be of order √x**. Once that holds, `1/2` turns from an assumption into a conclusion, and only then is it a genuine independent contribution.

### 6.3 Recommended positioning

Given the current evidence:

1. **Read through Alpöge's `ch_core` and its seven hypotheses first** (their only mathematical load-bearing point, and the likeliest place for hidden strength). Understanding it is how we learn which segment of the bridge is real.
2. **QRH should make no RH claim for now**; reframe it as a "zero-side constant mechanism" project: study whether the order of `m` can be derived from structure.
3. **Postpone the formalization route** until the open items in §7 are cleared.

## §7 Open Checks

Ordered by priority; each item carries an executable next step.

| Priority | Open item | Location | Criterion |
| --- | --- | --- | --- |
| P1 | Can the seven hypotheses of `ch_core` be truly constructed | `ChCore.lean:347-350` | each hypothesis has an independent proof body |
| P1 | The five-level nested fields of `HostFactsS` | `hS.2.2.2.2.2.1` at `:419` | unfold level by level; look for a component wider than literature |
| P2 | Strength of `aAtG`/`irrC`/`zL`/`tie` in `HypsAlt` | `Hyps.lean:73-87` | compare item by item with the literature source |
| P2 | Position of `le_refl` inside `size_windows_split` | `ChCore.lean:369` | decide whether `hm1` is self-certified or derived |
| P3 | The conversion in `CharacterBalanceMoves.core` | `ChCore.lean:440` | check whether `hY → hc'` adds anything |
| P3 | Provenance of the constant 4 in `one_char` | `ChCore.lean:419` | confirm that `4X` is not a new hypothesis |

## Appendix A Key Files

| File | Role |
| --- | --- |
| `Main.lean` | top-level target |
| `CharacterBoxes/EveryCharacter.lean` | definition of GRH-L |
| `ThirdPlaceSeries/TopPlug.lean` | exit packaging |
| `TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` | definition of `ZeroFreeOn` |
| `TotientGaloisClasses/Window.lean` | `FormBAt`, `HasWindows` |
| `TotientGaloisClasses/TopWin.lean` | `level_of_tiedWin` |
| `PrimitiveCosets/CoreGm.lean` | `core_gm` |
| `PrimitiveCosets/WindowInequalityOfArtinInputs.lean` | window inequality |
| `DedekindLFunctions/LandauTheorems/ChCore.lean` | `ch_core` |
| `ChainSlopeWindows/LipschitzWeightAndMinimum.lean` | `proposition_size_bound` |
| `ThetaKernels/GalTPDefs.lean` | `Tools_k`, `TLift_k` |
| `HalfIndexLattices/TLiftK.lean` | `TLiftK` |
| `ThetaParseval/SchurStep.lean` | `IsLift` |
| `ThetaParseval/ThetaKernels/ThkBaseStmtX.lean` | `SWFullX_k` |
| `TypeConditions/TrivialLocalCondition.lean` | empty-slot factory |

## Appendix B Reproduction

Open the corresponding files by `path:line`. Full-library scans:

```powershell
# empty slots
rg -n ": Prop := True" "F:\F\BSD_GRH_RH\RH_14\lean\src" --glob "*.lean"

# trivial proof bodies
rg -n "^\s*trivial\s*$" "F:\F\BSD_GRH_RH\RH_14\lean\src" --glob "*.lean"
```

The declaration index cache `_declidx.pkl` lives in `C:\proj2\_rh14_zeroside`, shaped as `short name -> [(kind, full_name, path, start_offset, end_offset)]`, reusable to avoid a full rescan.
