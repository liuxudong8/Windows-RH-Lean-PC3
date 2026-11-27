# The Alpöge–Claude Library Main Chain: A Two-Ledger Summary

This note succeeds No. 08, *Layer-by-Layer Anatomy of the Main Chain*. No. 08 cut the source open layer by layer and answered "what does it stand on". This one compresses it into a ledger and answers "how far does it actually stand". The only difference is scope: No. 08 read source only; here the machine measurements from notes 17–20 and 23 are folded in, so one chain now carries two distinct completion levels.

## §0 One-sentence conclusion

**Source side: 16 layers with no gaps, 1/2 written into the definition body, load-bearing weight confined to `ch_core` and `proposition_size_bound`, and the mathematical ceiling of the whole chain is 1944. Machine side: the closure of `Main.lean` is 175,191 library files and 1.03 GB of source, the whole library ships 175 oleans (0.0999%), the top level was never compiled, and a dense build of 245 artifact-missing files gives 189 pass and 56 fail.**

The two ledgers do not contradict each other; they measure different things. One asks whether what was written reads correctly; the other asks whether what was written runs.

## §1 The two-ledger table

| Item | Source side (read) | Machine side (compile) |
| --- | --- | --- |
| Closure size | 175,191 library files | 1,030,531,854 B of source; 175 oleans |
| Coverage | all 16 layers carry proof bodies | \(175/175{,}191 \approx 0.0999\%\) |
| Top level | `riemannHypothesis` exists in `Main.lean` | no `Main.olean`; never built |
| Gaps | static scan: zero `sorry`; nine `: Prop := True`; one `:= trivial` | compilation receipts cannot confirm or deny gaps |
| Dense build | — | 245 files: 189 pass (77.1%), 56 fail |
| Failure shape | — | 3 root errors, 53 cascades, amplification 1 : 54 |
| `RowSrc` subtree | 66,168 files, 197 dependency layers | 200 sampled at layer one already show 5 hard errors, blocking 1,313 files |

All five hard errors sit in elaboration (instance synthesis, implicit-argument inference, `rewrite` mismatch, heartbeat timeout); none is a false proposition. That fingerprint says more than any single number: **the code was written, not run.**

## §2 Five compressed stages

Sixteen layers need not be read one by one; five stages suffice.

| Stage | Layers | Claim | Source evidence | Machine state |
| --- | --- | --- | --- | --- |
| S1 | L1–L4 | top goal reduced to GRH-L | `rh_of_every`, three lines, \(\chi=1\) | upstream unbuilt |
| S2 | L5–L9 | seven-slot assembly emits `ZeroFreeAll` | `TopPlug` + `EveryCharacterOfLiteratureOfVWin` | upstream unbuilt |
| S3 | L10–L14 | window inequality to growth control | `la` is window width; \(\theta \to 1/2+\delta\) | upstream unbuilt |
| S4 | L15 | three-part assembly | `ch_core`, about 100 lines | closure contains a 66,168-file subtree, unbuilt |
| S5 | L16 | pure arithmetic | `proposition_size_bound`, 86 lines | unbuilt |

S1 to S3 are interface transport. `EveryCharacter` is GRH-L verbatim, and `ZeroFreeAll` unfolds to

\[
\forall \psi\, \forall s,\quad \tfrac{1}{2} < \operatorname{Re} s \;\Rightarrow\; L(\psi.\chi, s) \neq 0
\]

The \(1/2\) is not in the arguments; it is in the body of `ZeroFreeOn`. That is clean design: any theorem producing `ZeroFreeAll` must already have zero-freedom for \(\operatorname{Re} s > 1/2\), and no limiting argument slips past the type checker. The \(\theta \to 1/2+\delta\) trick in S3 is also legitimate — `ZeroFreeAbove(1/2+δ)` for every \(\delta>0\) does support `ZeroFreeAbove(1/2)` without ever setting \(\theta = 1/2\).

## §3 The three load-bearing pieces

### 3.1 `ch_core`: one hundred lines, one rearrangement

`ChCore.lean:343-351` is the signature; `:352-442` the proof. Four lines carry the weight:

```lean
:426  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x
:440  have hc' := CharacterBalanceMoves.core ... hTop hY
:441  have hz := proposition_size_bound _ _ _ _ _ _ _ _ _ _ _ G hW hc'
:442  linarith
```

The `G := GmA − SigA` at `:426` shows that the `+ SigA` in the conclusion is not an unabsorbed error term but a rearrangement. `:367-370` constructs `SizeWindows` on the spot from `hSize` (that is, `RestSize`), `hm` and `hxm`. The rest is elementary estimation — `Real.log_le_rpow_div`, `mul_le_mul_of_nonneg_left`, `linarith`.

### 3.2 `proposition_size_bound`: 86 lines of tautological arithmetic

Starting at `LipschitzWeightAndMinimum.lean:507`. The hypothesis `hW` splits into 16 components, exactly the 16 conjuncts of `SizeWindows`, no more and no fewer. The only entrance for \(1/2\) is at `:522-526`:

```lean
have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m
```

It uses only `hm1 : x^(1/2-ε) ≤ m`; `hm2` never appears in this proof. The rest is size shuffling by `ring` and `linarith`, landing on

\[
G_x \;\le\; 4\,x^{1/2+\varepsilon} \;+\; 22\,P\,Y\,x^{\varepsilon}
\]

The constant 4 in the leading term comes from the `one_char` side (`:419`), not from inside these 86 lines. **Not one line here touches a zero-related fact.**

### 3.3 `core_gm` and the Landau transfer

The conclusion at `CoreGm.lean:12` is

\[
\Lambda.G_m(x) \;\le\; x^{\,1/2+(e_D+e_L+7)\varepsilon},\qquad \varepsilon>0 \text{ arbitrary}
\]

with only the two host conditions `EAtH` and `CoreAtH`. The step to RH shape is `ChebyshevGrowthImpliesZeroFree`:

\[
\Big(\forall y \ge y_0,\; \Lambda.G_m(y) \le y^{\theta}\Big) \;\Longrightarrow\; \Lambda.\text{ZeroFreeAbove}(\theta)
\]

That is the legitimate Landau explicit-formula transfer, quantified over \(\theta \in (0,1)\), assuming nothing about RH.

## §4 The full provenance of \(1/2\)

The \(1/2\) is neither an input nor a derived result; it is one hypothesis that floats, through elementary arithmetic, into the position of a constant in the conclusion:

1. `hm1 : x^(1/2-ε) ≤ m` in `SizeWindows` — **this is an assumption**;
2. `hxX` turns `hm1` into \(x \le x^{1/2+\varepsilon} m\);
3. the size lemmas carry this single \(1/2\) into \(G_x \le x^{1/2+(C+21/8)\varepsilon}\);
4. `core_gm` yields \(G_m \le x^{1/2+(e_D+e_L+7)\varepsilon}\);
5. `level_of_tiedWin` closes it to `ZeroFreeAbove(1/2)` via \(\theta \to 1/2+\delta\).

**So \(m\) is not constrained to \(\sqrt{x}\) by arithmetic; it is pinned there by one conjunct of `SizeWindows`.** Change that value and you get a different zero-free constant — which is exactly where the original intuition of note 08 held, and the only place where the chain genuinely needs external input.

## §5 The machine ledger

One, closure and artifacts. The full dependency closure of `Main.lean` is 175,191 library files and 1,030,531,854 B of source; the local `.lake/build/lib/lean` holds 175 oleans. Coverage \(0.0999\%\). **The top level has never been compiled.**

Two, dense build. Taking the union of eight subtrees and dropping already-built files leaves 245 files; 24.9 minutes of compilation gives 189 pass, 56 fail.

Three, failure shape. Only 3 of the 56 are root errors: `LocalRingCardinality/DataLevel.lean:137` (class A), `DegreeSingleAdd.lean:121` (class B), and `eGamE` at `NegOneNeOneUnitsZmodFour.lean:154` (class C, reduction divergence: all four experiments with `whnf` and `isDefEq` time out). The other 53 are cascades, all chained to `NegOneNeOneUnitsZmodFour` — **amplification 1 : 54**. This explains why the sampling view (200 samples, 2.5% hard-error rate) and the dense view (3/245, 1.22%) give different intuitions: a cascade paints one root error across a whole sheet of red.

Four, subtree check. `RowSrc.lean` is 6 lines with two `import`s, yet its closure is 66,168 files, 197 layers, 417 MB — 37.8% of the library. Of the 3,076 compilable files at layer one, a 200-file sample already shows 5 hard errors blocking 1,313 files. A full build at 18–22 s per file is 13.8 days single-threaded.

Five, the one root error fixed. `Formalism/GaloisCohomology/Statement.lean:97` (class D, instance-search collapse) is repaired with `abbrev LocH2`, `@[instance_reducible]` and `letI`: olean 779,984 B, EXIT=0. Classes A, B and C remain.

**How to read this: the numbers do not say "it is wrong", they say "it has not run".** Proposition truth cannot be read off source; it can only be compiled out. When it will not compile, every source-side conclusion drops to reference value.

## §6 Four corrections to note 08

1. **"The chain is closed at the type level, with no `sorry` and no `axiom`"** — downgraded to "statically no `sorry`/`axiom` gap in source; machine-verified: not verified". These are two different claims, and note 08 merged them into one.
2. **"The main chain has 9 layers" versus the L1–L16 table in §1** — internal contradiction; unified to 16.
3. **§5.2's "the prime suspect is the seven hypotheses of `ch_core` hiding strength"** — upgraded: the gap is not hidden strength but failure to compile to the bottom. The strength suspicion stays on the books (`aAtG`, `irrC`, `zL`, `tie` in `HypsAlt` are still not compared line by line against the literature), but it is no longer the main contradiction.
4. **§3.4's "only 9 empty slots"** — that count holds only for `: Prop := True` and is no evidence of compilability. Nine explicitly declared empty slots are indeed too few to constitute smuggled assumptions, but they say nothing about whether the chain builds.

The three retractions in §4 of note 08 (`SizeWindows` is not an island; `Green` is not an external parameter; `TLift_k` does not rely on `swFull`) **still stand** and are not touched here. They are source-level conclusions and independent of the machine level.

## §7 Handover to the two lines

**Three things worth learning.** First, write the constant to be proved into the definition body (`ZeroFreeOn`'s \(1/2\)), leaving no opening for a limiting argument. Second, struct filling plus single-point assembly: 196 wrappers into 6 packages, 6 packages into one `Nonempty Hyps`, then three arguments into `plugWin` — the only organisational form that holds up in a large formalisation. Third, the Landau transfer: growth control to zero-freedom, quantified over \(\theta\), directly reusable.

**Three things not to trust.** First, compile status: any claim of "closed" needs an olean and a `#print axioms` receipt. Second, guessed interfaces: proof bodies like `first | A | B | C` are interface matching, not reasoning. Third, unchecked deep data packets: `hS.2.2.2.2.2.1` picks a field five levels down by position, and one level wider than the literature would go unseen.

**For the BSD main line**: this line does not intersect the BSD ledger under `C:\proj2`. The BSD side continues its own G2/G5/ring-debt sequence; what this note contributes is two methodological rules — put constants in definitions, and require olean size plus `#print axioms` on every probe. The RH side stays on "stop investing", keeping only the class-D instance-search repair as engineering experience.

## Appendix A Key files

| File | Role |
| --- | --- |
| `Main.lean` | top-level `riemannHypothesis` |
| `CharacterBoxes/EveryCharacter.lean` | GRH-L definition |
| `TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` | `ZeroFreeOn`, `Gm`, Landau transfer |
| `TotientGaloisClasses/TopWin.lean` | `level_of_tiedWin`, `zeroFreeOn_of_tiedWin_cyc` |
| `DedekindLFunctions/LandauTheorems/ChCore.lean` | `ch_core` |
| `ChainSlopeWindows/LipschitzWeightAndMinimum.lean` | `proposition_size_bound` |
| `PrimitiveCosets/CoreGm.lean` | `core_gm` |
| `Formalism/GaloisCohomology/Statement.lean` | class D repaired (`LocH2`) |
| `LocalRingCardinality/DataLevel.lean` | class A open (`:137`) |
| `NegOneNeOneUnitsZmodFour.lean` | class C open (`:154` `eGamE`) |

## Appendix B Reproduction

```powershell
# closure and artifact counts
(Get-ChildItem 'F:\F\BSD_GRH_RH\RH_14\lean\src' -Recurse -Filter *.lean).Count
(Get-ChildItem 'F:\F\BSD_GRH_RH\RH_14\lean\.lake\build\lib\lean' -Recurse -Filter *.olean).Count

# dense build of 245 and classification
python C:\proj2\_rh14_zeroside\_build_down.py
python C:\proj2\_rh14_zeroside\_classify_down.py
```

The declaration index cache `_declidx.pkl` lives in `C:\proj2\_rh14_zeroside`, keyed by short name to `[(kind, full_name, path, start_offset, end_offset)]`.
