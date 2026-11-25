# 第 1 条执行报告：GRH / Dirichlet-L 接口核查

日期：2026-11-23　|　标的：`F:\F\BSD_GRH_RH\RH_14\lean\src`（175,187 文件 / 17,374,215 行）

---

## 一、四句结论

1. **归档里没有 `GeneralizedRiemannHypothesis` 这个名字（0 命中）。** GRH 写在 `Statements.lean` 里，名为 `DirichletLZerosOnLine`，并在 `Main.lean` 里是**定理**（`theorem LFunction_eq_zero_re`），对**任意模 N、任意特征 χ（含非本原）**成立。

   ```lean
   def DirichletLZerosOnLine : Prop :=
     ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
       0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
   ```

   这比我上一轮的估计更强：不只「覆盖 Dirichlet L」，连非本原特征都覆盖。χ₅（N = 5）属于可直接实例化的范围。

2. **但主定理闭包 = 174,791 模块**（全库本地模块 174,798），且 `Main` 还引了 20 个归档中不存在的模块与 `Batteries.Tactic.OpenPrivate`。这五条定理在本机**无法编译引用**。所以「GRH 免费到手」是假的——**结论层拿不到。**

3. **真正的收获不在结论，在叶子。** Dirichlet-L 的分析器官不在那颗巨石里，实测传递闭包小到可编译：

   | 模块 | 闭包（本地模块数） |
   |---|---|
   | `Development…IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder` | **291** |
   | `Development…GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion` | **29** |
   | `Development…GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus` | 424 |
   | `Development…GlobalInterpolation.ExplicitFormulaDirichletZerosRightHalf` | 343 |
   | `Development…IwasawaDecomposition.Psi0ZeroFreeRegionBound` | 298（缺 1 模块） |
   | `Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime`（`ASK`/`MAIN`） | 14 |
   | `Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible`（`colour_balance`） | 16 |
   | `Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis` | 18 |
   | `Formalism.LandauZeroFreeBounds.NoZeroComplex` | 68 |
   | `Main`（五条主定理） | **174,791** |
   | `Statements` | 1 |

4. **已落地一件**：把 `DirichletLZerosInWindowFiniteAndPosOrder` 剥成**零依赖模块** `DirichletLZeroWindow.lean`（7 条 Mathlib import，oleans 195,432 B），7 条定理全部 `[propext, Classical.choice, Quot.sound]`、0 error。其中 `finite_zeros` **就是** QRH 的 `zerosLChi5_bounded_finite`，而且严格更强：任意 q、任意 χ、任意窗口。

---

## 二、抽取为什么成立

那 5 条归档 import 全是冗余：定理体只用到 Mathlib 层的事实（解析恒等定理、紧集上的聚点、零点阶）。`zerosIn` / `zmult` 两个定义来自 `RayPrimes.lean`，同样只依赖 Mathlib。剥完只剩 7 条：

```
Mathlib.NumberTheory.LSeries.DirichletContinuation
Mathlib.NumberTheory.LSeries.Nonvanishing
Mathlib.Analysis.Analytic.Uniqueness
Mathlib.Analysis.Analytic.IsolatedZeros
Mathlib.Analysis.Analytic.Order
Mathlib.Analysis.Complex.Norm
Mathlib.Analysis.Normed.Module.Connected
```

两处 API 漂移（归档 v4.33.1 → 我方 v4.34.0-rc2）已修：

- `LFunction_apply_one_ne_zero` 在新 mathlib 里位于 `LSeries/Nonvanishing`（原文件没导入），且 `χ` 是隐式参数，须写 `(χ := χ)`；
- `Mathlib.olean` 聚合件在本机不存在，只能用具体模块 import（既有约束）。

修完 `BUILD_EXIT=0`，零 warning。

## 三、七条定理干了什么

| 定理 | 内容 | 对 QRH 的意义 |
|---|---|---|
| `finite_zeros` | 任意 χ、任意窗口 `zerosIn χ t T` 有限 | **就是** `zerosLChi5_bounded_finite` |
| `order_ne_top` | 零点阶有限（非 ⊤） | 重数可数 |
| `one_le_zmult` | 零点阶 ≥ 1（正的） | `pair_count_bound` 缺的另一半 |
| `finite_and_one_le_zmult` | 上面两条打包 | 一条引用搞定 |
| `analyticOff` / `exists_entire` / `ne_one_of_mem` | 解析性、去极点整函数化、零点不为 1 | 支撑件 |
| **`finite_zeros_of_eq_LFunction`** | **口径搬运件**：若 `f` 在窗口上逐点等于真实 L 函数，则 `f` 的零点集同样有限 | 让 `opaque LFun` 不必改动即可用 |

## 四、与 QRH 接线：只差一行

QRH 现状（三条）：

```
S7_1_Main.lean:66   opaque LFun : ℂ → ℂ
S7_1_Stage3.lean:700 def zerosLChi5UpTo (T) : Set ℂ := {z | z ∈ zerosLChi5 ∧ |z.im| ≤ T}
S7_1_Stage3.lean:706 axiom zerosLChi5_bounded_finite (T) : Set.Finite (zerosLChi5UpTo T)
```

两条路，请你拍：

**A（不动口径，一小时）** 用搬运件把 axiom 换成定理：

```lean
theorem zerosLChi5_bounded_finite
    (hL : ∀ z, LFun z = DirichletCharacter.LFunction chi5Dirichlet z) (T : ℝ) :
    Set.Finite (zerosLChi5UpTo T)
```

债务从「一整条平坦假设」降为「一条同一性 + 已证定理」。不碰 `opaque`，不动 2719 jobs 之外任何东西。

**B（修口径，一次性）** 令 `def LFun := DirichletCharacter.LFunction chi5Dirichlet`（`stage_3.lean:1155` 已有 `chi5Dirichlet : DirichletCharacter ℂ 5`），则 A 里的 `hL` 变 `rfl`，axiom 直接删。

**但 B 带一个必须一起处理的雷**：`S7_1_Main.lean:77` 的 `lfun_series`

```
∀ s, 0 < s.re → LFun s = ∑' n : ℕ, (chi5 n : ℂ) * n^(-s)
```

原始 Dirichlet 级数只在 `re s > 1` 收敛，Lean 在发散处取 0。所以这条对 `0 < re s ≤ 1` 的断言**真值是假**的。现在它是 `opaque` + axiom，没人发现；一旦 `LFun` 变成真实 L，它就立刻变成一条假的 axiom。修口径时必须同时把它改成 `1 < s.re`（或改走 Euler 积解析延拓）。

**建议：先 A。** 成本一小时、零风险、立刻少一条平坦 axiom；B 等 `lfun_series` 口径一起改，别让假 axiom 与真定义同时落地。

## 五、还能顺手抽的

`ExceptionalDirichletZeroUniqueZeroFreeRegion`（闭包 **29**）是唯一近乎零成本的另一片叶子，可能直接供 `Z_T` 的结构（例外零点唯一性）。抽它的代价是半小时；要不要抽，等你一起说。

## 六、三层标注

- **定理（机检）**：上表 7 条，`#print axioms` 全 `[propext, Classical.choice, Quot.sound]`，`BUILD_EXIT=0`。
- **数据（实测）**：闭包计数（本地 import 图 BFS，174,798 节点）、命中统计（175,187 文件 / 17,374,215 行）、`GRH` 缩写 10 命中全为 `GRHaar` 假阳性。
- **未验证**：`Main.lean` 五条定理的实际依赖（闭包 174,791 未编译，只有源码级静态 0 sorry 支撑），所以「GRH 已证」这句话我们**不背书**，与审计台的一贯口径一致。

## 七、A 方案落地（2026-11-23，本轮已写入并验收）

**动作**：`QRH zerosLChi5_bounded_finite` 由 axiom 改为 theorem，口径借外部已证定理，不动 `opaque LFun`。

- 搬运件：`C:\proj2\OrderPreservingBijection\DirichletLZeroWindow.lean`（7 条定理，公理全 `[propext, Classical.choice, Quot.sound]`，BUILD_EXIT=0）。
- 新语句：`theorem zerosLChi5_bounded_finite (χ : DirichletCharacter ℂ 5) (hL : ∀ z, LFun z = DirichletCharacter.LFunction χ z) (T : ℝ) : Set.Finite (zerosLChi5UpTo T)`，证法 = 集合等式 + `QRHZeroWindow.finite_zeros_of_eq_LFunction χ LFun hL 0 T`。
- 传染面：`pairCount_L1_bound`、`pair_const_eps_bias` 各加 `(χ)(hL)`，两个调用点同步；`zerosLChi5_bounded_finite` 全库唯一下游链仅此两处。

**实测验收（不是推断）**

| 项 | 结果 |
|---|---|
| 单编 `QRH\S7_1_Stage3.lean` | EXIT=0，仅剩既有 deprecated 警告（自己引入的两条已修：`Set.mem_setOf_eq`→`Set.mem_ofPred_eq`、去掉未用的 `and_assoc`） |
| 全量 `lake build QRH` | **3624 jobs，0 error**（2719→3624 增量系新增 Mathlib 依赖闭包） |
| `#print axioms QRH.zerosLChi5_bounded_finite` | `[propext, Classical.choice, Quot.sound]` —— **该 axiom 已消失** |
| `#print axioms QRH.pairCount_L1_bound` | `[propext, Classical.choice, QRH.N_L, QRH.N_L_lower_bound, QRH.pair_count_bound, Quot.sound]` |
| `#print axioms QRH.pair_const_eps_bias` | 同上 |

**债务形态的变化（必须写清，别自我美化）**

- 之前：一条平坦 axiom「L(s,χ₅) 零点在紧竖带内有限」——不可证、不可审、也因此不可攻。
- 现在：一条同一性假设 `hL : LFun = DirichletCharacter.LFunction χ` + 一条已证定理（外部件，公理干净）。债务从「数学事实的假定」降为「定义口径的假定」。
- `hL` 本身仍未消解，它是 B 方案（`LFun := DirichletCharacter.LFunction chi5Dirichlet` 真定义）的入口；且 B 方案必须与 `S7_1_Main.lean:77 axiom lfun_series` 一并改口径（该条断言 `0 < s.re` 时级数收敛，在 `0<re≤1` 真值为假）。

**残余 axiom 清单（Stage3 侧，6 → 5）**

`n2_linkage`、`n3_remainder_uniform`、`N_L`、`N_L_lower_bound`、`pair_count_bound`（`zerosLChi5_bounded_finite` 已出账）。

---

## 八、B 方案落地：`opaque` → mathlib 真定义（2026-11-23）

A 方案把「零点局部有限」从 axiom 降为「同一性 + 已证定理」；本节把那条**同一性**本身也消掉。

**改了什么（4 处结构性改动，零数学假设）**

| 文件:行 | 旧 | 新 |
|---|---|---|
| `S7_1_Main.lean:62` | `opaque chi5 : ℕ → ℝ` | `noncomputable def chi5 := fun n => (chi5Dirichlet (n : ZMod 5)).re` |
| `S7_1_Main.lean:66` | `opaque LFun : ℂ → ℂ` | `noncomputable def LFun := fun z => DirichletCharacter.LFunction chi5Dirichlet z` |
| `S7_1_Stage3.lean:710` | `zerosLChi5_bounded_finite (χ) (hL) (T)` | `zerosLChi5_bounded_finite (T)` |
| `S7_1_Stage3.lean:975 / 1339` | `pairCount_L1_bound` / `pair_const_eps_bias` 各带 `(χ) (hL)` | 参数删除，调用点同步 |

`chi5Dirichlet`（`OrderPreservingBijection/stage_3.lean:1155`，`MulChar.ofUnitHom chi5UnitHom`）的乘法性由 `chi5UnitFun_mul` 的 16 情形枚举证出，全链公理干净。`S7_1_Main` 因此新增 `import OrderPreservingBijection.stage_3` 与 `import Mathlib.NumberTheory.LSeries.DirichletContinuation`；**无 import 环**（`OrderPreservingBijection` 侧不 import `QRH`）。

**审计（`_b_ax.lean` / `_b_ax.txt`）**

| 打印 | 结果 |
|---|---|
| `#print axioms QRH.zerosLChi5_bounded_finite` | `[propext, Classical.choice, Quot.sound]` —— **零 axiom，无条件定理** |
| `#print axioms QRH.pairCount_L1_bound` | 3 基础 + `N_L`、`N_L_lower_bound`、`pair_count_bound` |
| `#print axioms QRH.pair_const_eps_bias` | 同上 |
| `#print axioms QRH.s71_main` | 3 基础 + `bgs3_pair_expansion`、`bgs5_khat_fourier_supp` |

全量 `lake build QRH`：**3834 jobs / 0 error**（3624 → 3834，因 Main 拉入 `stage_3` 闭包）。

**债务形态**

- 旧：`opaque LFun` + `opaque chi5` 两个不透明载体，任何关于「它就是 χ₅ 的 L 函数」的说法都只能挂在 axiom 上。
- 新：`LFun` 就是 mathlib 的 `DirichletCharacter.LFunction χ₅`，`chi5` 就是 `chi5UnitHom` 的实投影。所有引用它们的定理（`zerosLChi5`、`zerosLChi5UpTo`、配对和、`pair_const_eps_bias`）现在都站在真对象上。
- 唯一剩余口径洞：`lfun_conj_symm`（`S7_1_Main.lean:87`，真命题、仍 axiom）。mathlib **没有** `LFunction_conj`；证明路线：`1 < re s` 上 `LSeries χ₅` 系数为实 ⟹ `conj` 下逐项相等，再用 `χ₅ ≠ 1` 时 `LFunction` 在 `s ≠ 1` 全纯 + 解析延拓唯一性延到全平面。

**口径边界（不要夸大）**

- `LFunction` 与 `LSeries χ₅` 只在 `1 < re s` 一致；mathlib 的 `LSeries` 在 `re s ≤ 1` 被**定义**为 0。故原 `lfun_dirichlet_series`（`0 < re s` 口径）不是「待证」，而是**假命题**，已于增量⑪撤除，将来只能以 `1 < s.re` 形式回归。
- 本次只消除「定义口径」类假设；`N_L`、`pair_count_bound`、`bgs3_pair_expansion` 等**数学内容**类公理一条未动。

---

## 九、`vonMangoldt` 真定义（2026-11-23，B 方案续）

**改动一处**：`S7_1_Main.lean:115`

```lean
-- 旧
opaque vonMangoldt : ℕ → ℝ
-- 新
noncomputable def vonMangoldt : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
```

配套 `import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`（mathlib `:65`，`Λ n = if IsPrimePow n then Real.log (minFac n) else 0`）。

**审计**：全量 `lake build QRH` **3834 jobs / 0 error**；`_b_ax.txt` 公理集与增量⑫完全一致（`zerosLChi5_bounded_finite` 零 axiom；`s71_main` = 3 基础 + `bgs3_pair_expansion`、`bgs5_khat_fourier_supp`）——即这一刀**不产生 axiom 缩减**，它产生的是**工具面**。

**为什么还值得做**：`primePowerSum` / `landau_explicit_L` / `siegel_walfisz_chi5` 里的 Λ 从此是 mathlib 的真对象，可挂以下引理：

| 引理 | 用途 |
|---|---|
| `vonMangoldt_apply` / `vonMangoldt_apply_prime` | 把 Λ 具体算成 `log p`（素数处非零判定） |
| `vonMangoldt_nonneg` / `vonMangoldt_le_log` | 逐项界，支撑部分求和与显式公式余项估计 |
| `vonMangoldt_ne_zero_iff` / `vonMangoldt_eq_zero_iff` | 支撑集 = 素数幂集，限定求和范围（省掉「非素数幂项为 0」的假设） |
| `vonMangoldt_sum`、`log_mul_moebius_eq_vonMangoldt` | Λ–ζ–log 三者的乘性关系，PNT-in-AP 的标准入口 |

**边界**：mathlib 到 2026-11 仍**没有** PNT in AP（`ψ(x; q, a)` 的 Siegel–Walfisz 型估计），故 `siegel_walfisz_chi5` 依旧是 axiom；本节只把它的**系数侧**（Λ 与 χ₅）全部钉到真对象，剩下的是纯粹的分布估计。

---

## 十、`logDerivTerm` 真定义（2026-11-23，B 方案续二）

**改动一处**：`S7_1_Main.lean:138`

```lean
-- 旧
opaque logDerivTerm (r : ℝ) : ℝ
-- 新
noncomputable def logDerivTerm (r : ℝ) : ℝ := (logDeriv LFun (r : ℂ)).re
```

配套 `import Mathlib.Analysis.Calculus.LogDeriv`（mathlib `logDeriv f := deriv f / f`，`𝕜 = 𝕜' = ℂ`）。

**审计**：全量 `lake build QRH` **3834 jobs / 0 error**；`_b_ax.txt` 与增量⑫⑬逐字一致——`zerosLChi5_bounded_finite` 零 axiom，`s71_main` 仅 `bgs3_pair_expansion` + `bgs5_khat_fourier_supp`。**这一刀同样不缩减 axiom**。

**口径边界（关键，别自我表扬）**

`(logDeriv LFun r).re` 之所以是「(L′/L)(r,χ₅) 的实数值」，前提是实点处 `LFun` 与 `deriv LFun` 都取实值——这正好由 `lfun_conj_symm` 推出。所以：

- 这一刀**没有**消掉任何 axiom，它把 `logDerivTerm` 从「抽象未知量」变成「有明确数学内容的表达式」；
- 同时它把 `lfun_conj_symm` 从「一条可选的对称性」变成**口径的硬前提**：不证它，`logDerivTerm` 的实数解读就是未证断言。

**`lfun_conj_symm` 的证明料齐了（三步，mathlib 侧已落实可引）**

1. **系数实**：`∀ n, (chi5Dirichlet (n : ZMod 5)).im = 0`。料在 `OrderPreservingBijection/stage_3.lean`——`chi5UnitFun` 的 16 情形枚举（`chi5UnitFun_val`、`chi5_multiplicative` 已在）。
2. **`1 < re s` 上逐项共轭**：`LFunction χ s = LSeries χ s`（`LFunction_eq_LSeries`）＋ `LSeries χ (conj s) = conj (LSeries χ s)`（需自证：`(n:ℂ)^{-conj s} = conj ((n:ℂ)^{-s})`，用 `Complex.cpow_conj`／`conj_tsum`；mathlib 无现成 `LSeries_conj`）。
3. **延拓**：`s ↦ LFunction χ s` 与 `s ↦ conj (LFunction χ (conj s))` 在 `{s ≠ 1}` 全纯（`differentiableAt_LFunction`，需 `χ₅ ≠ 1`），在开连通集 `{1 < re s}` 上相等 ⟹ 由解析函数唯一性延到 `{s ≠ 1}`；`s = 1` 由 `χ₅ ≠ 1` 时 L 在 1 全纯补上。

工作量估计：第 1 步 1h 内（枚举件已在，只差「`im = 0`」的收口）；第 2 步 1–2h（`tsum` 共轭与 `cpow` 共轭的手工装配）；第 3 步 1–3h（唯一性定理的调用形态要试对 `AnalyticOnNhd` 版本）。合计 **半天量级**，且若要动 `χ₅ ≠ 1`（第 3 步前提）另加 1h。

---

## 十一、`lfun_conj_symm` 第 ① 步：χ₅ 实数性（2026-11-23，真证）

**新模块**：`OrderPreservingBijection/Chi5Real.lean`（4 条定理，无 sorry/axiom）。

| 定理 | 内容 | 证明要点 |
|---|---|---|
| `chi5UnitFun_eq_one_or_neg_one` | `chi5UnitFun u = 1 ∨ = -1` | `unfold chi5UnitFun` + `split_ifs`（三分支：`u=1`、`u=4`、其余） |
| `chi5Dirichlet_eq_unit` | 单位点 `χ₅ ↑u = chi5UnitFun u` | `unfold chi5Dirichlet` + `MulChar.ofUnitHom_coe`（**关键**：`↑h.unit` 与 `h` 的原点定义相等，故 `χ ↑h.unit` 与 `χ h` 无需 rewrite） |
| `chi5Dirichlet_apply_im_zero` | `∀ x : ZMod 5, (χ₅ x).im = 0` | `by_cases IsUnit x`：单位点走 `chi5Dirichlet_eq_unit` + ±1；非单位点走 `MulChar.map_nonunit` |
| `chi5Dirichlet_eq_re` | `χ₅(n) = (χ₅(n)).re` | `Complex.ext`（`re` 恒等、`im = 0`） |

**QRH 侧接口自检**（`S7_1_Main.lean`，紧跟 `chi5` 定义）：

```lean
lemma chi5_eq_chi5Dirichlet (n : ℕ) : (chi5 n : ℂ) = chi5Dirichlet (n : ZMod 5)
```

即 B 方案里 `chi5 := fun n => (χ₅ (n : ZMod 5)).re` 的 `.re` 投影**不丢信息**——这是上一轮 `opaque → def` 的口径合法性证据，此前只能口头声明。

**审计**

- `_chi5real_ax.txt`：5 条 `#print axioms` 全部 `[propext, Classical.choice, Quot.sound]`；
- `sorry/admit/axiom/native_decide` 扫描：**0 命中**；
- 全量 `lake build QRH`：**3835 jobs / 0 error**（3834 → 3835，多编 `Chi5Real` 一个模块）。

**口径变化（诚实版）**

- `lfun_conj_symm` **仍是 axiom**，但内部结构从「三段全黑」变成「① 已证、② ③ 待攻」；
- 第 ② 步（`1 < re s` 上 `LSeries χ (conj s) = conj (LSeries χ s)`）现在有了唯一缺件之外的**全部前提**：系数实性由本节的 `chi5Dirichlet_eq_re` 提供；
- 摩擦记录：`(MulChar.ofUnitHom f x)` 无法用 `rfl`/`change` 直接展开（`FunLike` 强制转换不是定义透明），必须走 `IsUnit.unit` 的可定义相等 + `ofUnitHom_coe`；`rw [← hx.unit_spec]` 会因 motive 依赖 `hx` 而失败。

---

## 十二、`lfun_conj_symm` 第 ② 步：收敛半平面共轭（2026-11-23，真证）

**新模块** `OrderPreservingBijection/LSeriesConj.lean`（4 层，全部 `[propext, Classical.choice, Quot.sound]`）。

| 层 | 定理 | 内容 | 关键步骤 |
|---|---|---|---|
| 1 | `conj_eq_self_of_im_eq_zero` | `z.im = 0 ⟹ conj z = z` | `Complex.ext` + `conj_re`/`conj_im` |
| 2 | `term_conj_of_real_coeff` | `term f (conj s) n = conj (term f s n)` | `map_div₀`；`ℂ.cpow_conj`（需 `arg ↑n ≠ π`，由 `natCast_arg = 0` 与 `Real.pi_pos.ne` 给出）；`conj_natCast` |
| 3 | `LSeries_conj_of_real_coeff` | `LSeries f (conj s) = conj (LSeries f s)` | `tsum_congr` + `Complex.conj_tsum`；**无条件**（不需收敛假设） |
| 4 | `LFunction_conj_of_real_coeff` | `1 < re s ⟹ LFunction χ (conj s) = conj (LFunction χ s)` | `LFunction_eq_LSeries`（两侧都需 `1 < re (conj s)`，由 `conj_re` 给出） |

**QRH 侧落点**（`S7_1_Main.lean`，紧跟 `lfun_conj_symm` 之后）：

```lean
theorem lfun_conj_symm_of_one_lt_re (z : ℂ) (hz : 1 < z.re) :
    LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z)
```

审计：`_conj_ax.txt` 四条 `#print axioms` 全为 `[propext, Classical.choice, Quot.sound]`；`LSeriesConj.lean` 无 sorry/admit/axiom（唯一 `axiom` 字面出现在文档字符串里）。全量 `lake build QRH`：**3836 jobs / 0 error**（3835 → 3836）。

**口径变化（诚实版）**

- `lfun_conj_symm`（`∀ z`）**仍是 axiom**，但 `1 < re z` 一支已是定理，剩余负担是 `re z ≤ 1`；
- ⚠️ 这**不**立即改善链上的任何结论：`zerosLChi5 = {0 < re < 1 ∧ L = 0}` 恰落在剩余区间，`zerosLChi5_conj_closed` 仍然骑在 axiom 上。真正的收益在第 ③ 步之后才兑现。

**第 ③ 步（把 axiom 彻底去掉）的三件待办**

1. `χ₅ ≠ 1`（`differentiableAt_LFunction` 在 `s = 1` 处需要）：给 `n = 2` 处 `χ₅(2) = -1` 即可反驳「恒为 1」；料在 `stage_3.lean` 的 `chi5`,  需经 `chi5Dirichlet_eq_unit`/枚举转过去。
2. 解析性：`fun z => conj (LFunction χ (conj z))` 与 `LFunction χ` 都在 `{z ≠ 1}` 上全纯（`differentiableAt_LFunction` + `Complex.differentiable_conj` 的复合）。
3. 唯一性：两者在开连通集 `{1 < re z}` 上已相等（本节第 4 层）⟹ 由 `AnalyticOnNhd` 的唯一性定理延到 `{z ≠ 1}`；`z = 1` 由 `χ₅ ≠ 1` 时 L 在 1 也全纯补上。

估计 2–4 小时（第 3 步的调用形态需试 `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` 一族）。

---

## 十三、第 ③ 步前置·1：χ₅ 非平凡 + L 全纯（2026-11-23，真证）

`OrderPreservingBijection/Chi5Real.lean` 新增 3 条（合计 7 条），公理集全部 `[propext, Classical.choice, Quot.sound]`（`_chi5one_ax.txt`）。

| 定理 | 内容 | 证明 |
|---|---|---|
| `chi5Dirichlet_two` | `χ₅(2) = -1` | 单位 `u = ⟨2, 3, …⟩`（`2*3 = 6 = 1`）→ `chi5Dirichlet_eq_unit` → `chi5UnitFun_val` 强转到 ℂ → `(u:ZMod 5).val = 2` → `chi5 2 = -1`（`decide` + 强转） |
| `chi5Dirichlet_ne_one` | `χ₅ ≠ 1` | 若 `χ₅ = 1`，则 `χ₅(2) = -1` 变成 `(1 : MulChar) 2 = -1`；`MulChar.one_apply`（`2` 是单位）给 `= 1`，`norm_num` 撞出 `1 = -1` |
| `differentiable_LFunction_chi5` | `Differentiable ℂ (LFunction χ₅)` | `DirichletCharacter.differentiable_LFunction chi5Dirichlet_ne_one` |

第 3 条直接来自 mathlib（`differentiable_LFunction` 对非平凡特征成立）；它把「解析延拓唯一性」所需的「两侧全纯」在 `s = 1` 处也补齐了。

**审计**：`_chi5one_ax.txt` 三条全部只有 3 个基础公理；全量 `lake build QRH` **3836 jobs / 0 error**（与上轮同数，`Chi5Real` 模块本就在依赖里）。

**两处摩擦（下次会再遇到）**

1. `Units ℂ` 的 `DecidableEq` 走 `Classical.choice`（`Complex.instDecidableEq` 是 classical 的）⟹ `decide` **卡死在** `Classical.choice`，无法判定 `(if … then 1 else -1 : Units ℂ) = -1`。可行路径：先 `chi5UnitFun_val` 把值强转到 ℂ，再在 ℤ/ℕ 层用 `decide`（那里是计算型可判定）。
2. `if_neg` 在 2026-11 的 mathlib 已废弃（建议 `ite_eq_right`）；本项目内直接用 `simp`/`decide` 收口更稳，避免 deprecation 噪声。

**第 ③ 步剩余**（现在只剩「唯一性装配」）：

- 目标引理形态：`FunLike`/`AnalyticOnNhd` 层面——`LFunction χ₅` 与 `fun z => conj (LFunction χ₅ (conj z))` 在 `{z ≠ 1}` 上解析且相等，延拓到全平面；
- 已备齐的三块：① 系数实（`chi5Dirichlet_im_zero`）、② 收敛半平面相等（`LFunction_conj_of_real_coeff`）、③ 全纯（本节第 3 条 + `Complex.differentiable_conj`）；
- 待试的接口：`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` 一族（名字与参数形态需实测）。


## 十四、第 ③ 步闭环：`lfun_conj_symm` 由 axiom 降为 theorem（全平面，无条件）

**结论先行**：QRH 命名 axiom 从 **14 条降为 13 条**；`lfun_conj_symm` 与唯一使用点 `zerosLChi5_conj_closed` 的公理集实测均为 `[propext, Classical.choice, Quot.sound]`（`_conj_ax2.lean`）。全量 `lake build QRH` = **3836 jobs / 0 error**（`build_qrh_H.txt`）。

### 14.1 主定理（`OrderPreservingBijection/LSeriesConj.lean`）

```lean
theorem LFunction_conj_global {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : ∀ n : ℕ, (χ (n : ZMod N)).im = 0) (hne : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ (starRingEnd ℂ s)
      = starRingEnd ℂ (DirichletCharacter.LFunction χ s)
```

**证明结构**（与 mathlib `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:461` 的 `riemannZeta_conj` 同款，但省掉了 `s = 1` 的分情形）：

1. `hf_an : AnalyticOnNhd ℂ (LFunction χ) univ` ← `DifferentiableOn.analyticOnNhd` ∘ `DirichletCharacter.differentiable_LFunction hne`（χ ≠ 1 ⟹ **整函数**，无极点，这是省掉 `s=1` 分情形的原因）；
2. `hg_an : AnalyticOnNhd ℂ (fun z => conj (LFunction χ (conj z))) univ` ← `differentiableAt_conj_conj_iff.mpr`（`Mathlib/Analysis/Calculus/Deriv/Star.lean:123`）；反全纯件不需要 `Complex.differentiable_conj`（那只给 ℝ-可微）；
3. `hgz : 1 < z.re → conj (L (conj z)) = L z` ← 第 ② 步 `LFunction_conj_of_real_coeff` 两侧取共轭（`conj_conj`）；
4. `hev : conj∘L∘conj =ᶠ[𝓝 (2:ℂ)] L` ← `filter_upwards` + `(isOpen_lt continuous_const continuous_re).mem_nhds (1 < 2)`；
5. **唯一性**：`AnalyticOnNhd.eq_of_eventuallyEq hg_an hf_an hev`（`[PreconnectedSpace ℂ]` 版本，比 `eqOn_of_preconnected_of_eventuallyEq` 少两次 `mem_univ` 显式给参）；
6. 收口：`congrFun` + `congrArg (starRingEnd ℂ)`。

### 14.2 两个环境坑（不是数学问题）

| 报错 | 真因 | 修法 |
|---|---|---|
| `Unknown identifier 'differentiable_LFunction'` | 该名在 `namespace DirichletCharacter` 内，本文件未 `open` | 全限定 `DirichletCharacter.differentiable_LFunction` |
| `Unknown identifier 'eventuallyEq_of_mem'` | 它在 `namespace Filter`（`Mathlib/Order/Filter/Basic.lean:958`），zeta 模板文件顶部 `open Filter` 才有裸名 | 加 `open Filter`；或直接 `filter_upwards` 手搓 `=ᶠ` |
| `Unknown identifier '𝓝'` | 记号在 `scoped Topology` 里 | 文件头加 `open scoped Topology` |

### 14.3 QRH 侧落刀

```lean
theorem lfun_conj_symm : ∀ z : ℂ, LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z) := by
  intro z
  exact LSeriesConj.LFunction_conj_global OrderPreservingBijection.chi5Dirichlet
    OrderPreservingBijection.chi5Dirichlet_im_zero OrderPreservingBijection.chi5Dirichlet_ne_one z
```

零改动即成立：`LFun` 已是 `def`（`DirichletCharacter.LFunction chi5Dirichlet`），定义透明，无需 `simp [LFun]`；`chi5Dirichlet_im_zero`（§十三）与 `chi5Dirichlet_ne_one`（§十三）直接充当前两个前提。`S7_1_Main.lean:94-105` 原 `axiom` 行原位替换为 `theorem` + 新 docstring。

### 14.4 审计证据

- `_conj_ax2.lean`：
  - `QRH.lfun_conj_symm` → `[propext, Classical.choice, Quot.sound]`
  - `QRH.zerosLChi5_conj_closed` → `[propext, Classical.choice, Quot.sound]`
- `_conjglobal_ax.lean`：`LSeriesConj.LFunction_conj_global` → `[propext, Classical.choice, Quot.sound]`
- `_b_ax.lean` 三条无回归：`zerosLChi5_bounded_finite`（零 axiom）、`pairCount_L1_bound` / `pair_const_eps_bias`（3 基础 + `N_L`、`N_L_lower_bound`、`pair_count_bound`）、`s71_main`（3 基础 + `bgs3_pair_expansion`、`bgs5_khat_fourier_supp`）。
- 剩余 13 条 axiom 分布：`S7_1_Core:705 fourierCos_Khat`；`S7_1_Main:180/312/345/1145/1176/1179/1185`（`landau_explicit_L`、`siegel_walfisz_chi5`、`bgs5_khat_fourier_supp`、`bgs3_pair_expansion`、`bgs4_offcrit_split/low/high`）；`S7_1_Stage3:691/695/727/1390/1395`（`N_L`、`N_L_lower_bound`、`pair_count_bound`、`offcritSum`、`n3_remainder_uniform`）。

### 14.5 口径后果（诚实记录）

- `logDerivTerm` 的 `.re` 合法性此前挂 `lfun_conj_symm`；该 axiom 消失后，`logDerivTerm` 的**口径前提**随之成为已证定理 → `landau_explicit_L` 那一条的「无条件」色彩略增，但其本体仍是命名 axiom（Landau 显式公式），未降级。
- 本次**不缩减** `offCriticalError/offcritLow/offcritHigh/offcritSum`（4 个 opaque，BGS 引理 4 机制算子），也不动 Stage3 数论三件。


## 十五、`N_L` 数据型 axiom → 真定义（axiom 13 → 12）

**结论**：`S7_1_Stage3.lean` 原 `axiom N_L : ℝ → ℝ`（一条自由浮动的算子假设）换成

```lean
noncomputable def N_L (T : ℝ) : ℝ := ((zerosLChi5UpTo T).ncard : ℝ)
```

即「临界带内 `|Im z| ≤ T` 的零点个数」——`Set.ncard`（无穷集取 0，但本集对任意 `T` 有限：`zerosLChi5_bounded_finite`，故恒为真计数）。新增真证 `N_L_nonneg`（`Nat.cast_nonneg`）。

### 15.1 为什么这不是「换个名字」

原 `N_L` 是一条**数据假设**：它只说「存在某个实值函数叫 N_L」。`N_L_lower_bound` 与 `pair_count_bound` 因此只对「某个未知算子」成立，可以在有意选择该算子（例如取恒为 0、或取极大）时被绕开或变得空洞。改成真实计数后，两条 axiom 变成：

- `N_L_lower_bound`：`∃c>0, c·T·log T ≤ #{ρ : L(ρ,χ₅)=0, |Im ρ| ≤ T}`（RvM 主项方向的下界）；
- `pair_count_bound`：竖直差带内配对总数 `≤ Dcnt·#{ρ}`（RvM 密度 + 零点分离的直接算术）。

**这是加强，不是缩水**：陈述更难满足、不可退让，兑水空间被消掉。

### 15.2 落刀位置要求（踩坑）

定义必须引用 `zerosLChi5UpTo`，而后者原本排在 `N_L_lower_bound` 之后 ⟹ 直接把 `N_L` 改成 def 会撞「前向引用」。处理：

- 删 `axiom N_L`，原位留 `/- -/` 块注释（**注意**：不能留 `/-- -/` docstring，否则下一行是 docstring 时解析器报 `unexpected token '/--'; expected 'lemma'`——这是本项目第二次踩同一个坑）；
- `N_L` 定义移到 `zerosLChi5_bounded_finite` 之后（`:714` 定理 → `:733` 定义）；
- `N_L_lower_bound` 随之移到 `N_L_nonneg` 之后（`:738`）。

### 15.3 审计证据

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_J.txt`）。
- `_nl_ax.lean`：
  - `QRH.N_L` → `[propext, Classical.choice, Quot.sound]`
  - `QRH.N_L_nonneg` → 同
  - `QRH.pairCount_L1_bound` → `[propext, Classical.choice, N_L_lower_bound, pair_count_bound, Quot.sound]`（**`N_L` 这个名字从公理集里消失**，上一轮是 3+三件）
  - `QRH.pair_const_eps_bias` → 同上
- 命名 axiom 总数：**12**（Core 1 + Main 7 + Stage3 4：`N_L_lower_bound`、`pair_count_bound`、`offcritSum`、`n3_remainder_uniform`）。

### 15.4 下一步的真实难度（提前标定）

`N_L_lower_bound` 若要降级，需要 `L(s,χ₅)` 的 Riemann–von Mangoldt 计数（含 `arg` 连续化与幅角原理），是本工程里**第一条真正的解析数论活**，不是装配。`pair_count_bound` 依赖它 + 零点分离性。所以本轮到此为止是正确停点。


## 十六、撤除 N3 空条目（`offcritSum` + `n3_remainder_uniform`）：axiom 12 → 10

**这是清理，不是口径替换**：删掉的两条不携带任何数学内容，也不被任何证明引用。

### 16.1 判定依据（三步检查）

**第一步：使用面**。`offcritSum` 全库仅 2 处（自身声明 + `n3_remainder_uniform` 语句内）；`n3_remainder_uniform` 全库仅 1 处（自身声明）。**零下游引用**（与 `lfun_dirichlet_series` 同型死代码）。

**第二步：内容面（空）**。该对是「自由算子 `(ℝ→ℝ)→ℝ→ℝ` + 一条关于它的 `∃R` 有界声明」：

```lean
axiom offcritSum : (ℝ → ℝ) → ℝ → ℝ
axiom n3_remainder_uniform (T0 : ℝ) (hT0 : 1 ≤ T0) :
  ∃ R : ℝ, 0 ≤ R ∧ ∀ K : ℝ → ℝ, (∀ u : ℝ, 1 < |u| → fourierCos K u = 0) →
    Bound R T0 (fun T => |offcritSum K T|) (fun T => T * Real.sqrt (Real.log T))
```

取 `offcritSum ≡ 0` 即可同时满足：`|0| ≤ R·T·√logT` 在 `T ≥ T0 ≥ 1` 时成立（右端非负）。⟹ 该对无任何可推出或被推出的内容，属「账面上占位、数学上空转」。

**第三步：文档对象不可如实定义**。S7.5 的 `Roff` 不是「离线零点两两求和」，而是 BGS 配对公式**减去主项后的余项**：

- S7.5 §3.1 (iii)：`Roff = O((logT)^{-1/2})·N_L`；
- 其 `O(1/√logT)` 来自 `R(x,T)=∫₀ᵀ|r(x,t)|²dt`（GM87 引理 6/7），而「核只出现在零点侧 L(x,T)，经 L=R 恒等式吸收」（S7.5 §2.3）；
- 引理 5 本体（S7.5 `:25`）为 `Σ_{0<γ,γ'≤T} r̂(i(ρ−ρ')logT/2π)·w(ρ−ρ') = 主项 + O(T√logT)`。

本工程缺三件：`w(ρ−ρ')` 权重（代码中不存在）、复自变量 `r̂`（只有实自变量的 `Khat`/`fourierCos`）、`x` 尺度下的相减抵消。若按字面写「离线零点两两原始求和」：量级为 `O(#离线零点²)`，而 `#` 若为 `O(T logT)` 即 `O((T logT)²)`，与声明的 `O(T√logT)` 冲突 ⟹ **会写出假命题**。假命题比空条目危险得多，故不写。

### 16.2 落刀

- `S7_1_Stage3.lean:1405` 原「N3 节」两条 axiom 整块删除，原位留 `/-! ... -/` 说明（含上述三条理由 + 原语句存档，供复核、勿复活）；
- `S7_1_Main.lean:1265` 击破清单 `- [x] (N3)` 改为 `- [ ] (N3)` 并注明撤除理由；
- `S7_1_Stage3.lean:2138` 清单同步：`N_L_lower_bound` 单列（仍是 axiom），`n3_remainder_uniform` 划掉并注明撤除。

### 16.3 审计

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_K.txt`；改注释后复验同；第四刀后 `build_qrh_M.txt`；第五刀后 `build_qrh_N.txt`）。
- 列 0 的 `axiom` 声明数：**9**（`^axiom\s+` 正则，排除注释内的存档块；第四刀把 `bgs4_offcrit_split` 降 theorem 后由 10 降至 9；第五刀是结构接线，条数不变）。
- `_n3_ax.lean` 无回归：`pairCount_L1_bound` = 3 + `N_L_lower_bound` + `pair_count_bound`；`pair_sum_expansion` = 3 + `bgs3_pair_expansion`；`offcritical_small` = 3 + `bgs4_offcrit_low` + `bgs4_offcrit_high`；**`s71_main` = 3 + `N_L_lower_bound` + `bgs3_pair_expansion` + `bgs4_offcrit_low` + `bgs4_offcrit_high`（第六刀后 `bgs5_khat_fourier_supp` 已退出闭包，用户 axiom 由 5 条降至 4 条）**；`bgs4_offcrit_split`、`offcrit_remainder_le_one`、`zerosLChi5_bounded_finite` 见下条。
- opaque 仍 2 个（`offCriticalError`、`offcritLow`）——`offcritHigh` 已在第四刀改为 `noncomputable def`。注意 `offcritSum` 原本是 `axiom` 而非 `opaque`，此前台账把它算进「4 个 opaque」是记错，此处更正。

### 16.4 明账：N3 未形式化（不是被证掉）

**N3（离线项跨 λ 一致）在本工程中处于「未形式化」状态**，不是「已证」。补真的前置条件：

1. 引理 5 配对公式本体形式化（含 `w` 权重与复自变量 `r̂`）；
2. BGS 显式公式的 `x` 尺度参数进入 Lean 侧；
3. 主项相减口径（`Roff` 是余项而非总和）。

这三件都在「L 版 BGS 假设」层，属长线。在此之前的正确账目是：**9 条命名 axiom + 2 个 opaque + 1 条明确登记未形式化项（N3）**。

### 16.5 当前 9 条 axiom 分布

| 位置 | 条目 | 性质 |
|---|---|---|
| `S7_1_Core:705` | `fourierCos_Khat` | 连接件（`fourierCos Khat = Khat`） |
| `S7_1_Main:210` | `landau_explicit_L` | Landau 显式公式（L 版） |
| `S7_1_Main:342` | `siegel_walfisz_chi5` | PNT-in-AP 量级（模 5） |
| `S7_1_Main:375` | `bgs5_khat_fourier_supp` | 频域窄支撑（积分层；**已不在 `s71_main` 闭包内**，仍由 Stage3 `prime_sum_bound` 使用） |
| `S7_1_Main:1191` | `bgs3_pair_expansion` | BGS 引理 3（配对和展开；**第六刀固定核为 `Khat`**，离线项为具体项） |
| `S7_1_Main:1243/1250` | `bgs4_offcrit_low` / `_high` | BGS 引理 4 两段界（绝对常数；`split` 已降 theorem） |
| `S7_1_Main:121` | `N_L_lower_bound` | RvM 计数下界（**第五刀自 Stage3 上移**） |
| `S7_1_Stage3:729` | `pair_count_bound` | 竖直邻域配对计数 |


## 十七、`bgs3_pair_expansion` 口径手术（含 `s71_main` 连带）

### 17.1 缺陷（语句层，不是「未证」）

旧语句把 `pairConstant` 的归一化分母写成 `Real.log T / (2π)`，即：

```lean
pairConstant K δ (Real.log T / (2 * Real.pi)) zerosLChi5 = diag + prime + offcrit
```

而 `pairConstant K δ N Z := 1 + (Σ' p : ℂ×ℂ, …) / N`。后果有两重：

1. **δ 被当成零点数**：第三实参位置本是 `N`（零点计数，`N_L T ≍ (T/π)logT`），却传入 `δ = logT/2π`，归一化变成除以 δ（偏差约一个 `T` 量级）；
2. **在无穷集上求和**：`Z = zerosLChi5` 是整条临界带的零点集（无穷），`∑' p : ℂ×ℂ, if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then …` 在无穷集上是无意义/不可和的 `tsum`。

Stage3 侧的 `pair_const_eps_bias` / `pairCount_L1_bound` 早已改用正确口径（`N_L T` + `zerosLChi5UpTo T`），只有 Main 侧的引理 3 及其下游 `s71_main` 停留在旧口径。

### 17.2 修正后语句

```lean
axiom bgs3_pair_expansion (K : ℝ → ℝ) (δ T ε : ℝ) (hK : KernelAdmissible K)
    (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime offcrit : ℝ), 0 ≤ C₁ ∧
    pairConstant K δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offcrit ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1 ∧ |offcrit| ≤ 1
```

`s71_main` 结论同步改为 `pairConstant Khat (logT/2π) (N_L T) (zerosLChi5UpTo T) ≤ C_MT + C₁ε + C₂`；`QRH.lean` 根模块的自检 `example` 同步（原先也是旧口径，会 Type mismatch）。

### 17.3 结构性前置：定义上移（避免 import 环）

`N_L` / `zerosLChi5UpTo` 原在 Stage3，而 Stage3 `import QRH.S7_1_Main`，Main 不可反向 import。故把两件（含 `N_L_nonneg`）**上移至 `S7_1_Main`**（紧跟 `zerosLChi5` 之后）：

- `def zerosLChi5UpTo (T) : Set ℂ := { z | z ∈ zerosLChi5 ∧ |z.im| ≤ T }`
- `noncomputable def N_L (T) : ℝ := ((zerosLChi5UpTo T).ncard : ℝ)`
- `lemma N_L_nonneg (T) : 0 ≤ N_L T`

Stage3 只留注释占位（`zerosLChi5_bounded_finite`、`N_L_lower_bound`、`pair_count_bound` 仍在 Stage3，经 import 取得定义）。依赖方向变为 Main →（Stage3 单向依赖），无环。

### 17.4 语义后果（这是加强）

- 归一化分母从「δ」变为**真实零点计数**：`1 + (配对差和)/N_L T`，与 Stage3 的 `pair_const_eps_bias` 口径统一；
- 求和域从「整条无穷零点集」变为**有限截断集** `Z_T`：`tsum` 在有限集上自动退化为有限和，`Summable` 不再需要假设；
- `bgs3` 的算术内容变强（有限口径下 `diag + prime + offcrit` 的分解必须真的成立），且不再含「无穷集 tsum」这种无意义项。

### 17.5 审计

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_L.txt`）。
- `_s71_ax.lean`：`s71_main` = `[propext, Classical.choice, bgs3_pair_expansion, bgs5_khat_fourier_supp, Quot.sound]`（与手术前同集，未新增 axiom）；`pair_sum_expansion` = 3 + `bgs3_pair_expansion`；`N_L` = 3 基础（是定义）。
- 命名 axiom 总数 **9**；opaque **2**（第四刀后）。
- `pairConstant` 全库使用点复核：Main `:1170/:1178/:1241/:1248` 与 Stage3 `:1350-1376` 全部为 `(N_L T) (zerosLChi5UpTo T)` 口径，无残留旧形状（仅注释与历史行提及）。

### 17.6 手法备忘（第三次踩同坑）

删除/替换声明后，原位注释**必须**用 `/- -/`；若用 `/-- -/` 且下一条又是 docstring，Lean 直接报
`unexpected token '/--'; expected 'lemma'`（本轮在 Stage3 连撞两处）。


## 十八、第四刀：`bgs4_offcrit_split` axiom → theorem（`offcritHigh` 降为定义）

### 18.1 被切掉的是什么

旧账里 BGS 引理 4 的「切割分解」是一条 axiom：

```lean
opaque offCriticalError (T : ℝ) : ℝ
opaque offcritLow  (T : ℝ) : ℝ
opaque offcritHigh (T : ℝ) : ℝ
axiom bgs4_offcrit_split : ∀ s : ℝ, offCriticalError s = offcritLow s + offcritHigh s
```

问题不在「未证」，而在**语句的语法形态**：`offCriticalError`、`offcritLow`、`offcritHigh` 三者都不是某条真实数论对象的切片，而是三个自由算子；于是「余项 = 低频 + 高频」不是一条数学事实，而是一条**命名约定**。用 axiom 声明一个命名约定，效果等于「声明两个新名字相加等于原来的名字」——这条 axiom 既不可能被推翻（三个符号由我们任意指定），也不可能在证明里提供任何信息（它的唯一作用是把 `E` 换成 `low + high`）。

### 18.2 改法：把第二个名字定义成「剩下的部分」

```lean
noncomputable def offcritHigh (T : ℝ) : ℝ := offCriticalError T - offcritLow T
theorem bgs4_offcrit_split : ∀ s : ℝ, offCriticalError s = offcritLow s + offcritHigh s := by
  intro s; unfold offcritHigh; ring
```

这是**真的定义性分解**：先有 `E` 和低频段 `low`，高频段按「`E` 减去 `low`」命名。改名不改数学——`offcritical_small` 的证明（`abs_add_le` + `add_le_add` + `ring`，R = R₁ + R₂）一字未动，结论逐字相同。

### 18.3 内容有没有缩水

没有。`bgs4_offcrit_low` / `bgs4_offcrit_high` 两条 √log 段界仍在 axiom 层级（未证、未弱化），只是形状从「关于两个自由符号」变成「关于 `low` 与 `E − low`」。信息量守恒：由两段界仍推 `|E s| ≤ (R₁+R₂)√log s`，反之单独一条段界都推不出这个结论。

### 18.4 审计

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_M.txt`）。
- `#print axioms bgs4_offcrit_split` → `[propext, Classical.choice, Quot.sound]`（**纯三基础，公理级已清零**）。
- `#print axioms offcritical_small` → `[propext, Classical.choice, bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]`（`split` 已从集合中消失）。
- 列 0 计数：axiom **10 → 9**，opaque **3 → 2**（`offCriticalError`、`offcritLow` 仍在，理由见 18.5）。

### 18.5 顺手抓到的第二处口径缺口（未动，留给下一步拍板）

`offcritical_small` 在**全库零下游消费**：除 `S7_1_Main` 自身注释与探针 `_n3_ax.lean` 外，没有任何定理把它当引理用。同时 `bgs3_pair_expansion` 的文档注释写着「离线项 `|offcrit| ≤ 1`（引理 4 缩放：`offcritical_small` 除以 `N_L`）」——**这句是文档层承诺，形式层没有对应的连线**：`bgs3` 里的 `offcrit` 是 `∃` 绑定的自由实数，与 `offCriticalError` 无名可通。

两条可选收尾（都需先拍板，因为会动 `bgs3` 语句形状）：

1. **接线（推荐）**：把 `bgs3` 的 `offcrit` 从 `∃` 绑定改为具体的 `offCriticalError T / N_L T`，再用 `offcritical_small` + `N_L_lower_bound`（`N_L ≥ c·T·logT`）推出 `|offcrit| ≤ 1`（需 `(R₁+R₂)√log T ≤ c·T·logT`，T 足够大时成立，尾段用 `T₀` 截断）。代价：`bgs3` 语句改动 + `s71_main` 连带，收益是 L4 链第一次真正进入主定理的依赖闭包。
2. **退役**：与 N3 同款理由（零下游 + 对自由符号可满足）把 `bgs4_offcrit_low/high` 降为「未形式化机制」，账本变 7 axiom / 1 opaque。代价：合伙人文档里「BGS 引理 4 已移植」这句要改口径。

本刀**只做 (a) 的最小版本**（分解定义化），以上两条不动。


## 十九、第五刀：把 L4 链接进主定理（`bgs3` 离线项改为具体项）

### 19.1 病灶（并上节 18.5 指出的那条）

`bgs3_pair_expansion` 把离线项写成 `∃ offcrit, … ∧ |offcrit| ≤ 1`。这个 `offcrit` 是**由 ∃ 绑定**的自由实数，与 `offCriticalError` 无名可通；于是「离线项 ≤ 1」是公理里的一句话，而不是任何东西的推论。与此同时 L4 链（`offcritical_small`）在整个库里**零下游消费**——账本上「BGS 引理 4 已移植」这句话，形式层没有一条线把它接到主定理上。

### 19.2 改法（三处联动）

**(1) `bgs3` 离线项改为具体项**：

```lean
axiom bgs3_pair_expansion (K : ℝ → ℝ) (δ T ε : ℝ) (hK : KernelAdmissible K)
    (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime : ℝ), 0 ≤ C₁ ∧
    pairConstant K δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offCriticalError T / N_L T ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1
```

即「离线项 = 离线误差 ÷ 真实零点计数」，**并且不再断言它 ≤ 1**（那条要证，不假设）。

**(2) 两段界改为绝对常数**（配合，必需）：

```lean
axiom bgs4_offcrit_low :
  ∃ (R₁ : ℝ), 0 ≤ R₁ ∧ ∀ (T : ℝ), 1 ≤ T → WeakRealPart T zerosLChi5 →
    ∀ s : ℝ, T ≤ s → |offcritLow s| ≤ R₁ * Real.sqrt (Real.log s)
```

原写法是 `∀ T, ∃ R₁`（先 T 后 R₁），常数允许随 T 增长。这比 BGS 原文**弱**——而且正好弱到不可用：要收尾 `|E T / N_L T| ≤ 1`，分子上的常数必须对所有 T 是同一个。故这不是加强断言，是**把口径修回原文**。

**(3) 收尾定理**（新增真证，`S7_1_Main`）：

```lean
theorem offcrit_remainder_le_one (T : ℝ) (hT : 1 ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (hbig : offcritThreshold ≤ T) : |offCriticalError T / N_L T| ≤ 1
```

链条：`offcritical_small` 给绝对常数 R ⟹ `R·√log T`；阈值 `T₀ = max(e, max 1 (R/c))` 保证 `log T ≥ 1`（故 `√log T ≤ log T`）与 `R ≤ c·T`；于是 `R·√log T ≤ c·T·log T ≤ N_L T`（`N_L_lower_bound`）；再 `abs_div` + `div_le_one`（`N_L T = 0` 时 Lean `x/0 = 0`，结论平凡成立）。

阈值被做成**命名对象**而非匿名 ∃：`offcritConst := Classical.choose offcritical_small`、`NLc := Classical.choose N_L_lower_bound`、`offcritThreshold := max (exp 1) (max 1 (offcritConst / NLc))`，另有 `offcritConst_spec` / `NLc_spec` / `one_le_offcritThreshold` 三条规格引理。

**(4) 结构性前置**：`N_L_lower_bound` 从 `S7_1_Stage3` **上移**到 `S7_1_Main`（收尾定理住在 Main，而 Main 不可 import Stage3；Stage3 经 import 取得，`pair_count_bound` 仍留 Stage3）。

### 19.3 代价必须说清：`s71_main` 多了一个前提

```lean
theorem s71_main (T : ℝ) (hT : 1 ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (hbig : offcritThreshold ≤ T) (ε : ℝ) (hε0 : 0 < ε) : …
```

即「T 足够大」。这是**诚实的代价**：旧语句在 T ≥ 1 时就把 `|offcrit| ≤ 1` 当公理含着，那并不是更普遍，只是把一条未证的界藏进了 ∃。现在它是一条**对 T ≥ T₀ 成立、且被证明**的界。`QRH.lean` 根模块自检 `example` 同步加 `hbig`。

### 19.4 审计

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_N.txt`）。
- `#print axioms s71_main` → `[propext, Classical.choice, N_L_lower_bound, bgs3_pair_expansion, bgs4_offcrit_low, bgs4_offcrit_high, bgs5_khat_fourier_supp, Quot.sound]`——**L4 链（3 条中 2 条段界）第一次出现在主定理闭包里**（此前是 2 条：`bgs3` + `bgs5`）。
- `#print axioms offcrit_remainder_le_one` → 3 + `N_L_lower_bound` + `bgs4_offcrit_low` + `bgs4_offcrit_high`。
- `#print axioms pair_sum_expansion` → 3 + `bgs3_pair_expansion`（`offcrit` 已是具体项，故少了一条）。
- 列 0 计数：axiom **9**（本刀不减少条数，是**换内容**：`bgs3` 少了「≤1」、`bgs4` 两条换成绝对常数）、opaque **2**。

### 19.5 这一刀到底赚了什么

不是减少 axiom 条数，而是三件：

1. **消掉了一处「文档承诺 / 形式无连线」**：`bgs3` 注释里「离线项 ≤ 1 由引理 4 缩放」现在有对应的真证明；
2. **L4 链不再悬空**：主定理的依赖闭包里第一次出现引理 4 的两条段界，删掉它们主定理就崩——这才叫「已移植」；
3. **可复用**：`offcrit_remainder_le_one` 与 `offcritThreshold` 是独立可查的接口，后续 BSD 侧或 Stage4 若要同一形状的「余项 ÷ 计数 ≤ 1」，直接可借用，不必再假设。


## 二十、第六刀：`bgs3` 不能降为定理——它是**假命题**，不是「未证」

### 20.1 先纠正我上一轮的判断

上一轮把 `bgs3_pair_expansion` 说成「剩下的只有一句组合恒等式，形状应该可证」，并把它列为 D 类（分解假设）。**这个判断错了**，且错在两个层次：

1. **分解恒等式本身是空的**。给定任意 `A`、`off`，令 `diag := C`、`prime := A − C − off`，恒等式 `A = diag + prime + off` 立刻成立。所以「能拆成三块」不可能是内容——内容全部在 `diag ≤ C_MT + C₁ε` 与 `|prime| ≤ 1` 这两条**界**上。把这两条界与恒等式合起来看，`bgs3` 说的其实是 `pairConstant` 被 `C_MT + C₁ε + 1 + E/N_L` 压住——这正是 BGS 的 Montgomery–Vaughan + Siegel–Walfisz 机制，也就是项目本身要证的东西。**它不是组合恒等式，而是分析心脏。**
2. **更糟：原语句对一般 `K` 是假的**。见 20.2。

### 20.2 病灶：虚假的 generality（机器证据）

```lean
def KernelAdmissible (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ ∀ u : ℝ, 1 < |u| → fourierCos Khat u = 0
```

第二个合取项**只涉及 `Khat`**，完全不涉及 `K`。于是「可容许」对 `K` 的唯一约束就是 `K 0 = 1`——`K` 在其它点上是完全自由函数。这一点已机检：

```lean
lemma kernelAdmissible_of_apply_zero (K : ℝ → ℝ) (h0 : K 0 = 1) : KernelAdmissible K
```

而 `pairConstant K δ N Z = 1 + (Σ_{z₁≠z₂∈Z_T} K(δ·im(z₁−z₂))²)/N` 是 `K` 在 `N(N−1)` 个配对点上的取值平方和。取

```lean
K := fun u => if u = 0 then 1 else M
```

则 `K 0 = 1`（可容许成立），但配对和 ≥ `(配对数)·M²`（`Δ.im = 0` 的项贡献 1，其余贡献 `M²`），于是 `pairConstant` 随 `M → ∞` 而无界，而结论中的 `C_MT + C₁ε + 1 + E/N_L` 与 `M` 无关（`N_L`、`E` 都只依赖 `T`）。**故原语句不可能对一切可容许 `K` 成立**——它和已删的 `lfun_dirichlet_series` 属于同一病灶：把一个自由参数放进量词，得到一条假命题，再用 axiom 供着。

（形式化一个具体反例还差一条未形式化事实：「存在两个不同高度的 χ₅ 零点」，即 `Z_T` 里存在 `Δ.im ≠ 0` 的配对。这属 S6 零点计数，暂未入账，故本刀只做到「证明可容许性几乎不约束 K + 把语句收窄到真被使用的核」。）

### 20.3 修法：把核固定为 `Khat`

```lean
axiom bgs3_pair_expansion (δ T ε : ℝ) (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime : ℝ), 0 ≤ C₁ ∧
    pairConstant Khat δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offCriticalError T / N_L T ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1
```

依据有三条：① `s71_main` 从头到尾只用 `Khat`（`pairConstant Khat …`）；② Stage3 的 `prime_sum_bound` 早就是「签名去 K/hKs、固定 Khat」的同一做法；③ 收窄后语句只谈一个**具体对象**，不再有「任意可容许核」这种假的一般性。`pair_sum_expansion` 与 `s71_main` 的调用点同步去掉 `K` / `hK`。

### 20.4 审计

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_O.txt`）。
- `#print axioms kernelAdmissible_of_apply_zero` → `[propext, Classical.choice, bgs5_khat_fourier_supp, Quot.sound]`（即：可容许性除 `K 0 = 1` 外只用到 `Khat` 的支撑公理）。
- `#print axioms s71_main` → `[propext, Classical.choice, N_L_lower_bound, bgs3_pair_expansion, bgs4_offcrit_low, bgs4_offcrit_high, Quot.sound]`：**用户 axiom 由 5 条降至 4 条**（`bgs5_khat_fourier_supp` 退出主定理闭包）。
- `#print axioms pair_sum_expansion` → 3 + `bgs3_pair_expansion`。
- 列 0 计数：axiom **9**（条数不变，`bgs5` 仍在账上、仍被 Stage3 使用）、opaque **2**。

### 20.5 结论：D 类这条不是「可证的」，是「必须外部机制」

按现在的形式层，`bgs3` 只剩两条出路：

1. **真做 BGS 引理 3**：Montgomery–Vaughan 大筛均值 + 显式公式的 `x` 尺度 + Siegel–Walfisz 压制。这不是「几天」的量，且其中 SW 那条（`siegel_walfisz_chi5`）本身就是 B 类外部定理。
2. **等外部形式化**：与接口一同一逻辑——若有人把大筛均值或 GRH 型语句做进 Lean，这条才可能被降级。这也是本项目与 Alpöge–Claude 那条链的真实接口位置。

所以本轮的正确产出不是「又消一条 axiom」，而是**把一条假命题改成真命题的形状**，并把「D 类应可证」这个错误预期从账本上划掉。

### 20.6 顺带发现待定的第三处口径问题：ε 在形式层是空转的

`pairConstant` 不含 `ε`；`ε` 只出现在 `diag ≤ C_MT + C₁ * ε`，而 `C₁` 与 `ε` 在同一个 `∃` 里（`ε` 还是调用方自由传入）。因此对任意 `ε` 取 `C₁` 足够大即可满足该不等式，`C₁ε` 这一项的松弛在形式层**不携带信息**；`s71_main` 结论里的 `C₁ * ε` 同理（`C₁` 由 ∃ 给出）。文档 S7.4 的 N2 联动（`ε = c(logT)^{−q}`）在形式层尚未接线。这是**口径松，不是假命题**，但对外表述「C_MT + O(ε)」时应当注明该项目前不承载内容；修它需要把正则化宽度真正做成 `K` 的参数，属下一轮议题。

## 二十一、第七刀：`fourierCos_Khat` 是假命题且使整库不一致——改用三角核（axiom 9 → 7）

### 21.1 起点：一条被标为「A 类、无数学风险」的连接件

`S7_1_Core`（原 :705）曾是

```lean
axiom fourierCos_Khat (u : ℝ) : fourierCos Khat u = Khat u
```

上一轮把它列为「A 类：定义一致性，只需实算 Bochner 积分」。实算结论是**这条是假的**，而且它不是孤立的假——它与 `bgs5_khat_fourier_supp` 合起来能推出 `False`。

### 21.2 病灶一：`fourierCos Khat ≡ 0`（不是「全等于 Khat」，而是「全等于 0」）

`Khat` 的衰减只有 `1/|u|`（两项 sinc 合并后主导项）

$$
\widehat{K}(u) \approx \frac{\cos(1/\sqrt2)}{\sqrt2\,\sin(1/\sqrt2)}\cdot\frac{\sin(\pi u)}{\pi u},
\qquad \text{逼近常数}\approx 0.767\neq 0
$$

故 $\int_{\mathbb R}|\widehat K|=\infty$，`fourierCos Khat u = ∫ Khat(x)cos(2πux)dx` 在 mathlib 里按 `MeasureTheory.integral_undef` **取 0**。于是 `fourierCos Khat u = 0` 对**一切** `u` 成立，而 `Khat` 在 `u = 4/3` 处为负——两条直接冲突。

机检（根级探针 `_incons_ax.lean`，`_incons_ax.txt`）：

- `khat_eq_zero_of_one_lt_abs : 1 < |u| → Khat u = 0`（`rw [← fourierCos_Khat u]` + `bgs5`）；
- `khat_four_thirds_neg : Khat (4/3) < 0`（纯符号判断：`√2 − 8π/3 < 0` 且 `(√2 − 8π/3)/2 ∈ (−2π, −π)` ⟹ `sin > 0`；`√2 + 8π/3 > 0` 且其半 ∈ `(π, 2π)` ⟹ `sin < 0`；两项同负、分母 `√2 sin(1/√2) > 0`），`#print axioms` = 3 条基础公理；
- `qrh_axioms_inconsistent : False`，`#print axioms` = `[propext, Classical.choice, bgs5_khat_fourier_supp, fourierCos_Khat, Quot.sound]`。

也就是说：**此前账本上的 9 条 axiom 不是「9 条可能为真的假设」，而是「8 条 + 1 条使整库不一致的假命题」**。这是第七刀真正的收获——它把「账本长度」问题变成了「库一致性」问题。

### 21.3 病灶二：`bgs5_khat_fourier_supp` 是空话

```lean
axiom bgs5_khat_fourier_supp : ∀ u, 1 < |u| → fourierCos Khat u = 0
```

它字面上想说「频域窄支撑」，但因为 `fourierCos Khat ≡ 0`，它对**任何** `u` 都成立，与「支撑窄」毫无关系。一条在所有点上都成立的等式不约束任何东西——这与第六刀 `KernelAdmissible` 的病灶同类（自由/无关参数进命题，命题退化成恒真）。

### 21.4 一个字面上更弱的方案，反而更强：三角核

文档 S7.3 §3 的本意是「频率核 = 时域核 $f_0$ 的余弦变换」，真命题是 `fourierCos f0 u = Khat u`（四段初等积分可证），而不是「$\widehat K$ 的余弦变换等于 $\widehat K$」。但把 `Khat` 留在 S7.6 的链上还有第二个结构问题：`K` 在 `S7_1_Main` 里被当成两种东西——`pairConstant`（Main:60）用 `K(δ·im)`（K = 频率 profile），`primeSum`（Main:370）用 `(√n)⁻¹·fourierCos K(δ log n)`（K = 时域核再取变换）。直接「符号替换 1→2」实测在 `Main:985` 处类型不匹配，且数学上 `b_n ≈ 0.767/(πδ√n log n)` 配 `|vonMangoldt| ~ log n` 后素数项 $\sum$ 发散如 $\sqrt X$——现有有界性全靠 `prime_sum_bound` 里 `X' = min(X, e^{1/δ})` 的求和截断在硬撑，而截断的正确性依赖「Khat 支撑紧」，恰恰是 `bgs5` 假装给出、实际没给的东西。**（该失败轮次日志 `build_qrh_P.txt`，脚本已整体回滚，回滚点 `bak_20261123_142148`。）**

所以核本身要换。取

$$
\Gamma(u)=\operatorname{triKer}(u):=\max\{0,\,1-|u|\}
$$

它的全部性质由定义给出：

| 性质 | 语句 | 证明 | 公理集 |
|---|---|---|---|
| 归一 | `triKer 0 = 1` | `max_eq_right zero_le_one` | 3 基础 |
| 紧支撑 | `1 < |u| → triKer u = 0` | `max_eq_left hneg.le` | 3 基础 |
| 有界 | `|triKer u| ≤ 1` | `triKer_le_one` + `abs_of_nonneg` | 3 基础 |
| 1-Lipschitz | `|triKer a − triKer b| ≤ |a − b|` | `abs_max_sub_max_le_max` + `abs_abs_sub_abs_le_abs_sub` | 3 基础 |

对比原来撑 `Khat` 的那套件（`khat_hasDerivAt` / `khat_deriv_bound` / `S_smooth` 奇点延拓 / 均值定理，L ≈ 3.42 且要处理 `√2 ± 2πu = 0` 的除零点）：三角核把「光滑 + 紧支撑」这对矛盾**取消了**——它不光滑（折点），但它本来就只当频域 profile 用，不需要光滑。**代价从「证不出」变成「不用证」。**

### 21.5 A1/A2/A3 三步落刀

**A1（`S7_1_Core` §4c）**：新增 `triKer` 定义与上表四条 + `triKer_nonneg`，全部真证，公理集 3 基础（探针 `_tri_ax.txt`）。

**A2（`S7_1_Main`）**：新增 `prime_weight_bounds_tri`——与 Khat 版同构，`M = δ + 1`（`B = sup Γ = 1`、`L = Lip Γ = 1`），`|b_n| ≤ M·n^{−1/2}`、`|b_{n+1} − b_n| ≤ M·n^{−3/2}`，复用 `inv_sqrt_succ_sub_le` / `log_succ_sub_le_inv` / `inv_sqrt_sq_eq_inv`，sin 估计全换成 `triKer_abs_le_one` / `triKer_lipschitz`。公理集 3 基础。

**A3（口径统一 + 撤 axiom）**，共九处：

1. `primeSum` 定义改为 `∑ n ∈ Icc 1 ⌊X⌋₊, (Λ n · χ₅ n) · ((√n)⁻¹ · K(δ log n))`——**K 直接就是频域 profile**，与 `pairConstant` 同口径，不再外套 `fourierCos`。这消掉了 §21.4 的「一个 K 两种含义」。
2. `axiom bgs5_khat_fourier_supp` 原地撤除，替换为存档块；替代物是 `triKer_supp`（定义即得）。
3. `primeSum_window_eq` 前提由 `∀ u, 1 < |u| → fourierCos K u = 0` 改为 `∀ u, 1 < |u| → K u = 0`，调用点 `primeSum_window_eq triKer X δ hX hδ (fun _ h => triKer_supp h)`——**求和截断第一次有真实依据**（`X' = min(X, e^{1/δ})` 现在真的不丢项）。
4. `prime_weight_bounds_Khat`（含 docstring，109 行）整块删除。
5. `prime_sum_bound` 区间替换（`primeSum Khat`→`triKer`、`fourierCos Khat (`→`triKer (`、`prime_weight_bounds_Khat`→`_tri`、`bgs5`→`triKer_supp`）。
6. **`KernelAdmissible` 重定义**：`K 0 = 1 ∧ ∀ u, 1 < |u| → K u = 0`——第二个合取项从此**真的关于 K**。删 `Khat_admissible`、删第六刀的证据件 `kernelAdmissible_of_apply_zero`（其论点随新表述消失），新增 `theorem triKer_admissible`。
7. `bgs3_pair_expansion` / `pair_sum_expansion` 核改 `triKer`；`s71_main` 同步；`QRH.lean` 根自检同步。
8. `axiom fourierCos_Khat` 原地撤除，写存档块（含假命题两路理由、真命题 `fourierCos f0 u = Khat u` 的四段真证路线、消费点已改口径）。
9. `S7_1_Main:585` 措辞「与前件 `prime_weight_bounds_Khat` 同构」改为「与已撤的 Khat 版同构」。

### 21.6 审计（本轮全部机检）

- `lake build QRH`：**3836 jobs / 0 error**（`build_qrh_R.txt`、`build_qrh_R2.txt`）。job 数与手术前一致，说明换核没有引入新文件、也没有丢件。
- `_a3_ax.lean` / `_a3_ax.txt`：

| 常数 | `#print axioms` |
|---|---|
| `triKer_admissible` | 3 基础 |
| `primeSum_window_eq` | 3 基础 |
| `prime_sum_bound` | 3 基础 + `siegel_walfisz_chi5` |
| `pair_sum_expansion` | 3 基础 + `bgs3_pair_expansion` |
| `bgs3_pair_expansion` | （本身为 axiom） |
| `s71_main` | 3 基础 + `N_L_lower_bound` + `bgs3` + `bgs4_offcrit_low` + `bgs4_offcrit_high` |

- 列 0 计数：**axiom 7**（`N_L_lower_bound` Main:121、`landau_explicit_L` :210、`siegel_walfisz_chi5` :342、`bgs3_pair_expansion` :1177、`bgs4_offcrit_low` :1227、`bgs4_offcrit_high` :1234、`pair_count_bound` Stage3:729）、**opaque 2**（`offCriticalError` :202、`offcritLow` :1202）。**9 → 7**，且撤掉的两条一条是假命题、一条是空话。
- `s71_main` 闭包仍是 4 条用户 axiom（第六刀后的 4 条，未增未减）：换核没有让主定理多背任何假设。
- 库里 `Khat` 仍然存在，但已退回文档层解析式：`S7_1_Stage3` 的 `Khat_closed_form` / `Khat_a_even` / `khat_second_order_bound` 是独立历史件，不在 `s71_main` 的闭包内（已由上面的 `#print axioms s71_main` 确认）。

### 21.7 新账（7 + 2 + 1）

| 类 | 条目 | 性质 | 处置方向 |
|---|---|---|---|
| 数论外部定理 | `siegel_walfisz_chi5` | 真定理（Siegel–Walfisz，非平凡） | 等外部形式化 |
| 数论外部定理 | `landau_explicit_L` | 真定理（Landau 显式公式） | 等外部形式化 |
| 分析心脏 | `bgs3_pair_expansion` | 真命题，但 = MV 大筛 + SW | 长线 / 等外部 |
| 计数结构 | `N_L_lower_bound`、`pair_count_bound` | 真命题（RvM 型计数） | 可形式化，需 mathlib 聚合 |
| 段界 | `bgs4_offcrit_low`、`bgs4_offcrit_high` | 真命题（零点求和分段） | 可形式化 |
| 数据型 | `offCriticalError`、`offcritLow` | opaque（无定义体） | 需 `w(ρ−ρ')` 权重机制 |
| 未形式化 | N3 主不等式 (M) | — | 与 Alpöge–Claude 同位置 |

### 21.8 常数重算：口径 A 撤数（2026-11-23 当日撤回「常数 0.8435059964」）

- **撤回对象**：`2 − C_A = 0.8435059964`、以及「与 7/8 差 0.0314940」「常数由 0.6725 提到 0.8435」这一整串表述。**C_A = 1.1564940036 保留**（它是下面 F1 的合法值），撤的是把它当常数基底的那一步减法。
- **口径裁定（仍有效）**：库内的三角核是**配对核**（`pairConstant triKer`，K = Γ 直接入 ΣK(δΔ)²），记为口径 A，采用。口径 B（Γ 作密度、配对核取 sinc²）保留旧文，日后单独改；但 B 的那个 0.8833 与 0.8435 属同一类错（把 C 直接减成常数而未核归一与 λ_eff），启用前须先过硬判据。
- **两个泛函，被拼成了一个数**：
  - **F1（ρ₂ 积分泛函，与代码同词法）**：C = 1 + ∫ K(u)² ρ₂(u) du，ρ₂ = 1 − (sin πu/πu)²。Γ ⟹ ∫Γ² = 2/3、J₁ = ∫₋₁¹ (1−|u|)²(sin πu/πu)² du = 2[−½log(4π²) − γ + Ci(2π) + ½ + πSi(2π)]/π² = 0.5101726630（20 位，sympy 闭式与 mpmath 分裂积分独立吻合）⟹ **C_A = 1.1564940036**。这个数没错。
  - **F2（密度泛函，「常数 = 2 − C」这个减法真正的归属）**：C = 1 + ∫f² − ⟨f*f,Γ⟩ = 2 − ∫K·Γ。Γ（常密度 f≡1）⟹ ∫Γ·Γ = 2/3 ⟹ **C = 4/3**，常数 **2/3 = 0.66667**（与库里 `C_MT_lt_four_thirds` 自洽）。
  - 故 `1.1564940` 属 F1、`2 − C` 属 F2，拼出的 0.8435060 不对应任何泛函。**三角核并没有抬高常数：按 F2 词法它是 0.66667 < 0.6725，是下降。**
- **F1 不能用来判 7/8（钉子）**：ρ₂ ≥ 0 且 ρ₂(0) = 0，K 越往 0 挤积分越小。实测 a=1/2：Γ 1.15654、cos-window 1.15143、cos(πx) 1.08531、exp(−16x²) 1.03980、exp(−256x²) 1.00071；支撑缩到 0.0625 时一律 ≈1.00003。**F1 的下确界 = 1**，所以「C ≤ 1.125 即过 7/8」在 F1 下是空赢。
- **F2 下同类的核族排序（μ = 2 − C）**：变分最优 0.6755169434（闭式）> cos-window 0.67454（闭式 0.6725007037）> Γ 0.66667 > exp(−4x²) 0.66216 > (1/4−x²) 0.61905 > cos(πx) 0.60793 > (1/4−x²)² 0.54849 > exp(−16x²) 0.49907。
- **变分最优的答案（已闭式，不再依赖数值）**：F2 最大化 ⟺ 算子 T f(x) = ∫_{[−a,a]} Γ(x−y) f(y) dy 的最大特征值。两次分部积分给 (Tf)″ = −2f，故 f″ + k²f = 0、k² = 2/μ；g := Tf − μf 线性，两支边界条件：偶支 (1−a)k sin(ka) = cos(ka)、奇支 cos(ka) = 0。a = 1/2 记 v = ka，得**特征方程 `v tan v = 1`**，
  **v₁ = 0.8603335890193797625，μ₁ = 1/(2v₁²) = 0.6755169434391893120，C_min = 2 − μ₁ = 1.3244830565608107**；
  最优密度 **f\\*(x) = cos(2v₁x) = cos(1.7206671780·x)**（比 cos-window 的 k = √2 高 21.7%）。全谱闭式：偶支 1/(2v_n²)、奇支 2/((2n+1)²π²)（前五：0.6755169434、0.2026423673、0.0426080858、0.0225158186、0.0120659842）。三重校核：点值 max|Tf\\*−μ₁f\\*| = 2.7e−10；与分片常数 Galerkin 外推 0.67551694 差 3.4e−9；a = 1/4 公式给 0.4175227354 与 Galerkin 0.41752274 一致。旁证：常密度的 Rayleigh 商 = 2/3，与 Γ 行吻合。**适用域：仅 2a ≤ 1（λ_eff ≤ 1）；λ_eff > 1 时核的紧支撑截掉 |x−y|>1 的耦合，ODE 须重推，不可用此公式外推。**
- **判定（取代旧判定，但 2026-11-23 晚已由 §21.9 降级）**：supp f ⊂ [−1/2,1/2] 内，形状优化全部收益 0.6725 → 0.6755169434（闭式，+0.0030162），距 7/8 的 0.875 差 **0.1994830566**。**在 F2 泛函内**，7/8 不能靠核形状解决。⚠ 这句话对 A **无效**：§21.9 已判定 F2 不是 A 的泛函，故 0.1995 这个差距本身是错尺度的产物（真泛函下差 0.034）。
- **保留条款（2026-11-23 由 §21.9 改写，旧判错误）**：旧文说「F2 的连续形式丢了离散求和的 1/δ 与 N 归一」——**此句错**。S6 原文与其脚本（`xlii_s6_lambda.py` 第 105 行）写明 δ = logT/2π，它本身就是平均间距的倒数，u = δΔ 已是归一间距，A 即「1 + 每对 1/N」，**不存在 1/δ**。真正的错位不在归一而在核形状（K = f̂ 而非 f\\*f），见 §21.9。F2 数不能用于判定 7/8 的结论仍成立，理由已换。
- **新判据（进审计台）：一个常数只能有一个泛函。** 凡出现 C 与常数，必须同时写明 ①泛函、②归一（K(0)=1 与 δ 的含义）、③λ_eff 与支撑、**④核的定义（K = f̂ 还是 K = f\\*f？支撑有限还是无限？）**。§21.8 的口径漂移是前三项缺两项；§21.9 的口径错位是前三项齐全却缺第四项。
- **无条件分支不变**：λ ≤ 1/2 的 C_MT = 1.3274993 ⟹ 0.6725。Γ 的 supp = [−1,1] ⟹ λ_eff = 1，属超支撑，需拟随机 (H2′_λ)。
- **形式状态**：以上全为解析闭式 + 数值复核，**未 Lean 机检**；axiom 计数不变（7 axiom / 2 opaque / 1 明账）。A4（`fourierCos triKer`）在 C_A 里不出现，其消费者是口径 B（待启用）。
- **证据**：`_cmt_families2.py`/`.txt`（两泛函表与锚点自检；F1(Γ) 数值 1.1565398 与 1.1564940 差 4.6e−5 为网格误差）、`_cmt_lambda_eig.py`/`.txt`（特征值与 2/3 校核）、`_cmt_exact.py`、`_cmt_sym.py`、`_cmt_probe3.py`（J₁ 的 20 位闭式）。
- 三角核余弦变换闭式本身已机检（`fourierCos_triKer`，见下条原文）：

  `fourierCos triKer z = ∫₋₁¹ (1 − |x|) cos(2πzx) dx = 2·(1 − cos 2πz)/(2πz)² = (sin πz / πz)²`，

（`z = 0` 取 1，与 `∫Γ = 1` 自洽）。这条此前属**注释层断言（待证）**，已于 2026-11-23 **机检闭环**：`QRH/S7_1_Core.lean` §4c′ 的 `fourierCos_triKer` 为真定理，配套 10 件辅助引理，11 件 `#print axioms` 全部 = 3 基础公理（`_a4_ax.txt`），且**不进 `s71_main` 闭包**。技术路线与旧预测一致；旧预测中的风险「`IntervalIntegral` olean 缺失」已证为误判（聚合模块缺、子模块齐备，另加 `Mathlib.MeasureTheory.Integral.Bochner.Set`）。
- `Khat` 此刻在库里只剩「历史件载体」身份；若日后要把「频率核 = $f_0$ 的余弦变换」重新入账，语句应取 `fourierCos f0 u = Khat u`（真命题），而不是旧的那条。
- `ε` / `C₁ε` 空转（§20.6）未动。

### 21.9 核正：A 的真泛函是 K = f̂，F1/F2 整族作废（2026-11-23 晚）

- **起因**：常数机制连撤两轮（§21.8）之后，仍未回答「归一到底该怎么定」。本轮不再在连续模型里推，而是回到 A 的原始定义——包括此前从未纳入分析的 **S6 原始脚本** `…\2026-10-16\new-chat\qrh_work\xlii_s6_lambda.py`。
- **原始口径（按脚本行号）**：第 22–29 行 `K(u) = ∫ f(x) cos(2πux) dx`（`f₀ = cos(√2x)/(√2 sin(1/√2))`，支撑 [−1/2,1/2]，∫f₀ = 1 ⟹ K(0) = 1）；第 31–39 行尺度族 `f_λ(x) = f₀(x/λ)/λ` + 显式 K(0) 归一；第 54–76 行配对直方图（`binw = 0.02`、`half = 40`、**双向**）；第 85 行 `A = 1 + Σ(hist·K²)/n`；第 105 行 `δ = log T/(2π)`。
- **因此**：A 的核是**密度的余弦变换 f̂**（支撑无限、按 1/u 衰减），不是自相关 f\\*f（支撑 [−1,1]、在 ±1 归零）。**「λ_eff = 1 处 K 端点归零 ⟹ 配对和退化为 0」这个现象，是 §21.8 那套口径自己造出来的，不在 A 里。**
- **归一**：δ = logT/2π 是平均间距的倒数，u = δΔ 已归一，**没有 1/δ**。§21.8 的保留条款据此撤回。
- **真泛函（连续模型）**：A(f) = 1 + ∫₀^∞ ρ₂(u)|f̂(u)|²du，ρ₂ = 1 − sinc²(πu)，f ≥ 0、∫f = 1、supp f ⊂ (−λ,λ)（λ 即 a，半宽）。
- **校准**：f₀ 在 λ = 1/2 给 A = **1.162882**，S6 实测 **1.1868**，差 **2.0%** ⟹ 模型可用（**§21.10 撤回：这是「单边模型 vs 有序实测」的假吻合，真差额 12%**）。λ-尺度族（支撑 λ/2）模型系统低 13–24%，故模型只在校准点附近可信，绝对数按区间用。
- **边界读数（a = 0.5，同一泛函）**：梳状最优 1.1588（2−A = 0.8412）｜flat 1.1654（0.8346；解析锚点 ∫₀^∞ρ₂sinc² = 1/6 精确）｜f₀ 实测 1.1868（0.8132）｜**C_MT 1.3275（0.6725）= 最坏情况上界，不是实际值**。这才是「GUE 排斥压低、方向有利」这句话的准确含义。【**§21.11 更正**：恒等式 C_η = 1 + ∫ρ₂K²（ρ₂ = 1 − sinc² 是 Fourier 核、不是猜想）⟹ C_MT 是 **f₀ 在恒等式下的取值**，即类内**极小**，不是「上界」；且「典型值」与「定理值」在该类内不是两回事——GUE 参考曲线 H→∞ 收敛到 1.327317 ≈ C_MT（0.02%）。本节「边界读数」四行的量级关系仍对，但「最坏情况」这个词应删。】
- **变分（可容许类 f ≥ 0、∫f = 1、supp ⊂ [−a,a]）**：
  - 极小元为梳状密度（峰/均值随 n 增），先排除网格假象：Q_min 于 n = 50/100/200/400 为 0.16280/0.16100/0.15958/0.15881（a = 0.5）、0.11033/0.10991/0.10863/0.10808（a = 0.6），**收敛到有限值**；
  - **7/8 临界**：梳状端 a\\* = 0.562、flat 端 a\\* = 0.5752（40 次二分）⟹ **λ_eff\\* ≈ 1.124–1.150**；
  - **光滑度只值 0.013（2.3%）**：门槛不是病态核撑出来的，flat 核本身够。
- **两个「更平滑」的核反而更差**：抛物 (1−(x/a)²) 在 a = 0.575 给 0.1696、半周期余弦 cos(πx/2a) 给 0.1801（都远高于 0.125）。原因：它们抬高 ‖f‖₂²（3/(5a)、π²/(8a)，flat 为 1/(2a)）。**关键变量是支撑宽度，不是光滑性。**
- **两个刻度（不可混写）**：典型（GUE）刻度 λ_eff ≈ 1.13–1.15 即够 7/8；定理刻度要「对所有可容许零点配置 A ≤ 1.125」，须最坏情况上界（C_MT 即 λ = 1/2 处的那个界）。粗测最坏形（ρ₂ ≡ 1）下 A = 1 + ‖f‖₂²/2，flat 在 a = 0.5 已是 1.5 ⟹ 定理门槛必大于 1.13，且无解析件定不下来。
- **账本处置**：F1（1 + ∫|f\\*f|²ρ₂）与 F2（2 − ∫(f\\*f)·Γ）标为「泛函不符，作废」；C_A = 1.1564940、4/3、μ₁ = 0.6755169434、λ_eff\\* = 2.0363 退为该族内部数值，不作 7/8 判据。**axiom 7 / opaque 2 / 明账 1 不变**（全为解析与数值，未进 Lean）。
- **未决（① 已由 §21.10 判为「不能，也不需要」；λ_eff\\* ≈ 1.124–1.150 随之撤回）**：~~① 最坏情况上界能否写成一般 λ 的形式（把 1.13 变成定理的唯一路径）~~；② 连续意义下 Q 的下确界是否有限（n-收敛支持「有限」但未证明）；③ λ-尺度族上 13–24% 偏差的来源（§21.10 已定口径：S6 为有序对 = C_η、连续模型为单边 = (C_η+1)/2；实测 1.1868 与定理 1.3275 的 12% 差额见 §21.11 已拆完：δ 口径 58%、全局 δ/bin 26%、截断 1%、有限 T 14%；该族偏差本身仍待用 δ_loc 重算后再判，旧数含 S6 全局 δ）。
- **证据**：`_s6_func.py`、`_s6_var.py`、`_s6_qp2.py`、`_s6_ncheck.py`、`_s6_unif.py`、`_s6_bis.py`、`_s6_comb.py`、`_s6_smooth.py`（均在 `C:\proj2` 根）；全部纯数值，**未 Lean 机检**，不进 axiom 计数。旧族脚本保留为 F2 内部记录。

### 21.10 ① 的答案：它不是「界」，是无条件恒等式；类内极小 1.3275 已被 CCLM 封顶（2026-11-23 深夜，第三刀）

- **问题纠偏（这是本轮唯一的方法论收获）**：§21.9 的未决 ①「最坏情况上界能否写成一般 λ 的形式」隐含「存在一个随 λ 变的界」。这个隐含是错的：真硬件是一条**等式**，不是一个界。凡「最坏情况」四字，先问它在给定类内是等式还是不等式——**若为等式，「最坏」无内容，而它的适用域本身变成硬约束**。这条记为审计台判据第 ⑤ 项。
- **原文硬件（此前缺的正是这块）**：Lamzouri `arXiv:2609.02882v1`（2026-09-02，14 页），链路 Prop 2.1 ⟹ Lemma 3.1 ⟹ Lemma 3.2 ⟹ Theorem 1.1。
  - **Prop 2.1（λ 任意，纯 Hilbert 空间）**：λ > 0、η ∈ L²(ℝ) 实偶、supp η ⊂ (−λ,λ)、η²̂(0) = 1，Z 为复共轭不变的有限重集，则
    #(Z∩ℝ 且单重) ≥ 2#Z − Σ_{z,s∈Z} K(z−s)²，以及 #(互异元) ≥ (3/2)#Z − ½Σ_{z,s}K(z−s)²，K := η²̂。
    证明是 L²((−λ,λ)) 上三层嵌套 Gram–Schmidt（U ⊂ V ⊂ W）+ Bessel + a²+1 ≥ 2a、a²+4 ≥ 4a，α_j 求和恰好塌缩成 #Z。**它不是非负核论证**——这是它能脱离 RH 的原因。
  - **Lemma 3.1（= BGS Lemma 5，无条件）**：f ∈ L¹ 实偶、supp f ⊂ [−1,1]、0 处 Lipschitz，则
    Σ_{0<γ,γ'≤T} f̂(i(ρ−ρ')logT/2π)·w(ρ−ρ') = (T/2π)logT·( f(0) + 2∫₀¹ α f(α)dα + O(1/√logT) )，w(z) = 4/(4−z²)。
  - **Lemma 3.2（去权，得常数）**：取 r_{δ,T} = Q_δ − Q_δ''/(4(logT)²)，因 Q_δ''^(z) = −4π²z²K_δ(z)²，故 r̂_{δ,T}(z) = (1 + π²z²/(logT)²)K_δ²，正好抵掉 w；于是
    **C_η = Q(0) + 2∫₀¹ α Q(α) dα，Q = f\\*f，f = η² ≥ 0、∫f = 1、supp f ⊂ (−λ,λ)**。
    要点：**C 只由 f 的形状决定，与零点的真实分布无关——它是恒等式，不是不等式。**
  - **Remark 3.3（换方法不换常数）**：Claude 侧矩阵路线（Alpöge–Furman `arXiv:2608.13637` Thm 5.7）与 Lamzouri 的 Hilbert 空间不等式「both may be viewed as variants of a second-moment argument, and the optimization leads in both cases to the same Montgomery–Taylor extremal problem」⟹ 换泛函压常数这条路不通。
  - **Remark 3.4（最优性）**：C_η ≥ C_MT，由 Carneiro–Chandee–Littmann–Milinovich（J. Reine Angew. Math. 725 (2017) 143–182, Cor. 14）给出；极值函数 f₀ = cos(√2x)/(√2 sin(1/√2)) on [−1/2,1/2] 即 Montgomery–Taylor（1974）极值函数。
  - **Theorem 1.1**：C₀ = 3/2 − (1/√2)cot(1/√2) = 0.6725007…、C₁ = (C₀+1)/2 = 0.83625…；摘要另给「simple 或在线 ≥ 88.76%」「两者平均 ≥ 83.62%」。
  - **附录 A**：AxiomProver 对 Prop 2.1 + Theorem 1.1 形式化，仓库 `https://github.com/AxiomMath/ZetaZeros`（Comparator 机检），前提是 BGS Lemma 5 + Riemann–von Mangoldt。**这是与 QRH 直接同源的可对照件。**
- **机检（本轮唯一机器证据，`_ceta_check.py`）**：自相关走 |FFT|²，dx = 2⁻¹⁸，承载窗 [−4,4]，滞后 [−1,1] 无回绕。

  | 核 | Q(0) | J = 2∫₀¹αQ | C_η | 判定 |
  |---|---|---|---|---|
  | f ≡ 1（经典 Montgomery） | 1.0000038 | 0.3333371 | **1.3333410** | 4/3，差 +7.6e−6 ✓ |
  | f₀（Montgomery–Taylor） | 1.0061298 | 0.3213753 | **1.3275051** | C_MT = 1.3274992963，差 +5.8e−6 ✓ |
  | cos(2v₁x) 按 ∫f = 1 归一 | 1.0141047 | 0.3149594 | **1.3290640** | ≥ C_MT ✓（CCLM Cor.14 成立） |

  意义：第二行把「C_MT 就是 f₀ 在这个泛函下的值」钉死（此前只把它当「已知常数」，从未对表）；第一行说明经典 2/3 正是 f ≡ 1 的取值（4/3 ⟹ 2 − 4/3）；第三行判死 μ₁ 那条路。
- **撤回一：μ₁ = 0.6755169434（§21.8 闭式）**。该特征方程解的是「max ⟨f\\*f,Γ⟩ / ‖f‖₂²，supp ⊂ [−1/2,1/2]」，约束是 ‖f‖₂ = 1；C_η 的合法约束是 ∫f = 1、f ≥ 0。换归一化就换极值点：cos(2v₁x) 归一后 C_η = 1.3290640 > 1.3274993，极小仍由 f₀ 取得。**不是我们赢了 0.003，是把约束写错了。** 原式 μ₁ = 1/(2v₁²) 算术无误，但已无归属。
- **撤回二：λ_eff\\* ≈ 1.124–1.150（§21.9）**。它由 A = 1 + ∫₀^∞ρ₂|f̂|²du（ρ₂ 是猜想）+ 单边模型得出；而定理口径的 7/8 门槛是 C ≤ 1.125（**A_s6 ≡ C_η，无因子 2**），1.3275 与它差 15% ⟹ 该「临界支撑」落在受证类极小值之下，是**不可达区**，不是精度不足。同撤「λ 增大就能救」：λ 增大 ⟹ K 变窄 ⟹ 计入的对数变少 ⟹ C 反向趋 1（f 摊到 [−λ,λ] 给 C ≈ 1/(2λ) + 1 → 1，界退化为空话）；二次矩强度在 λ = 1/2 取极大，与 CCLM 最优性同向（此段为同机制外推，**属推断**，λ > 1/2 无定理）。
- **归一口径闭合（§21.8 的悬案，并更正上稿的错误）**：
  - **S6 侧是有序对，无换算因子**：`pair_hist`（脚本 63–74 行）对每个零点取 `z−half … z+half` 两侧邻点、只滤掉 `ds ≤ 1e−12` 的自身项 ⟹ 每个无序对记两次 ⟹ `A_s6 = 1 + Σ_{有序 z≠s}K²/N = Σ_{全部配对}/N ≡ C_η`。**上稿「C = 2A − 1 适用于 S6」作废。**
  - **只有连续模型是单边**：A_model = 1 + ∫₀^∞ρ₂|f̂|²du ⟹ A_model = (C_η + 1)/2 ⟹ **C_η = 2A_model − 1**。锚点：flat 模型 1.16667 ⟹ 4/3 精确 ✓；f₀ 模型 1.162882 ⟹ 1.32576（差 0.13%）✓。
  - **实测与定理差 12%，未闭合**：S6 实测 1.1868 按有序对读应 = C_η = 1.3275，缺口 0.141。候选：零点表不全（本地 npz 缺失）、half = 40 对 1/u 尾的截断、ζ 与 L 混族的 N 归一。**「模型与实测差 2%」撤回。** 【**§21.11 已闭合**：表完整（N(8×10⁵) = 1,369,279 ✓）、截断排除（H 40→400 差 0.0016）、δ 口径为主因（+0.0823 = 58%）、全局 δ/bin 复合 0.0371（26%）、残差 0.0195（1.5%）为有限 T。修正后 A_sat = 1.3078。】
- **7/8 判决（定理级，不是进度问题）**：受证类（2λ ≤ 1，即 supp Q ⊂ [−1,1]、Montgomery α ≤ 1 段）内 C_η ≥ 1.3274992963 且由 f₀ 取到 ⟹ 该类的比值封顶 2 − C_MT = 0.6725007。7/8 需 C ≤ 1.125（A_s6 ≡ C_η），**缺口 15% ⟹ 在这个二次矩方法类里被最优性定理排除**。三条出口：(i) α > 1（PPC / 强 Montgomery，即 S6 的 (H2′_λ) 超支撑）；(ii) 换非二次矩类泛函（Remark 3.3 已判换装不换核）；(iii) 类外信息（素数侧 / BGS 余项 —— 正是 QRH 的入口）。
- **对 Lean 侧的处置（本轮零代码，只重定位，账本 7 axiom / 2 opaque / 明账 1 不变）**：
  - `bgs3_pair_expansion` 的身位改变：不再是「配对和能拆三块」这条对一般核为假的组合恒等式，而可改写为 **C_η 恒等式**的具体语句（有 Lamzouri 定理支撑，带 O(1/√logT) 余项）。这一步是「变真」，不是「变短」。
  - 真正可形式化的硬核是 **Prop 2.1 本体**：纯 L²((−λ,λ)) 内的嵌套 Gram–Schmidt + Bessel + 初等不等式，mathlib 有 L² 内积、Bessel、有限维 Gram–Schmidt、Finset 求和等件。这是把「配对不等式」从 axiom 变真定理的唯一入口，且**不依赖任何未证猜想**。
  - 边界提醒：Theorem 1.1 的数值件（C₀ = 0.6725、88.76%）依赖 BGS Lemma 5 + RvM，仍属「引用外部定理」，不进 QRH 的 axiom 清单——除非照 App. A 的做法单独建一条带文献署名的接口 axiom（这需要拍板，不在本轮）。
- **审计台判据（累计五项）**：①泛函 ②归一 ③λ_eff 与支撑 ④核的定义（K = f̂ 还是 f\\*f）⑤**恒等式 vs 界**（等式类内「最坏」无内容，适用域即硬墙）。
- **证据与可复查指针**：`C:\proj2\_ceta_check.py`（纯数值，未 Lean 机检，输出见上表）；`https://arxiv.org/html/2609.02882v1`（一次读完 11206 tokens，含 Prop 2.1 完整证明、Lemma 3.1/3.2、Remark 3.3/3.4、Thm 1.1、App. A）；BGS `https://arxiv.org/abs/2306.04799`；对照件 `https://github.com/AxiomMath/ZetaZeros`。

### 21.11 实测口径与定理口径的对接：12% 拆完，δ 是主因；C_η 的初等 Fourier 表示（2026-11-23 深夜，第四刀）

**这一节的性质**：§21.10 把「7/8 是否被定理排除」判死，但留下一个界面问题——**我们的实测（S6 的 A = 1.1868）与定理（C_η = 1.3275）差 12%，差在哪？** 界面没接上，就不敢说「实测支持定理」。本轮把这条缝拆完，并在过程中拿到一个可以写进形式化接口的表示式。

- **先修数据（推翻 §21.10 的一条候选解释）**：§21.10 写「本地 npz 缺失，数据在另一台机」——**误判**。表在本机 `…\tmp_word_scatter`，且完整：`zeta_T800000.npz` 1,369,279 条，对 RvM 预测 1.3694×10⁶ 一致；另有 `zeros_T6e5.npz`（zeta 999,492 / L 1,150,050）、`L_D5_T800000.npz`（1,570,290）、分级 T40000/100000/200000/400000。「表不全」当场排除。
- **half 扫描（`_s6_halfscan.py`，ζ 于 8×10⁵ 带 [7.2e5, 7.95e5] 内 8,215 个中心零点，partner 全表，δ_loc = 1.869787）**：A 从 H = 2 的 1.274190 单调升到 H = 40 的 1.306230，再到 H = 400 的 1.307788；同 half 的 GUE 参考（1 + 2∫₀^H(1−sinc²)K²du）为 1.293528 → 1.325756 → 1.327317。**H = 40 → 400 只差 0.0016（超出部分的 0.5%）⟹ 截断不是 12% 的原因，H ≈ 40 已饱和。** 另一条：实测与 GUE 参考**全程平行**（间隔恒 0.0195），而参考曲线在 H → ∞ 收敛到 **1.327317 ≈ C_MT（0.02%）** ⟹ 定理常数与「典型值」在该类内是同一个数，§21.9 的「C_MT 是最坏情况上界，不是实际值」这句应改写（见下条恒等式）。
- **δ 对表（同一批 i，H = 40）**：δ_S6 = log(8e5)/2π = 2.162295 ⟹ A = 1.223878；δ_loc = log(8e5/2π)/2π = 1.869787 ⟹ A = 1.306230。**S6 的 δ 比真实平均间距密度大 15.6%（= logT/log(T/2π)），把超出部分压掉 27%。这是 12% 的主因。**
- **0.141 的四项拆分**：全局 δ/bin 的复合 +0.0371（26%）｜δ 口径 +0.0823（58%）｜截断 +0.0016（1%）｜残差 +0.0195（14%），合计 0.1407 ≈ 0.141。**修正后 A_sat = 1.3078 ± 0.002，与 C_MT 差 1.5%。**
- **T 依赖（`_s6_Tscan.py`，H = 200，每档 4–5 千个 i）**：亏 = C_MT − A 于 T = 4e4/1e5/2e5/4e5/6e5/8e5 为 0.0282/0.0223/0.0172/0.0214/0.0238/0.0236；噪声探针（i 错开一位）差 0.0021 ⟹ 无单调趋势。**结论：残差 0.0195 为有限 T 效应（量级合 O(1/√logT)，系数 ≈ 0.055），log T 只跨 10.6–13.6，本机表已到分辨极限，不再追。**
- **本轮真正的收获：C_η 的初等 Fourier 表示**（对形式化接口有用，因为它是纯 Fourier 恒等式，不碰零点）

  **C_η = 1 + ∫_{-∞}^{∞} ρ₂(u) K(u)² du，ρ₂(u) = 1 − sinc²(πu)，K = f̂**

  推导四步：① sinc²(πu) = Ĉ[Γ]（Γ(x) = max(0,1−|x|)）——**这正是已机检的 A4 `fourierCos triKer`**；② 余弦变换 Parseval ⟹ ∫₀^∞sinc²K² = ½∫Γ·Q = ∫₀¹(1−α)Q(α)dα；③ ∫₀^∞Q = ½Q̂(0) = ½K(0)² = ½；④ 2∫₀^∞ρ₂K² = Q(0) − 2∫₀¹(1−α)Q = Q(0) + 2∫₀¹αQ − 1。锚点：flat 给 4/3 精确、f₀ 给 1.327317（H = 400）→ C_MT。
- **回收「ρ₂ 是猜想」这句（§21.9 与 §21.10 各一处）**：ρ₂ 在这个表示里**不是关于零点分布的猜想，而是恒等式的 Fourier 核**；上式只用 ∫f = 1，与零点无关。真正在 λ > ½ 失效的是 **C_η 本身**（supp Q ⊄ [−1,1]，Lemma 3.1 的前提破了），`1 + ∫ρ₂K²` 仍是合法的数但不再是配对和的值。**故 §21.10「撤回二」的理由应改写成「λ > ½ 无定理」，而不是「ρ₂ 靠猜想」；被撤的仍只有单边计数与 λ > ½ 的外推两项。**
- **对 Lean 接口的两点处置（本轮零代码，账本 7 axiom / 2 opaque / 明账 1 不变）**：
  - **A4 身位回升**：`fourierCos triKer` 不再只是「口径 B 的预备件」，而是上述恒等式的第 1 步（机检叶子）。若要形式化整条恒等式，缺的是 cos-Parseval 与 Q̂ = K² 的卷积定理，mathlib 未必有 ⟹ 独立一件活，**未机检**。
  - **两处 docstring 需加口径警示（涉及表述改动，未拍板不动）**：`S7_1_Main.lean:38` 与 `:57` 写「δ = logT/(2π)」，那是 S6 脚本的历史口径；物理值是 `log(T/2π)/(2π)`，在 T = 8×10⁵ 处差 15.6%。`pairConstant`（`:60`）的 δ 是**参数**，代码语义不受影响，但**只要把 A 的值与真实零点对表就必须用 δ_loc**。建议各加一句「（δ 的物理值 = log(T/2π)/(2π)；本语句不固定 δ，见增量㉜）」。
- **界面结论（可以对外说的那句话）**：实测与定理的差额 **98.5% 可由口径错误解释**（δ 15.6% + 全局 δ/bin），剩下 1.5% 是有限 T 项且已到分辨极限。**故 §21.10 的判决（7/8 在受证类内被排除）在数值上获得同向支持：真实数据的配对常数落在 1.304–1.308，离 1.125 的门槛差一个数量级方向的距离，不是 1–2% 的口径误差能救的。**
- **证据**：`_z_inspect.py`（表体检 / RvM 对照）、`_s6_halfscan.py`（half 扫描 + δ 两口径 + 参考曲线，含 `rfft` 相位 `(−1)^k` 修正）、`_s6_Tscan.py`（T 表 + 噪声探针）；前件 `_ceta_check.py`。全部纯数值 + 解析推导，**未 Lean 机检**。



### 21.12 把 (i) 降成定义：`diagTerm` / `DiagRate`，并把「Abel 求和」这条路正式判死（2026-11-24，第十一刀）

**语句层（已落刀、已编译、已探针）**

- 旧 `BGSDecompositionCore : ∃ C₁ ≥ 0, ∀ᶠ T, ∀ hweak, ∃ diag, pairConstant = diag + primeSum/N_L + offCriticalError/N_L ∧ diag ≤ C_MT + C₁·(log T)⁻¹` **删除**。
- 新 `noncomputable def diagTerm (T : ℝ) : ℝ := pairConstant triKer (physDelta T) (N_L T) (zerosLChi5UpTo T) − primeSum triKer (physWindow T) (physDelta T)/N_L T − offCriticalError T/N_L T`。
- 新 `def DiagRate : Prop := ∃ C₁ ≥ 0, ∀ᶠ T, diagTerm T ≤ C_MT + C₁·(log T)⁻¹`。
- 新 `theorem DiagRate_to_uniform : DiagRate → BGSLocalUniform`（真证：`unfold diagTerm` + `ring` 消化恒等式；素数槽用 `prime_normalized_le`，常数 `2π·e^{2π}/NLc` 显式不需要 axiom 之外的输入）。
- `s71_main_tail_core` → `s71_main_tail_diag`（唯一前件 `DiagRate`）。

**为什么这一步在审计意义上是净收益（可复用手法）**

`∃ diag … ∧ 恒等式 ∧ 率` 这种写法有两个病：恒等式对任意实数成立（`diag` 自由），所以它不是「条件」；但它把真条件（率）包在同一个 `∃` 里，使 **G4 判据失效**——「去掉这条前件，结论是否还成立」问不出答案，因为去掉的是整包。把 `diag` 换成**具体项** `diagTerm` 之后：恒等式变定义（自动消失），前件塌缩成**单句不等式**，G4 才可判。**这一手法对账上所有「`∃` 打包了几何量 + 一条不等式」的条目通用**，本工程此前只在此处用过；`bgs4_offcrit_low` / `bgs4_offcrit_high`（两条 opaque）应照此复查一遍。

**探针（`_probe_g1b.lean`，原文）**

```
QRH.diagTerm              : [propext, Classical.choice, Quot.sound]
QRH.DiagRate_to_uniform   : [propext, Classical.choice, N_L_lower_bound, Quot.sound]
QRH.s71_main_tail_diag    : [propext, Classical.choice, N_L_lower_bound,
                             bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]
```

`s71_main_tail_diag` 的闭包**不含** `bgs3_pair_expansion`：A 线尾部形状的未证内容只剩 `DiagRate` 一条，加上两条 offcrit（`bgs4_*`）与 `N_L_lower_bound`。`bgs3_pair_expansion` 退回点形式 `s71_main` 自己的前件。

**定性：(i) 是二阶矩 Weil 显式公式，不是 Abel 求和**

台面上的判断是「`primeSum` 与 `pairConstant` 做 Abel 型重排」。**判死，理由三条**：

1. Abel 求和是**同一序列内部**的改写（Σ aₙbₙ → Σ Aₙ(bₙ−bₙ₊₁)），求和对象不变。 (i) 要把「有序零点对上的 K(δΔγ)² 求和」变成「素数幂上的加权和」，对象从零点换到素数——Abel 不跨这一步，任何 Abel 变体都不跨。
2. 这条恒等式的真身是 **BGS 引理 3**：Parseval 把配对和搬进 Fourier 域 ⟹ 得到 ∫ K̂²ρ₂ 型量 ⟹ 显式公式把零点侧换素数侧 ⟹ 在 **α ≤ 1** 段 form factor = 1 + 素数项 ⟹ 拆出 diag 与 prime。它只在 α ≤ 1 成立，这正好解释了我们 7/8 出局与 λ 阈值那套为何必然撞墙。
3. 账上唯一的显式公式是**一阶**：`landau_explicit_L : Σ_ρ x^{ρ−r}/(ρ−r) = trivialTerm − primePowerSum − logDerivTerm`，且全库 0 消费（死条目）。 (i) 要的是**二阶**（乘积 ⟹ 二次型），缺的零件是：Plancherel（cos-Parseval 即可，mathlib 未必有）、`triKer` 的 K̂ 显式式、对相关密度 ρ₂ 的可用形式、α ≤ 1 段的 form factor 计算。四件里只有第一件的叶子曾机检过（A4：`fourierCos triKer` = sinc²），其余三件**从未在工程内出现过**。

**登记方式（据此改写账本措辞）**

(i) 不再登记为「缺一条组合恒等式」，而登记为「**缺二阶矩显式公式模块**（BGS 引理 3 复刻）：工程量月份级，四件零件清单如上」。`DiagRate` 是它的**结论侧**，不是它的替代品。

**核族风险（A-R1，新增，必须核清）**

`s71_main` 的 A 是 `pairConstant triKer`（triKer 支撑 |u| ≤ 1，K̂ = sinc²），而 `C_MT = 1.3274993` 出自 **f₀/λ-族**的类内极小（21.10，CCLM 封顶）。两族不同 ⟹ 「A ≤ C_MT」可能大半由核更窄买下。数值侧（triKer 口径，见 增量㉝）：ζ 表 1.119396、χ₅ 表 1.188930，距 C_MT 留 0.14–0.21 富余——富余大得可疑。**两条出路**：① 在 triKer 族内重解一次类内极小，得到 C_MT^(triKer)；② 把主定理的核整体换成 f₀。核清之前，`s71_main` 不得对外表述为「配对和 ≤ 1.3275」。

**数值旁证与三条警示**

见 增量㉝ 的表。警示不复述，只记硬约束：① Lean 的 `N_L` 是抽象量（仅 `NLc·T·logT ≤ N_L T`），任何具体数值 A 都依赖归一假设；② 与 21.11 的 1.3039/1.3062 **不可并表**（核 f₀、H = 200、除 i 数）；③ 只取「富余」定性。**待办：钉 `N_L` 的真定义**——现在它只是一条 axiom 的下界，这使任何数值 A 都带 15% 级口径歧义。

**下一步（丙）的最小起手**

模块第 0 步已有叶子：`fourierCos triKer` = sinc²（A4 机检）。第 1 步：cos-Parseval（∫₀^∞ K·G = ½∫ f·g）。第 2 步：`triKer` 的对相关形式 ∫₀^∞ sinc²·K² = ∫₀¹(1−α)Q(α)dα。第 3 步：一阶矩 `landau_explicit_L` 从死条目转活（这一步本身就值得做，与 (i) 无关：`landau_explicit_L` 是全库唯一「零消费」的 A 线 axiom）。第 4 步才碰 α ≤ 1 的 form factor。

**账本**：axiom 7 / opaque 2 不变；`BGSDecompositionCore` 移除，`diagTerm` / `DiagRate` 入表；`lake build QRH` 3836 jobs 全绿。本节除探针外均为解析判断，未机检。

### 21.13 A-R1 结案：核/密度错位（第十二刀，2026-11-24）

**判决（对象层，不是界层）**

`triKer` 出现在 `pairConstant` / `primeSum` 的 K 位置，而 Lamzouri/BGS 的类约束的是**密度 f**（f = η² ≥ 0、∫f = 1、supp f ⊆ (−λ,λ)），核 **K := f̂**；`C_η = Q(0) + 2∫₀¹αQ(α)dα` 只在 2λ ≤ 1 成立。于是：

- **K = triKer 时**：f = 逆 Fourier(triKer) = sinc² 型，无紧支撑 ⟹ 类外 ⟹ A = 1.119396 / 1.188930 无主；
- **f = triKer 时**：λ = 1，2λ = 2 > 1 ⟹ 超域 ⟹ 恒等式失效，K = sinc² 的 1.085822 无主；
- **受证域 λ = 1/2 flat 支**：f ≡ 1、K = sinc(πu)、C_η = 4/3（精确）⟹ 这才是主链该用的对象。

**判据登记（第 ⑥、⑦ 项，进审计台）**

- **⑥「K 是密度还是密度的 Fourier」**：凡见到 K，先问它处在哪一侧。把 f 当 K（或把 K 当 f）会让"可容许性"变成空条件，所有常数失去归属；且这类错位**不报错、不违反类型**，只能靠"常数对不上任何文献值"这种间接征兆发现。
- **⑦「每个常数必须挂一支具体核」**：C_MT 属于 f₀ 支（Montgomery–Taylor 极值函数），4/3 属于 flat 支，二者不可互换。任何"≤ C_MT"的陈述若核不同支，结论在对象层就无意义——**这比"界太紧"严重一档**：前者要重证，后者要重述。

**本刀的落点（第十二刀，已编译已探针）**

- 新增 `sincKer u := Real.sinc (π u)`、`sincKer_zero`、`sincKer_abs_le_one`、`C_FLAT := 4/3`（§2.1a′）。
- 主链 11 处 `triKer → sincKer`、`C_MT → C_FLAT`（`bgs3`、`pair_sum_expansion`、`s71_main`、`BGSLocalUniform`、`diagTerm`、`DiagRate`、`DiagRate_to_uniform`、`primeSum_abs_le_floor`、`prime_normalized_le`、`s71_main_tail`、`s71_main_tail_diag`）＋ `QRH.lean` 两条自检 example。
- `KernelAdmissible` / `triKer_admissible` 降级为历史件：该谓词把"可容许"定义成 **K 自己紧支撑**，与密度类不是同一件事；`sincKer` 不满足它，主链不经过它。**这一条要在 21.11 的"核 = f̂"结论下读**——第七刀的 profile 口径就是 A-R1 的根因，不是笔误。
- `triKer` 的 Abel/Lipschitz 族原样保留（old-chain 专用）。

**账本**：axiom 7 / opaque 2 不变；`lake build QRH` 3836 jobs 全绿；`_probe_g1c.lean` 十条探针，`s71_main` 闭包仍为 `N_L_lower_bound + bgs3 + bgs4_low + bgs4_high`。

**数值与 5% 系统偏差（新增硬约束）**

受证域 flat 支实测 A = 1.266513（T = 8×10⁵，ζ 全表，除 N_L），定理 4/3，差 5.0%。㉜ 的 f₀ + H = 200 + 除 i 数口径差 1.5%。差异根因是**没有做 BGS Lemma 3.2 的去权**（原式带 `w(z) = 4/(4−z²)`）。硬约束：**本口径只许定性**，其"富余/亏"不许升级为定理证据；要逐字对齐必须补 w(z) 权重或按 Lemma 3.2 换核 `r_{δ,T} = Q_δ − Q_δ''/(4(logT)²)`。

**遗留**

1. 回到 C_MT 需引入 f₀ 的显式 f̂（超越表达式，工程量约本次 3–4 倍；`sincKer → f₀Ker` 属增量，不返工）。
2. 数值补 w(z) 去权。
3. `N_L` 仍是抽象参数（只有 `NLc·T·logT ≤ N_L T`）——它使任何数值 A 带 15% 级归一歧义，与本次的 5% 偏差是两类不同的误差源，勿混。

### 21.14 w(z) 的核对：加权式 / 去权式的分界就是「核的幂次」（2026-11-25，第五刀·数值口径）

**原文结构（Lamzouri §3，两句就够）**

- `w(z) = 4/(4−z²)`，z = ρ−ρ'（纯虚）⟹ `w(Δ) = 4/(4+Δ²) = (1+π²ζ²/(logT)²)⁻¹`，ζ = Δ·logT/2π。
- **Lemma 3.1（加权式）**：`Σ f̂(ζ)·w = (T/2π)logT·(f(0)+2∫₀¹αf(α)dα+O(1/√logT))` —— **核一次方 + w**。
- **Lemma 3.2（去权式）**：`r̂ = K²/w`（由 `Q̂=K²`、`Q''^(ζ)=−4π²ζ²K²` 推出），与 w 相乘抵消 ⟹ `Σ K²` **无权重**。

**判据 ⑧（进审计台）：核的幂次就是判据。** 见到 `Σ K²` 就要想到 Lemma 3.2（已去权，无权重）；见到 `Σ K·w` 才是 Lemma 3.1。把 w 加到 `Σ K²` 上，等于同时用了两条引理的核，得到的数不属于任何定理。`pairConstant` 属前者，**它无需"补 w"**。

**实算（ζ 表 T = 8×10⁵，6000 中心，partner 全表）**

| 口径 | 核 | 权重 | δ = 2.1633 | δ = 逐点 | 理论 | 残差 |
|---|---|---|---|---|---|---|
| 去权（= `pairConstant`） | sinc² | 无 | 1.19739 | 1.31200 | 4/3 | −1.6% |
| 加权（Lemma 3.1） | sinc | 4/(4+Δ²) | 1.09877 | 1.23486 | 5/4 | −1.5% |

**两个常数属不同测试函数，互不矛盾**：去权式的核 sinc² = Q̂ ⟹ f = Q（三角）⟹ `Q(0)+2∫₀¹αQ = 4/3`；加权式的核 sinc = 矩形 f 的 f̂ ⟹ `f(0)+2∫₀^{1/2}αdα = 5/4`。**两式残差同为 1.5%**，与 21.11 的 1.5% 同量级 ⟹ 有限 T 残差。

**5% 的真根因（更正增量㉞）**：不是缺 w，是 **δ 全局化**。N'(γ) = (1/2π)log(γ/2π) 在表内从 1.311（γ=2.4e4）到 1.868（γ=7.85e5）；用 T 处单值 δ 对全段求和，低端 u 被放大约 65% ⟹ sinc² 被压 ⟹ A 偏低。逐中心 δ_i 后残差 4.8% → 1.6%。

**未闭合 P-δ**：定理字面 ζ = Δ·logT/2π（≠ log(T/2π)/2π，差 15.6%）；在 δ = 2.1633 下两式给 −13%/−15%，**对不上常数**。只有逐点 δ_loc 能到 1.5%。故「定理字面尺度 ↔ 表实际间距」之间还缺一层换算（候选：z 尺度、w 在 |Δ|~T 的尾部压制、0<γ,γ'≤T 边界计数，三者叠加）。**P-δ 解开之前，只许说"δ_loc 口径下差 1.5%"，不许说"实测 = 定理常数"。**

**负面结果（单独记）**：朴素全表口径下 A = 4/3 出现在 δ ≈ 1.66（既非 2.1633 也非 1.8708）——**"调 δ 直到对表"不算对表**，它只暴露该口径缺一个因子。

**对 Lean 的含义（无代码改动，只记口径张力）**：`physDelta T = logT/2π` 与定理字面一致（Lemma 3.1 的 ζ 尺度），但它与数值上能对表的 `δ_loc(γ)` 不是同一个对象。若将来要做"实测对表"的形式化桥，得先造一个 T ↦ 逐点 δ 的映射并证明其与 `physDelta` 的差为 `O(1/log²T)` 型——**这是一件新的、独立的工作，不能靠改 `physDelta` 的定义糊过去**。
### 21.15 P-δ 结案 + 判据 ⑨「δ 与分母必须同源」（2026-11-25）

**判据 ⑨（进审计台）**：只要见到「求和尺度 δ」与「归一化分母 N」，先问二者是否**同一个 log**。δ = logT/2π 配 (T/2π)logT 是自洽的（主项口径）；δ = log(γ/2π)/2π 配 N(γ) 是自洽的（真实口径）；**δ 取主项刻度而分母取真实零点数，是异源搭配** —— 编译器不会报错，类型也对，但 A 会被系统性推出定理的误差带，表现是「常数对不上任何文献值」。这是判据 ⑥（K 是密度还是密度的 Fourier）的**同构错误**：都是「两个配对对象取自不同层级」。

**判据 ⑩（新）：先问落在谁的误差带里，再问等不等于常数。** 定理自带的误差项 O(1/√logT) 就是它的可读精度。在 T = 8×10⁵，1/√log(T/2π) = 0.292，「A = 4/3」这个等式在 ±9.7%（去权）/ ±7.3%（加权）的带里没有意义。**任何「实测 = 定理常数」的断言，若不附带宽，都是把一个带内数值伪装成等式。**

**判决数据（全表，路径 `_pd_*.py`）**

| δ 口径 | T=4e4 | 1e5 | 2e5 | 4e5 | 8e5 | 判 |
|---|---|---|---|---|---|---|
| D1 常数 logT/2π | 1.1670 | 1.1780 | 1.1862 | 1.1938 | 1.1975 | **出界 5/5**（下界 1.2361） |
| D2 常数 log(T/2π)/2π | 1.2487 | 1.2549 | 1.2604 | 1.2653 | 1.2664 | 界内 5/5 |
| D3 逐点 log(γ/2π)/2π | — | — | — | — | 1.3139 | 界内 |
| D4 逐点 log γ/2π | — | — | — | — | 1.2255 | 出界 |

**D1 出界 5/5 是本轮最硬的一条**：它不是「差一点对不上」，而是**全程落在定理不允许的读数区**。所以 ㉟ 登记的「定理字面尺度」与「表实际间距」之间缺一层换算 —— 这层换算**不存在**，因为它不是换算问题，是**刻度选错**。

**15.6% 的解析身份**：log(2π)=1.838 除以 logT=13.59 ⟹ 13.5%；精确比 logT/log(T/2π) = 1.15636。这不是笔误，是「主项 (T/2π)logT + O(T)」写法的必然代价：真实 N(T) ≈ (T/2π)log(T/2π) − T/2π + 7/8。**主项写法在 T→∞ 无害，在有限 T 上就是 15.6%。**

**界内残差的律**：残差·log(T/2π) 在 5 个 T 上稳定到 2% 以内，去权 ≈ −0.24，加权 ≈ −0.198（≈ −1/5）。这是纯有限高度项；W_u 从 25 放到 400 只把 −1.03% 收成 −0.74%，此后封顶（`_pd_trunc.txt`）。**所以「再调一调参就能对上」这条路到此为止 —— 剩下的全部是 O(1/logT)。**

**分段诊断（δ 固定 2.1633，按 γ 分段）**：残差 −32%（γ 14–300）→ −28% → −24% → −17% → −11.8%（γ 3e5–8e5），**单调塌缩，没有一段在正确值上**。这否定了「用某个全局 δ 近似全表」的整个做法：δ 在 γ=14 处比局部密度大 5.8 倍，sinc² 完全失相。

**结论（三条）**

1. δ 必须逐点取 1/局部密度；全局常数（任何值）在低端都荒谬。
2. 正确刻度 log(T/2π)/2π（常数）或 log(γ/2π)/2π（逐点），两者都在带内；剩余 5.8% 是 O(1/logT)，不是缺陷。
3. **「精确复现 4/3」永久作废**，目标改为「落带 + 预测带内位置」。

**对 Lean 的张力（未改代码，只登记）**

`physDelta T = logT/(2π)` 配 `N_L T` 是判据 ⑨ 的异源搭配。要点：**这不是「s71_main 错了」** —— s71_main 的结论是 `A ≤ C_FLAT + C₁ε + C₂`，一个上界，主项写法下依然成立（渐近意义）。真正受影响的是**任何「physDelta 口径下实测对表」的动作**，它在原理上永远差 5–6%，而且不会因任何数值手段改善。

**已落地（2026-11-25，第十三刀·纯新增）**：保留 `physDelta` 作文献字面，新增 `physDeltaRvM T := log(T/(2π))/(2π)` 与 `physWindowRvM`，docstring 标注 15.6% 与「后者才是合法读数」。不动 axiom、不动结论形状。

**落地副产品：判据 ⑨ 拿到了一个定理级的锚**。`physDelta T − physDeltaRvM T = log(2π)/(2π)` 是**与 T 无关的精确常数**，已形式化为 `physDelta_sub_physDeltaRvM`（零 axiom，`Real.log_div` + `field_simp` + `ring_nf`）。所以判据 ⑨ 不是一句提醒，而有一把可机检的尺：**两个刻度的差永远 0.2925，与高度无关；它之所以表现为 15.6%，只是被 logT 稀释。** 凡「差随 T 变化」的说法都在此被排除。

探针 `_probe_pdelta.lean`：`physDeltaRvM` / `physWindowRvM` / `physDelta_sub_physDeltaRvM` 三条全为 `[propext, choice, Quot.sound]`；`s71_main` 的 axiom 集与第十二刀后完全一致（7 条不变）。`lake build QRH` 3836 jobs 绿。

**对表探针 §2.1a″（纯新增，与主链并列）**：`pairConstantRvM T := pairConstant sincKer (physDeltaRvM T) (N_L T) (zerosLChi5UpTo T)`；`PairBandRvM T : Prop := |pairConstantRvM T − C_FLAT| ≤ (1/√log(T/2π))/3`。后者是**形状不是定理**——它把判决表变成一个可 `#check`、可被审计脚本枚举的对象，适用域 `T > 2π` 已写进 docstring。两条真证引理 `physDeltaRvM_le_physDelta`（`0 < T`）与 `physDeltaRvM_pos`（`2π < T`）给这条形状做了实体支撑：RvM 刻度严格小于主项刻度、且在适用域内为正。四条全为零业务 axiom；`s71_main` / `s71_main_tail` 的依赖闭包逐条未变。

**方法论上的一句**：这一刀证明「口径修正」可以做到完全不触碰主链——新增对象、新增形状、新增真证引理，账本一条不动。凡以后要验「某某换口径后会不会落带」的猜想，都用这个模板：造 `*RvM` 型对象 + `*Band*` 型 Prop，不进闭包。


### 21.16 例外支线审计：不是「废弃骨架」，是「两套并行、互不交接」（2026-11-25）

**对象**：`OrderPreservingBijection/Exceptional/`（31 个 .lean）。由形状清单 v2 的 42 条孤立 Prop 引出，其中 38 条在这个目录。

**第一问：是否废弃骨架？不是。** 全域检索 `:= True` / `= True` / `:= trivial` / `:= by trivial` —— **零命中**。这些 Prop 每一条都是带具体常数、具体函数、具体界的实质数学陈述，且依赖的辅助对象（`psum`/`Gchi`/`Gone`/`cn`/`Li`/`Emain`/`rhoErr`/`GoodFor`/`InRegion`）全部有真定义（无 axiom）。**七条探针 `#check` 全部通过**（`_probe_exc.lean`）：`ZFRDirichlet`、`ZeroFreeSymmetric`、`PrimeCountAsymptoticInProgressions`、`ShortIntervalImpliesProgressions`、`PrimesInProgressionCountLowerBound`、`ExceptionalCharacterCountBound`、`TailSumBound`。

**第二问：那它们是什么？三件套，两套并行。**

| 件 | 位置 | 内容 | 状态 | 消费 |
|---|---|---|---|---|
| **真件** | `ExceptionalZeroInterface.lean:11` `dirichlet_exceptional_zero_unique_zero_free_region` | Deuring–Heilbronn 型：例外零点**成对唯一**（χ=χ'∧β=β'）、β ≥ 7/8、ord=1、`c/(M²logM) ≤ 1−β`，其余零点 `ρ.re ≤ 1 − c/log(M(|im|+2))` | **真定理**（由 `GlobalTheory.ExceptionalPair.main` 供，29 文件闭包自 Alpöge–Claude 归档搬运），`[propext, choice, Quot.sound]` | **0**（除探针） |
| **图纸 A（错版）** | `Statement.lean:20` `ZFRDirichlet` | `∃c, ∀qχs: InRegion → IsLZero → χ²=1 ∧ χ≠1 ∧ im=0 ∧ L'≠0 ∧` **跨 q 全局唯一** | `def : Prop`，无证明 | 0 |
| **图纸 B** | `PrimeCountAsymptoticInProgressions.lean` 22 条 + `SmoothedRemainderRealIntegralFormula.lean` 12 条 | 从平滑余项积分公式到「AP 素数渐近」，含 `PrimeCountAsymptoticInProgressions (C₀ Cr cr cb)` 四参数结论骨架 | 全 `def : Prop`，无证明 | 22 条中 21 条 0 引用；`PrimeCountAsymptoticInProgressions` 被 `ShortIntervalImpliesProgressions` 单引用，而后者自己 0 引用 ⟹ **悬空链** |

**图纸 A 的错在哪（这一条要写死）**：真件给的是**二分法**——零点要么是「实特征例外零点（唯一）」，要么落在 `1 − c/log(M(|im|+2))` 左侧。`ZFRDirichlet` 把这个二分**压成了单一的「实特征 + 全局唯一」**，丢了例外分支，还额外要求「跨所有 q 只有一个零点」。后者与真件直接**不相容**：每个模 q 的实特征各有自己的 Siegel 零点，跨 q 唯一是假的。**它不是「未施工」，是「画错了」。**

**形态图**

```
[Alpöge–Claude 归档 · 29 文件闭包]
   GlobalTheory.ExceptionalPair.main          ← 真件，零业务 axiom
        ↓ （Interface.lean 挂名）
   dirichlet_exceptional_zero_unique_zero_free_region     ← 可用，零消费
        ↓  ←—— 缺口就在这里：P–Z 显式公式 + 例外零点分离
   22 + 12 条图纸 Prop                        ← 无证明、无引用、悬空
        ↓
   siegel_walfisz_chi5（QRH 账上的 axiom）    ← |Σ_{n≤x} Λ(n)χ₅(n)| ≤ c·x·e^{−c′√log x}
```

**结论：`siegel_walfisz_chi5` 这条 axiom 站得住。** 它标的正是全链唯一真正的空白——上游有零 axiom 真件、下游是它自己，中间那段（显式公式 + 例外分离 → 点态界）就是那 34 条图纸想干而没干的事。**这不是一条「该删的占位」，是一条「位置精确的缺口标记」。** 相对地，图纸 A 是错版，图纸 B 是未施工。

**判据 ⑪（进审计台，本轮最重要的方法论收获）**：`#print axioms` 对 `def : Prop` **返回与真定理完全相同的 `[propext, choice, Quot.sound]`**。实测：

```
ZFRDirichlet（空壳 def）                  : [propext, choice, Quot.sound]
dirichlet_exceptional_zero_unique_...（真定理）: [propext, choice, Quot.sound]
```

**所以「零 axiom」完全不代表「已证」。** 我们此前用 `#print axioms` 判账本，对 `def : Prop` 会给出**假阴性**——看起来干净，实际一个字都没证。补强规则：凡 `#print axioms` 干净者，必须同时确认它是 `theorem`（有证明项）还是 `def`（无证明项）；对 `def : Prop`，要看 `#print` 里有没有 `:= by`。判据 ⑪ 与判据 ⑩（先问误差带）合起来，才堵住这类伪装。

**行动建议（均未执行，待拍板）**

1. **✅ 已执行（2026-11-25）**：`ZFRDirichlet` 加 docstring 标「⚠ 错版，勿用，仅作历史对照」——写明「跨 q 唯一性为假」「与真件不相容」，并指向 `dirichlet_exceptional_zero_unique_zero_free_region` 为正确形态；同时注明「`#print axioms` 干净但它是 `def : Prop`，判据 ⑪ 适用」。`lake env lean` 零错误、`lake build OrderPreservingBijection.Exceptional.Statement` 3757 jobs 成功、探针 `#check` 通过、axiom 集不变（纯注释）。
2. 图纸 B 的 34 条登记「未施工」，不删（它们是 S7.6 文档的 Lean 镜像，删了会丢对照）。
3. **✅ 已执行（2026-11-25，支线接线）**：`S7_1_Main.lean` 顶部新增 `import OrderPreservingBijection.Exceptional.ExceptionalZeroInterface`；`axiom siegel_walfisz_chi5` 的 docstring 补「上游真件」段，写明该件给出的是「例外零点成对唯一 + 零自由区」二分、两件均 `#print axioms` 实测为零业务 axiom、并注明接线**只建立可指认的引用，不改 axiom 陈述、不进 `s71_main` 闭包**。

   **前置检查（均通过）**：`OrderPreservingBijection` 全域不 import QRH（无循环，命中 0）；`GlobalTheory.ExceptionalPair.main` 本身也是 `[propext, choice, Quot.sound]`（不是黑箱）。

   **接线后账本实测未动**：

   ```
   s71_main      : propext, choice, N_L_lower_bound, bgs3_pair_expansion,
                   bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound        ← 7 条
   s71_main_tail : propext, choice, N_L_lower_bound,
                   bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound        ← 6 条
   ```

   `lake env lean S7_1_Main.lean` 零错误；`lake build QRH` **4025 jobs** 成功（由 3836 增至 4025，增量全部是 OrderPreservingBijection·Exceptional 闭包的 olean，无一条 axiom 进入主链）。

   **意义**：`siegel_walfisz_chi5` 这条 axiom 第一次有了**实体上游**——不是「一条孤立的假设」，而是「上游有零 axiom 真件、下游就是它、中间那段（零自由区 → 点态 Λχ 界）无施工」的一条精确缺口标记。


