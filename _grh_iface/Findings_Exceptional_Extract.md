# 闭包 29 抽取：`ExceptionalDirichletZeroUniqueZeroFreeRegion`

日期：2026-11-23　环境：Windows / Lean v4.34.0-rc2 / mathlib HEAD `f8d25bb`

## 一、结论先行

- 29 文件全量搬运完成，逐文件编译 **全部 EXIT=0**，落 29 个 olean；总 205,066 B。加接口层 30 文件 / 30 olean。
- 根定理 `GlobalTheory.ExceptionalPair.main` 实测：`[propext, Classical.choice, Quot.sound]`——**零 axiom、零 sorry**。
- 接口层 `OrderPreservingBijection.ExceptionalZero.dirichlet_exceptional_zero_unique_zero_free_region` 同公理集。
- 全目录 `sorry / axiom / opaque / native_decide` 扫描命中 **0**。
- 代价：**2 处 API 漂移修补**（都在 `logDeriv_mul` / `logDeriv_prod` 的语句形状上），无逻辑改动。根文件与原文逐行 diff，只有 import 行不同。

## 二、方法（可复跑）

- 落点：`OrderPreservingBijection/Exceptional/`，模块名 `OrderPreservingBijection.Exceptional.<基名>`，交叉 import 同步改写；olean 落 `.lake/build/lib/lean/OrderPreservingBijection/Exceptional/`。
- 真正的难点不是 29 个文件，而是 **`import Mathlib` 在本机不可用**：`.lake/build/lib/lean/Mathlib.olean` 不存在，只有 `Mathlib.Init` 与 `Mathlib.Tactic` 两个聚合件。29 个文件全部以 `import Mathlib` 开头 → 必须逐文件换成具体模块。
- 自动修复环：
  - `_port_exc/idx.py`：扫 mathlib 8,407 个 `.lean`，建 191,585 条声明基名索引，记录每个文件出现过的命名空间；支持 `public` / `nonrec` 修饰与 unicode 名（`riemannZeta₀`、下标字符）。
  - `_port_exc/port.py`：编译 → 抓未解析标识符 → 反查模块 → 累积 import → 重编，上限 16 轮。抓四类错误：`Unknown constant/identifier/namespace \`X\``、`The identifier \`X\` is unknown`、`The environment does not contain \`X\``、`unknown module prefix \`X\``。模块选择按「标识符命名空间前缀 vs 文件命名空间」打分。
- 收敛分布：多数 1–2 轮；`DifferentiableAtFractInt`、`ZeroFreePrincipal`、`LFunctionConjEqZero`、`OrderNeTop`、`LogDerivDirichletLFunctionLocalZeroSum` 需 2 轮。两处卡死在「Invalid field / Function expected」形态，正是 API 漂移，见下节。

## 三、两处人工修补（API 漂移，非数学缺陷）

**共同根因**：当前 mathlib 把 `logDeriv_mul` 的语句写成 `logDeriv (f * g) x = logDeriv f x + logDeriv g x`（函数乘法形式），而他们写作 `logDeriv (fun z => f z * g z) x`（lambda 点乘形式）。两者外延相同但不是 syntactic match，`rw` 直接失配；`logDeriv_prod` 同理（`logDeriv (∏ i ∈ s, f i) x` vs `logDeriv (fun z => ∏ i, f i z) x`）。

1. `NormOneSubConjMul.lean:234`
   - `change logDeriv ((fun z => ∏ w ∈ S, (z - w) ^ m w) * g) z = …`（lambda → 函数乘）；
   - `have hfun : (fun z => ∏ w ∈ S, (z - w) ^ m w) = (∏ w ∈ S, fun z => (z - w) ^ m w)`，证明 `funext z; simp [Finset.prod_apply]`。
2. `NegReLogDerivPrincipalLFunctionLe.lean:97`
   - `change` 把目标里的 `logDeriv (fun z => (∏…) * ζ z) s` 归一为函数乘形式；
   - `logDeriv_mul` 的 `f` 传 **lambda**（`fun z => ∏ p ∈ q.primeFactors, …`），这样原有 `hF0 : ∏ …, 1 - p^(-s) ≠ 0` 与 `hFd` 直接可用，不必另造假设；
   - 随后的 `logDeriv_prod` 用 `hfun2 : (fun z => ∏ …) = (∏ …, fun w => …)` 过渡。

两处都只动了 `rw` 前的等价改写，被证的命题与原文一字未改。

## 四、拿到的数学内容

接口定理（原样挂出，命名 `OrderPreservingBijection.ExceptionalZero.…`）：

\[
\exists c_0>0,\ \forall c_1\in(0,c_0],\ \exists c>0,\ \forall M\ge 3\ (\text{NeZero } M):
\]

1. **例外零点唯一**：至多一个 `(χ, β)` 满足 `IsExc c₁ χ β`，且该对唯一确定；
2. **该点性质**：`χ ≠ 1`、`β ≥ 7/8`、`L(χ, β) = 0`、`ord χ β = 1`、**`1 - β ≥ c / (M² log M)`**；
3. **区域**：任意 `ρ`（`re < 1` 且 `L(χ, ρ) = 0`），要么 `(im = 0 ∧ IsExc c₁ χ ρ.re)`，要么 **`re ≤ 1 - c / log(M (|im| + 2))`**。

即 Deuring–Heilbronn / Landau–Page 型的**一致（对模 M）零点区域 + 例外零点唯一性**，常数对 M 显式。

## 五、边界（不夸大）

- 它**不给 Siegel 定理**（`L(1,χ) ≫ q^{-ε}` 那一类），也不给显式公式；它只回答「零点能离 `s = 1` 多近」。
- `#print axioms` 打印出的 3 条是 Lean 基础公理，不是「无条件证明了什么」。

## 六、对我们项目的用处（先说清不能用的）

**不能用**：

- QRH 侧残余 5 条 axiom 是 `n2_linkage`、`n3_remainder_uniform`、`N_L`、`N_L_lower_bound`、`pair_count_bound`——没有一条正好是零点区域。
- `S7_1_Main.lean:129 landau_explicit_L` 是**显式公式恒等式**（Weil 型），不是零点区域，拿它顶是错配。
- 结论：本轮**不产生 QRH 的 axiom 缩减**。说成「又消灭一条」就是自我美化。

**能用（三处，按确定性排序）**：

1. **stage_4（Weil 正性路线）**：我们谱对偶要走「排除靠近 `s = 1` 的实零点」时，可直接引 `1 - β ≥ c/(M² log M)`，不必新开 axiom。这是最硬的一处。
2. **BSD `Positivity/…`**：`delta-law` / `PStar` 层若假设「实零点不靠近 1」，可换成本定理——**须先核对具体语句**，本轮未做。
3. **GRH 侧的一般性**：任何「模 q 一致的零点区域」需求，现在树内有现成定理可引，不必再从归档抄。

## 七、顺带入库的可复用零件（这批才是长期资产）

- `GlobalTheory.Lin.logDeriv_riemann_zeta_local_zero_sum`（zeta 对数和）
- `norm_logDeriv_le`、`norm_logDeriv_factor_le`（`NormOneSubConjMul`、`NegReLogDerivPrincipalLFunctionLe`）
- `AntitoneOn.tsum_comp_add_le_integral` 用法件（`TsumOneDivRpowLe`）
- `exists_factor_order`（`ExistsFactorOrder`，零点因子分解阶）
- `DirichletLZerosEqPrimitiveCharacterZeros`（本原化搬运）
- 区域三件：`GlobalTheory.RealZeroNearOne.main`、`GlobalTheory.ZeroFreePrincipal.zero_free`、`GlobalTheory.ZeroFreeComplex.zero_free_region`（均在闭包内，已入库）

## 八、产物与审计

| 项 | 位置 |
|---|---|
| 29 个搬运文件 + 1 接口 | `C:\proj2\OrderPreservingBijection\Exceptional\` |
| olean（30） | `C:\proj2\.lake\build\lib\lean\OrderPreservingBijection\Exceptional\` |
| 公理审计 | `C:\proj2\_exc_ax.lean` / `_exc_ax.txt` |
| 逐文件轮次日志 | `C:\proj2\_port_exc\port_log.txt` |
| 最终 import 清单（可复跑） | `C:\proj2\_port_exc\state.json` |
| 索引与驱动 | `_port_exc\idx.py`、`_port_exc\port.py`、`_grh_iface\dump_closure_exc.py` |

`_exc_ax.txt` 原文：

```
'GlobalTheory.ExceptionalPair.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlobalTheory.ExceptionalPair.le_log_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'GlobalTheory.ExceptionalPair.div_log_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrderPreservingBijection.ExceptionalZero.dirichlet_exceptional_zero_unique_zero_free_region' depends on axioms:
 [propext, Classical.choice, Quot.sound]
```

## 九、下一步（建议顺序）

1. 核对 BSD `Positivity` 层哪些假设可被本定理替代（1 小时内，收益明确）。
2. QRH 的 axiom 缩减另找目标：`bgs3_pair_expansion`（D 类，最该消灭）或 `N_L`，不要指望这条。
3. 决定是否把 `Exceptional/` 纳入常规回归：它已在 `OrderPreservingBijection` lib 根下，`lake build OrderPreservingBijection` 默认会扫到；本轮未跑全 lib 构建，只逐文件编译。
