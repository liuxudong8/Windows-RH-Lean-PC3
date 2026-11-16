# A5CharQ5：A₅ 三维不可约特征标的特征标域 = Q(√5)（层 2 定理形式化）

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

> **定理目标（层 2）**：A₅ 的 3 维不可约特征标在 5 阶元上取值 (1±√5)/2，全部特征标值 ∈ Q(√5)。

**数学背景**：A₅ ≅ PSL(2,5) ≅ 二十面体旋转群。其 3 维不可约表示即二十面体表示，特征标域 Q(√5) 来自黄金比 φ = (1+√5)/2；5 阶元上的特征标值正是 2cos(2π/5) 的共轭对。

---

## 1. 项目结构与编译环境

| 项 | 值 |
| --- | --- |
| 项目根 | `C:\proj2`（lake 项目，toolchain `leanprover/lean4:v4.34.0-rc2`） |
| 库 | `A5CharQ5`（lakefile.toml 注册，依赖 `mathlib4` → 符号链接 `C:\proj\mathlib4-master`） |
| 主源文件 | `A5CharQ5/A5Defs.lean`（**1786 行**，24 条陪集作用引理 + 5 条特征标值 + #5/#6 全真证，**零 sorry**） |
| 特征标主体 | `A5CharQ5/CharValues.lean`（**零 sorry**：`icosahedral_simple` 已于 2026-11-16 真证） |
| 聚合入口 | `A5CharQ5.lean`（import 上述两者） |
| 编译命令（唯一权威） | `Set-Location C:\proj2; $env:PATH = "C:\Users\shtcl\.elan\bin;..."; lake env lean A5CharQ5\A5Defs.lean` |
| 编译状态 | **exit=0，3509 jobs**（2026-11-16，日志 `build_step12.txt`） |

---

## 2. 六项击破清单状态

| # | 项 | 状态 |
| --- | --- | --- |
| #1 | `goldenToComplex`（GoldenInt → ℂ 代数嵌入） | ✅ 无 sorry |
| #2 | 生成元 s=(12345)、t=(123)，closure{s,t} = A₅ | ✅ 无 sorry |
| #3 | `icosahedralRep` / `finrank` | ✅ **完成**：#3a/#3b/#3c 全通（24 条陪集引理真证 → 呈现完备性陪集层闭环）；#3d `icosahedralRep = FDRep.of ρG`、`finrank_icosahedralRep = 3` 已证 |
| #4 | `icosahedral_simple`（不可约性） | ✅ **已闭合**（2026-11-16，CharValues.lean:64）：`simple_iff_char_is_norm_one` ← `icosahedral_char_sum`（五段求和 = 60）← 共轭类分类。施工期困难见 §5 |
| #5 | `exists_five_order_char_phi` | ✅ **已在 A5Defs.lean 尾部真证**（取 g = sG²，`orderOf_pow` + `char_sG_sq`）；CharValues 旧声明已删（原与本文件同名，全量 build 必撞重名） |
| #6 | 五黄金引理 + `char_values_in_Q5` | ✅ **已在 A5Defs.lean 尾部真证**（嵌套 ∃ 五元组 3/φ̄/0/φ/−1，逐条 `goldenToComplex_*` + `char_*`）；CharValues 旧声明已删 |

---

## 3. 已建立的 Lean 结果（全部无 sorry）

### 3.1 #1 黄金比嵌入（A5Defs.lean 58–99）
- `alpha : ℂ := (1 + √5)/2`；`alpha_sq : alpha·alpha = 1 + alpha`（φ² = φ+1）
- `goldenToComplex : GoldenInt →ₐ[ℤ] ℂ`，附四引理：φ ↦ alpha、φ̄ ↦ 1-alpha、3 ↦ 3、0 ↦ 0、-1 ↦ -1

### 3.2 #2 生成元与 A₅（124–263）
- `s := (12345)`（5 循环）、`t := (123)`（3 循环）；`sG`、`tG` ∈ A₅（sign = 1）
- `orderOf_sG = 5`、`orderOf_tG = 3`；`card_G : Nat.card G = 60`
- `closure_eq_top : closure {sG, tG} = ⊤`（路线：3∣|SGen|、5∣|SGen|、15∣|SGen| → 阶整除论证 + 指数 ≤ 4 排除）

### 3.3 #3a 呈现群（368–406）
- `rels = {a⁵, b³, (a²b)²}`（FreeGroup(Fin 2)）；`P := PresentedGroup rels`
- `s2t_sq : (sG²·tG)² = 1`；`φ : P →* G`（a ↦ s、b ↦ t）；`φ_range_top : φ.range = ⊤`（满射）

### 3.4 #3b 显式矩阵表示（434–525）
- 常量：`c5 = (√5−1)/4`、`g5 = (1+√5)/4`、`h = 1/2`；√5 幂引理 sqrt5_sq/cube/four/five
- `icosahedralS`、`icosahedralT`：S⁵ = T³ = (S²T)² = I
- `unitS`、`unitT`、`icosahedralPsi : P →* GL(3,ℂ)`（关系元验证 → 良定义）

### 3.5 #3c 呈现完备性 |P| = 60（549–641 + 陪集层）
mathlib 无 Todd-Coxeter 工具，|P|=60 靠手工陪集枚举（H = ⟨a⟩ 的 12 左陪集 = 二十面体 12 顶点）：

- `orderOf_a = 5`、`orderOf_b = 3`、`orderOf_a2b = 2`（正方向 `one_of_mem`；反方向矛盾 / `by decide`）
- `pA`、`pB`、`cosetRep : Fin 12 → P`（12 个最短字代表）
- `pA_pow_five`、`pB_pow_three`、`pA2B_pow_two`（关系元直证模式）
- 作用引理 `coset_a_0..11`、`coset_b_0..11`（∃k, g·cᵢ = cⱼ·aᵏ 口径）——**24 条全数真证**

**Python 数值验证（tc_check.py）**：呈现 ⟨a,b | a⁵=b³=(a²b)²=1⟩ 生成恰 60 个元素（=A₅）；a=(12345) 的 12 左陪集；作用表与最短字全部确定。

### 3.6 #3c 收官：24 条陪集作用引理补证（2026-11-02 编译清零）

**盘点**：24 条声明全在位；20 条原始证明体编译通过；真坏 4 条 = `coset_a_11`（k=4）、`coset_b_7`（k=4）、`coset_b_8`（k=2）、`coset_b_11`（k=1）。其中 `coset_b_8` 先期已修至零错；收官轮处理 a_11 / b_7 / b_11 三条 + 文件末尾 3 处外围错误：

| 外围错误 | 修复 | 位置 |
| --- | --- | --- |
| φ 左逆（hbij.2 方向） | `hg.symm → hg`（方向为 `x = φ_preimage g`） | A5Defs.lean:1534 附近 |
| ψ map_mul' | `congrArg2`（ASCII 名不存在）→ `congr 1` + 两个 `(Classical.choose_spec (φ_surjective gᵢ)).symm` | :1564 附近 |
| `icosahedralRep` | 手写结构体 V/ρ 底对象类型不齐 → `FDRep.of ρG`（mathlib 官方构造 `of {V} (ρ) : FDRep R G`，`of_ρ' : (of ρ).ρ = ρ`） | :1563 |

**编译轮次收敛**（完整错误行号清单为凭；教训：勿只看尾部，build_step3i 曾误判"只剩 1 处"）：

| 日志 | 错误数 | 要点 |
| --- | --- | --- |
| build_step3f/3g/3h | 13 | batch1/2/3 消解对照 |
| build_step3i | 误读为 1 | 只看尾部，不可信 |
| build_step3j | 7 | batch4 + 手动 Edit 后权威分布 |
| build_step3k | 2 | 对称等式 `← pow_add` 卡死 + show 漏括号 |
| build_step3l | 1 | `pow_add` 拆向错误 |
| build_step3m | 1 | `a^(2+2)` 未归约 |
| build_step3n | 1 | 多余 rfl |
| **build_step3o** | **0** | **exit=0，编译清零** |

---

## 4. Todd-Coxeter 作用表（12 陪集，H=⟨a⟩）

`a·cᵢ = cⱼ·aᵏ`（i: a→j | b→j）：

```
 0: a→0 | b→1    4: a→6  | b→8    8: a→10 | b→6
 1: a→2 | b→3    5: a→7  | b→9    9: a→5  | b→2
 2: a→3 | b→5    6: a→1  | b→4   10: a→9  | b→11
 3: a→4 | b→0    7: a→8  | b→10  11: a→11 | b→7
```

最短字：`0:1, 1:b, 2:ab, 3:bb, 4:abb, 5:bab, 6:aabb, 7:abab, 8:babb, 9:bbab, 10:ababb, 11:bababb`。

24 条作用的指数 (j,k) 表（每条对应一条 Lean 引理 `∃k, g·cᵢ = cⱼ·aᵏ`）：

```
a 作用：               b 作用：
a·c0=c0·a¹  a·c6=c1·a²   b·c0=c1·a⁰  b·c6=c4·a³
a·c1=c2·a⁰  a·c7=c8·a¹   b·c1=c3·a⁰  b·c7=c10·a⁴
a·c2=c3·a³  a·c8=c10·a⁰  b·c2=c5·a⁰  b·c8=c6·a²
a·c3=c4·a⁰  a·c9=c5·a²   b·c3=c0·a⁰  b·c9=c2·a⁰
a·c4=c6·a⁰  a·c10=c9·a²  b·c4=c8·a⁰  b·c10=c11·a⁰
a·c5=c7·a⁰  a·c11=c11·a⁴ b·c5=c9·a⁰  b·c11=c7·a¹
```

交换引理（A5Defs.lean 697–837 一带）：`b_a2_comm`（pB·pA² = pA³·pB²）、`a2_b_comm`（pA²·pB = pB²·pA³）、`pB_pow_four`（pB⁴，mathlib 无 `pow_four` 空名）、`a2_b_a2_eq_b2`、`b_a2_b_eq_a3`、`a_b_a_eq_a4_b2_a4`、`b2_a2_b2_eq_b_a3_b`；辅助 `pA_pow_five`、`pB_pow_three`、`pA2B_pow_two`、`pA_pow_mod`、`pA_pow_add_fin`、`pA_inv`、`pB_inv`；后入库 `hba`、`hbab4`。BFS 词路径数值背书：a_11 12 对 RHS 全单步可达；b_11 9 对全单步可达；b_7 前 4 对单步 fwd、尾段 R4→R9 深度 3 唯一路径。

---

## 5. 当前状态与下一步

**当前状态（2026-11-15 全量核验）**：

- `lake build A5CharQ5` → **3086 jobs，exit=0，零 error**（build_step5.txt）。
- `A5Defs.lean`（1786 行 + 忠实性区块）：**零 sorry**。#5 / #6 已在文件尾部真证——此前 summary 比 lean 文件早 3 小时，误记为「未动」，**以 lean 文件为准**。
- `ConjClasses.lean`：**零 sorry**。第 1 步 4 条（cycle type 分类）+ 双分裂 2 条 + 第 2 步三类 5 条 + 第 3 步中心化子 3 条 + 5-循环计数 3 条 + **推广与 `{5}` 析取 4 条**。
- `CharValues.lean`：仅剩 **1 个 sorry** —— `icosahedral_simple`（build log 报 `:62:8`）。原两条与 A5Defs 同名的 `exists_five_order_char_phi` / `char_values_in_Q5` 已删除；注意单独编译 `lake env lean A5CharQ5\CharValues.lean` 时**不报重名**是因为吃了旧 olean，必须用 `lake build` 才能暴露冲突。

### 5.1 #4 的目标算式（数值链已全部就绪）

唯一现成判据 `FDRep.simple_iff_char_is_norm_one`（实测签名，**需要 `[Fintype G]`**）：

    Simple V ↔ ∑ g, V.character g * V.character g⁻¹ = ↑(Nat.card G) = 60

按共轭类分组即得 60：

| 类 | 代表元 | 大小 | χ 值 | 贡献 |
| --- | --- | --- | --- | --- |
| 1 | `1` | 1 | 3 | 9 |
| 2A | `sG²·tG` | 15 | −1 | 15 |
| 3A | `tG` | 20 | 0 | 0 |
| 5A | `sG` | 12 | α = φ = (1+√5)/2 | 12·α² |
| 5B | `sG²` | 12 | 1−α = φ̄ | 12·ᾱ² |

`α² = 1+α`（`alpha_sq`）、`ᾱ² = 2−α`（`alpha_bar_sq`）⟹ α² + ᾱ² = 3 ⟹ 9 + 15 + 0 + 36 = **60** ✓
五条 `char_*` 引理与上述两个平方关系**全部已证**，缺口纯粹是「类大小 + 覆盖性」两条组合事实。

### 5.2 已实测排死的路线（勿重试）

| 尝试 | 结果 |
| --- | --- |
| `instance : Fintype G := Fintype.ofFinite G` + `native_decide` | `Fintype.ofFinite` 是 **noncomputable**，编译器拒绝 |
| 直接用 mathlib 自带 `alternatingGroup.instFintype` | 定义为 `Subtype.fintype _ _ sign.decidableMemKer _`，底层同样 noncomputable；`native_decide` 报 `depends on 'instFintypeSubtypePermFinOfNatNatMemSubgroupG'` |
| `decide`（核归约） | `Fintype.ofFinite` 的 `univ` 不可核归约，同样不可用 |
| `Finset.any` / `Finset.all` | mathlib 无此字段 |
| `native_decide` 直接作用含 `IsConj` 的 Prop | `IsConj` 无 `Decidable` 实例（即便有也需可执行 `Fintype`） |

**结论：60 元素穷举是死路，必须走群论论证（cycle type 分类 + A₅ 内共轭 + 类大小）。**

### 5.3 可用的 mathlib 工具（已 Read 源码确认）

| 引理 | 用途 | 限制 |
| --- | --- | --- |
| `Equiv.Perm.isConj_iff_cycleType_eq` | 同 cycle type ⟺ 共轭 | 只在 S₅ 层面 |
| `alternatingGroup.isConj_of` | S₅ 内共轭 ⟹ A₅ 内共轭 | 需 `support.card + 2 ≤ 5`，即 support ≤ 3（故只覆盖 3-循环） |
| `alternatingGroup.isThreeCycle_isConj` | A₅ 中两个 3-循环必共轭 | 直接可用 ✓ |
| `alternatingGroup.isConj_swap_mul_swap_of_cycleType_two` | 双换位共轭 | 已 deprecated；且要求 `cycleType` 全为 2，Fin 5 的 `{2,2,1}` 含 1 需先剥掉 |
| `alternatingGroup.isSimpleGroup` | A₅ 单群 | 可用于 `ρG` 忠实性 |
| `FDRep.char_conj` | `χ(hgh⁻¹) = χ(g)`（类函数性） | 直接可用 ✓ |

### 5.4 #4 施工路线（按依赖顺序，纯工程、数学无风险）

1. **cycle type 分类**：`∀ g : G, cycleType g ∈ {1⁵, 2·2·1, 3·1·1, 5}`（`sign_of_cycleType` + `sum = 5` 枚举 5 的 7 个 partition，偶的恰 4 个）。
2. **类覆盖**：四种 cycle type 分别共轭到 `1 / sG²·tG / tG / sG 或 sG²`；5-循环的 A₅ 双分裂须单独处理（`sG` 与 `sG²` 不共轭）。
3. **类大小**：轨道-稳定化子 `|G| = |orbit| × |centralizer|`，中心化子用显式元集识别（1→60、2A→4、3A→3、5→5）。
4. **分组求和**：`Finset.sum` 按 5 类拆（`Finset.sum_union` + `Disjoint`），代入已证五值与 α²/ᾱ²，`norm_num` 收 60。

第 1、2 步是主要工作量（约 200–300 行 Lean），第 3、4 步约 100–150 行。

**已完成（2026-11-07）：表示忠实性 `ρG.ker = ⊥`**

论证三段：(1) `MonoidHom.ker` 自动是正规子群；(2) `G = A₅` 单群 ⟹ 核 = ⊥ 或 ⊤（`Subgroup.Normal.eq_bot_or_eq_top`）；(3) 取 g = sG，`ρG sG = toLin' S ≠ 1`，故核 ≠ ⊤。

关键技巧：**不要碰 √5**。用 `S` 的 (0,1) 分量 = 1/2 而单位阵该位为 0，作用在基向量 e₁ 上取第 0 分量即可矛盾；若用 (0,0) 分量会撞上 `-g5 ≠ 1` 这种带根号的实数比较。

落点（A5Defs.lean 末尾）：`rhoGMonoidHom`（ρG 包装成 `G →* End(ℂ³)`）、`icosahedralS_ne_one`、`ρG_sG_ne_one`、`rhoG_ker_eq_bot`，外加 `ρG_injective`。全量 build **3085 jobs 通过**。

**第 1 步已完成（2026-11-07）：cycle type 分类**

新模块 `A5CharQ5/ConjClasses.lean`（已并入根模块），四条：

| 引理 | 内容 |
| --- | --- |
| `two_mul_card_le_sum` | multiset 每项 ≥ 2 ⟹ `2 * card ≤ sum` |
| `G_cycleType_card_le_two` | A₅ 元素 `cycleType.card ≤ 2` |
| `G_even_sum_add_card` | A₅ 元素 `Even (sum + card)`（由 `sign = 1` 与 `sign_of_cycleType`） |
| `G_cycleType_cases` | **cycleType ∈ {∅, {3}, {5}, {2,2}}** |

只用三条 mathlib 事实：`sum_cycleType_le`（sum ≤ 5）、`two_le_of_mem_cycleType`（每项 ≥ 2）、`sign_of_cycleType`（`(-1)^(sum+card) = 1` ⟹ 偶）。三种组合情形由 `card ∈ {0,1,2}` + `omega` 收口。

**第 2 步核心已完成（2026-11-07）：5-循环双分裂**

`alpha_ne_half` + `sG_not_isConj_sG_sq : ¬ IsConj sG (sG²)`。全量 build 3086 jobs。

**关键：不走 24 个 5-循环的组合计数，直接走特征标。** 若 sG 与 sG² 共轭，则存在 c 使 `c·sG·c⁻¹ = sG²`，于是 `χ(sG²) = χ(sG)`（`FDRep.char_conj`），即 **α = 1−α ⟹ α = 1/2**，与 α = (1+√5)/2 矛盾。

这一击把「5A ≠ 5B」从**组合计数事实**降级为**一条代数恒等式**：不用数任何共轭类的大小，也不用处理 5-循环在 A₅ 中的双分裂构造。实现上有两个坑：`IsConj` 给出的共轭元是 `(↥G)ˣ`，要显式 `(↑c : G)`；`α ≠ 1/2` 用 `Complex.re` 取实部转成实数比较，绕开 `ofReal` cast 的写法纠纷。

**第 2 步已完成（2026-11-15）：三类共轭全部落地**

`ConjClasses.lean` 新增五条：

| 结果 | 内容 | 关键技法 |
| --- | --- | --- |
| `G_cycleType_empty_isConj` | `cycleType = 0 ⟹ IsConj g 1` | `cycleType_eq_zero.mp` → `Subtype.ext`；**`rw [hg]` 会顺手把目标关掉（No goals to be solved），必须 `subst hg`** |
| `G_threeCycle_isConj` | `cycleType = {3} ⟹ IsConj g tG` | 直接 `alternatingGroup.isThreeCycle_isConj`；因 `IsThreeCycle` 的定义就是 `cycleType = {3}`（`Cycle/Type.lean:625`），`h` 可当 `hσ` |
| `swap_commute_involution` | 对合 σ 与 `swap a (σa)` 交换 | `hsq` 取点值必须 `congrArg (fun f => f x) hσ`（`congrFun` 类型不匹配）；`ext x` 三分类 |
| `G_twoTwo_isConj` | `cycleType = {2,2} ⟹ IsConj g (sG²·tG)` | S₅ 共轭 + 奇置换修正 |
| `G_cycleType_cases_isConj` | 除 {5} 外三类打包 | 由上面三条 + `G_cycleType_cases` 组合 |

**{2,2} 为什么必须自建路线**：`alternatingGroup.isConj_of` 的充分条件是 `support.card + 2 ≤ 5`；双换位 support = 4、只有 1 个不动点，**不满足**（该证明要求找 2 个不在 support 的点做 swap 修正）。自建四步：

1. `cycleType = {2,2} ⟹ orderOf = 2 ⟹ g² = 1`（`lcm_cycleType` + `pow_orderOf_eq_one`）
2. S₅ 层 `isConj_of_cycleType_eq` 得 π
3. `sign π = 1`：直接落 A₅
4. `sign π = -1`：取 σ 的非不动点 a，`w = swap a (σa)` 与 σ 交换，则 `sign (π·w) = (-1)(-1) = 1` 且 `(πw) σ (πw)⁻¹ = π σ π⁻¹`

**六个实现坑（{2,2} 密集踩，全部已踩通）**：

- `Equiv.Perm.swap` 被解析成 `Function.swap`，正确名是 **`Equiv.swap`**
- `subst h1`（`h1 : x = a`）会把 `a` 消掉变 unknown identifier，改用 `rw [h1]`
- `hπ : SemiconjBy ↑πu g rep` 是 **def 非结构**，`rw [← hπ]` 方向不对且 whnf 发散；先 `have hπ' : ↑πu * ↑g = ↑rep * ↑πu := hπ` 再 `rw [hπ']`
- `apply Subtype.ext` 后的 `show` 会在子群 coercion 处 whnf 循环（20 万心跳超时）；改用 `simp only [Subgroup.coe_mul, Subgroup.coe_inv]`
- `simp only [Subgroup.coe_mul]` 会把 `↑(sG²·tG)` 一并展开成 `↑(sG²) * ↑tG`，收尾须补同一条；**`Units.coe_inv` 不存在**
- `(sG²·tG).cycleType = {2,2}` 用 `native_decide` 秒过（`decide` 超时）

**第 3 步（2026-11-15）：中心化子论证落地，`sG` 的类大小 = 12**

三条新增（`ConjClasses.lean`）：

| 结果 | 内容 |
| --- | --- |
| `G_centralizer_sG_eq_closure` | `C_{A₅}(sG) = ⟨sG⟩` |
| `G_centralizer_sG_card` | `Nat.card C_{A₅}(sG) = 5` |
| `G_class_sG_card` | `Nat.card (ConjClasses.mk sG).carrier = 12` |

**论证链**：

1. 上界 `⟨sG⟩ ≤ C(sG)`：`Subgroup.closure_le` 归结为 `sG ∈ C(sG)`，`rfl`。
2. 下界用基数：`Nat.card C_{A₅} ≤ Nat.card C_{S₅} = 5`。
   - S₅ 层：`Equiv.Perm.nat_card_centralizer` 代入 `cycleType = {5}`，`(5−5)! * 5 * 1! = 5`；
   - 桥接：`Subtype.val` 构造注入 `C_{A₅} → C_{S₅}`，`Nat.card_le_card_of_injective`。
3. `Subgroup.eq_of_le_of_card_ge` 收口。
4. 类大小：`ConjClasses.card_carrier` 给 `|G| / |stabilizer|`，配合
   `Subgroup.nat_card_centralizer_nat_card_stabilizer` 把中心化子接到 `ConjAct` 稳定化子，`60 / 5 = 12`。

**四个实现坑（本轮新踩）**：

- `Subgroup.mem_centralizer_iff` 虽是 `Iff.rfl`，但 `rw` 匹配不到 `sG ∈ ↑(centralizer {sG})`（coercion 层不同）；改用 `change ∀ h ∈ ({sG} : Set ↥G), h * sG = sG * h` 直接落目标。
- `Nat.card` 与 `Fintype.card` **不是 defeq**，但 `60 / 5` 与 `12` **是 defeq**——`rw [hS]` 后目标自动变 `12 = 12` 并 rfl 关闭，多写的 `norm_num` 反报 "No goals to be solved"。
- `rw [Nat.card_eq_fintype_card]` 必须紧邻 `exact hcard` 之前，不可提前。
- `haveI : Fintype ↥G := Fintype.ofFinite _` 在证明里可用——此前排死的是「`native_decide` + Fintype」，不是 Fintype 本身。

**第 3 步预备：5-循环计数（2026-11-15）**

三条新增（`ConjClasses.lean`）：

| 结果 | 内容 |
| --- | --- |
| `G_fiveCycle_orderOf` | `cycleType = {5} ⟹ orderOf g = 5` |
| `perm_fiveCycle_count` | S₅ 层 5-循环总数 = 24 |
| `G_fiveCycle_count` | A₅ 层 5-循环总数 = 24 |

**计数口径（用户纠正）**：`n`-循环个数 `= (n−1)!`，**不是** `C(5,4)·4! = 120`。5-循环 `= 4! = 24`。

**证明要点**：

1. `orderOf`：`cycleType = {5}` ⟹ `lcm {5} = 5`（`lcm_cycleType`），再 `Subgroup.orderOf_coe` 桥回 `↥G` 层。
2. S₅ 层：`card_isConj_eq` 代入 `{5}` 得 24，用 `isConj_iff_cycleType_eq` 把 `{h | IsConj sG h}` 改写成 `{h | cycleType h = {5}}`。
3. A₅ 层：`Nat.card_congr` + `Equiv.ofBijective`，`g ↦ ⟨g.val.val, g.2⟩`；满射用 `sign_of_cycleType` 得 `(-1)^6 = 1` 故 `h ∈ A₅`。

**四个坑**：

- `rw [← Equiv.Perm.lcm_cycleType]` 的参数名是 `σ` 不是 `g`；裸 `rw` 靠 unification 即可，无需显式命名。
- `orderOf (↑g)` 与 `orderOf g` 不是 defeq，须 `rw [← Subgroup.orderOf_coe]`。
- `rw` 匹配不到 `h ∈ {h | IsConj ...}`，须先 `simp only [Set.mem_ofPred_eq]`（`Set.mem_setOf_eq` 已 deprecated）。
- `(-1 : ℤˣ)^6 = 1` 用 `decide` 收，`norm_num` 在 units 层不收。

**第 3 步推广与 `{5}` 析取收口（2026-11-15）**

四条新增（把中心化子论证从 `sG` 推广到任意 5-循环，并收口析取）：

| 结果 | 内容 |
| --- | --- |
| `G_centralizer_fiveCycle_eq_closure` | 任意 `{5}`-型 `g`：`C_{A₅}(g) = ⟨g⟩` |
| `G_class_fiveCycle_card` | 任意 `{5}`-型 `g`：`Nat.card (ConjClasses.mk g).carrier = 12` |
| `G_class_fiveCycle_set_card` | 任意 `{5}`-型 `g`：`Nat.card {h | IsConj g h} = 12` |
| **`G_fiveCycle_isConj_sG`** | 任意 `{5}`-型 `g`：`IsConj g sG ∨ IsConj g (sG ^ 2)` |

**析取证明链**：`sG` 类与 `sG²` 类各 12、互不相交（双分裂 `¬ IsConj sG sG²`），合计 24 = A₅ 中 5-循环总数；`Set.eq_of_subset_of_ncard_le` 给出集合等式 `5-循环 = sG类 ∪ sG²类`；`g` 是 5-循环，故落在并集中。

**本轮踩的坑**：

- `eq_of_le_of_card_ge` 的 H 是左边。目标 `C = ⟨g⟩` 要先 `Eq.symm` 转成 `closure = C`，否则 `rw [Subgroup.closure_le]` 在 `C ≤ closure` 上找不到模式。
- `IsConj` 的 witness 是 **units**（`(↥G)ˣ`）。跨层到 `Perm` 不能写 `↑↑c`，须 `Units.map (Subgroup.subtype (alternatingGroup (Fin 5))) c`。
- `simpa` 展开 `SemiconjBy` 要把 `SemiconjBy`、`Units.coe_map` 显式放进 simp 集，否则只化简到 `↑↑c * ↑sG = ↑h * ↑↑c` 而匹配不到 `SemiconjBy`。
- `Set.eq_of_subset_of_ncard_le` / `Set.ncard_union_eq` 的 `Finite` auto 参数不自动解，须显式 `(ht := by exact Set.toFinite _)`。
- `Nat.card` ↔ `ncard` 用 `Nat.card_coe_set_eq`（`Nat.card ↥s = s.ncard`），且 union 的目标已经是 `ncard` 形态，不要再反复 rw。

**第 3 步：`{2,2}` 类大小 = 15（2026-11-15）**

关键观察：**双换位全是偶置换**——`sign (σ) = (-1)^(sum + card) = (-1)^(4+2) = 1`，所以 S₅ 中的 15 个双换位全部落在 A₅，A₅ 的 `{2,2}` 类就是 S₅ 的那 15 个。不用中心化子论证（`C_{S₅}(σ)` 是 8 元的 D₈，它在 A₅ 中的那一半只有 4 个，比 5-循环的 `⟨g⟩` 难算）。

| 结果 | 内容 |
| --- | --- |
| `perm_twoTwo_count` | S₅ 层：`Nat.card {h \| h.cycleType = {2,2}} = 15`（`120 / 8`） |
| `G_twoTwo_set_card` | A₅ 层：`Nat.card {g : ↥G \| g.val.cycleType = {2,2}} = 15` |

**证明结构**（复用 5-循环模板）：

1. `Equiv.Perm.card_isConj_eq` 代入 `{2,2}`：`120 / (1! · 4 · 2!) = 15`（`norm_num` 收）。
2. `isConj_iff_cycleType_eq` 把 `{h | IsConj rep h}` 改写成 `{h | cycleType h = {2,2}}`。
3. A₅ 桥：`Nat.card_congr` + `Equiv.ofBijective`，签名 `sign_of_cycleType` 代入 `{2,2}` 得 `(-1)^6 = 1`（`decide`），再由 `mem_alternatingGroup` 造逆像。

**类大小谱已齐**：`1 + 15 + 20 + 24 = 60`，只剩 `{3}` 的 20。

**第 3 步：`{3}` 类大小 = 20（2026-11-15）**

同一机制：**3-循环也是偶置换**——`sign = (-1)^(3+1) = 1`，S₅ 的 20 个 3-循环全部在 A₅。

| 结果 | 内容 |
| --- | --- |
| `perm_threeCycle_count` | S₅ 层：`Nat.card {h \| h.cycleType = {3}} = 20`（`120 / 6`） |
| `G_threeCycle_set_card` | A₅ 层：`Nat.card {g : ↥G \| g.val.cycleType = {3}} = 20` |

代表元取 `tG = (123)`，`cycleType = {3}` 由 `decide` 直接给。

**类大小谱全部收齐**：`1 + 15 + 20 + 12 + 12 = 60` ✓ 与 `Nat.card G = 60` 严格一致。

**第 4 步（一）：两个求和的基石（2026-11-16）**

| 结果 | 内容 |
| --- | --- |
| `char_sG_inv` | `χ(sG⁻¹) = 1 − α`（`sG⁻¹ = sG⁴`，`tr(S⁴)` 直接矩阵展开算） |
| `char_eq_of_isConj` | `IsConj g h ⟹ χ(h) = χ(g)`（`char_conj` 的 `IsConj` 形式） |

**`toLin'` 桥（C 路线）的关键**：`Matrix.toLin'` 是 `LinearEquiv` 不是 `MonoidHom`，`map_pow` 不可用；必须手工把 `S⁴ = S²·S²`、`toLin'(A*B) = toLin' A ∘ₗ toLin' B` 两边同步展开，最后 **`rfl`** 收——因为 `LinearMap` 的 `*` 与 `∘ₗ` 是 defeq。

**`tr(S⁴)` 的数值路径**：`S⁴ = (S·S)·(S·S)` 后 `simp [Fin.sum_univ_succ, icosahedralS, c5, g5]` + `ring_nf` + `norm_num [sqrt5_*]`，结果 `ᾱ`。

**第 4 步（二）待做**：五段 `Finset.sum_filter_add_sum_filter_not` 拆分求和（1/20/15/12/12）、每段类常数性、代入 `simple_iff_char_is_norm_one`。

**本轮踩的坑**：

- `Matrix.toLin'` 的 `map_pow` 报 `MonoidHomClass` 缺失——它是 `LinearEquiv`，没有幂同态性。
- `Matrix.toLin'_mul` 的方向是 `toLin'(A*B) = toLin' A ∘ₗ toLin' B`，反向 `rw` 要 `←`。
- `pow_two` 一次 `rw` 会替换**所有** `^2` 出现，第二次 `rw` 会报 "Did not find the pattern"。
- `pow_two` 作为 `from` 证明时必须显式传参数：`from pow_two (S : Matrix ...)`。
- 收尾 `rfl`：`LinearMap` 的 `*` 与 `∘ₗ` defeq，能直接关。

**剩余**：

- `{5}` 类析取 `IsConj g sG ∨ IsConj g (sG²)`：**已完成**（`G_fiveCycle_isConj_sG`）。
- 共轭类大小 1 / 15 / 20 / 12 / 12：**全部完成**（`{1}` 平凡，其余四条定理）。
- 第 4 步 `Finset.sum` 分组收 60（不可约性判据）：未做。

---

## 6. 关键调试经验（已确认的坑与模式）

- **矩阵定义**用 `!![...]`（非 `![]`）；幂展开靠 `change` + `rw [pow_succ]` 链，每层乘法恰好一次 `simp`
- **√5 多项式收尾**：`ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num`；重复 simp 报 "made no progress"
- **呈现群阶**：`PresentedGroup.mk (x^5)` 需显式 `rels`；关系元引理用 `one_of_mem` + `simpa [rels]` 最稳
- **幂引理**：`simpa [orderOf_x] using pow_orderOf_eq_one` 会过化简成 True → 用 `have h := pow_orderOf_eq_one` + `rw [orderOf_x] at h` + `exact h` 或直接 `one_of_mem`
- **存在量化指数**：`∃ k : Fin 5, ... ^ k` 需 `k.val`（Fin 5 非 Nat）；引入用 `use (k : Fin 5)`
- **结合律方向**：右结合形 `x·(y·z)` 要 `rw [← mul_assoc]`（`mul_assoc` 正向只匹配左结合形）
- **G 中子群乘法**的 `congrArg Subtype.val` 深层 whnf 会心跳超时 → 用 `by decide`
- **编译反馈**：`lake build` 吞错误详情；单文件用 `lake env lean A5CharQ5\A5Defs.lean`；日志用 `Out-File -Encoding utf8`；以完整错误行号清单为准，勿只看尾部
- **本轮新机制点（陪集引理补证实战）**：
  1. `nth_rewrite_lhs` 在 mathlib 不存在 → `nth_rewrite <n> [...]`；裸 `rw [h]` 是**递归重写所有匹配**（"拆过头/重复行"根源），精确只动一处必须 `nth_rewrite 1`
  2. 左结合链尾部 `(…·b)·b` 不是 `b·b` 子树，`rw [← pow_two]` 匹配不到 → 先 `group` 括成 `(b·b)` 块
  3. `pow_add` 的 LHS 是 `a^(m+n)`：合成 `a²·a²→a⁴` 用 `← pow_add`；`rw` 后自动归约 `(2+2)→4` 闭合，`nth_rewrite 1` 不归约会留 unsolved
  4. 对称等式里 `rw [← pow_add]` 双向匹配互相抵消卡死 → `rw [show 单项 = 目标 by rw [← pow_add]]`（show LHS 须为目标当前形态）
  5. `group` 不展开 `^2` 幂节点；`congrArg2`（ASCII 名）不存在 → `congr 1` + 逐项 `exact (Classical.choose_spec (φ_surjective gᵢ)).symm`
  6. calc 某步被闭合后多余 rw/show 行报 `No goals to be solved`

---

## 7. 与三主线（QRH/BSD/RH）的关系

本定理是"可读证明"路线的一块拼图：不追求 43M 行巨无霸，而是把经典有限群论事实（二十面体群、呈现完备性、特征标域）小步形式化，每条引理带数学注释，可直接用人话读通。特征标域 Q(√5) 与结理论、五边形/黄金比结构同源（用户早期"结"理论笔记的收敛点之一）。A5CharQ5 工程在 GitHub（liuxudong8/Windows-RH-Lean-PC2）中以 `A5CharQ5\<日期>` 快照随 push.ps1 一键同步。

## 第 4 步（二）：五段求和（2026-11-16，本轮完成）

`ConjClasses.lean` 尾部新增，全部零 sorry、单文件 exit=0、全量编译无错。

| 定理 | 段定义 | 大小 | 每项值 | 段和 |
|---|---|---|---|---|
| `sum_zero_class` | `cycleType = 0` | 1 | 9 | **9** |
| `sum_three_class` | `cycleType = {3}` | 20 | 0（只需 χ(g)=0） | **0** |
| `sum_two_two_class` | `cycleType = {2,2}` | 15 | 1（g²=1 ⟹ g⁻¹=g，χ=−1） | **15** |
| `sum_five_a` | `cycleType={5} ∧ IsConj g sG` | 12 | ᾱ² = 2−α | **12(2−α)** |
| `sum_five_b` | `cycleType={5} ∧ IsConj g sG²` | 12 | α² = 1+α | **12(1+α)** |

合计 `9 + 0 + 15 + 12(2−α) + 12(1+α) = 24 + 36 = 60 = |G|` ✓

**配套基石（同批并入）**：

- `G_isConj_cycleType : IsConj g h → h.cycleType = g.cycleType`（A₅ 内共轭保持 cycleType，
  经 `h = c·g·c⁻¹` 转到 Perm 层用 `Equiv.Perm.cycleType_conj`）
- `sG_pow_eq_one`、`sG_inv_eq_pow_four`、`sG_val_cycleType`（`decide`）
- `sG_sq_val_cycleType`（`native_decide`）、`sG_sq_inv_eq_cube : (sG²)⁻¹ = sG³`

**{5} 两段的 card=12 路线**（不走 cycleType 保持，走集合相等）：

`{g | cycleType = {5} ∧ IsConj g sG} = {g | IsConj sG g}` → 用 `G_class_fiveCycle_set_card`
——正向靠 `IsConj.symm`，反向靠 `G_isConj_cycleType` 补出 `cycleType = {5}`。

**本轮新踩的坑（勿重试）**：

1. `∑ g in s, f g` **notation 在本文件不可用**（报 `unexpected token 'in'`，`open scoped BigOperators`
   也无效）。必须写 `Finset.sum s (fun g => ...)` 显式形式。
2. **含 `IsConj` 的 `Finset.filter` 谓词出现在定理声明（类型）里时，`classical` 救不了**——
   证明体内的 `classical` 管不到声明。必须在 import 之后加
   `attribute [local instance] Classical.propDecidable`（全局，代价是编译变慢）。
3. `simp only [Set.mem_ofPred_eq]` 会把 `IsConj` **展开成 `∃ c, SemiconjBy ...`**，
   之后 `IsConj.symm` 就匹配不上了。改用 `change (A ∧ IsConj g sG) ↔ IsConj sG g` 保住 `IsConj`。
4. `IsConj.symm hc` 的方向：若 `hc : IsConj sG g`，传给 `G_isConj_cycleType sG g` 的应是
   **`hc` 本身**，不是 `IsConj.symm hc`。
5. `12 + 12 * alpha = 12 * (1 + alpha)` 的收尾要 `ring`，`norm_num` 不够（含变量）。
6. 给 `ConjClasses.lean` 的 import 块插入 `attribute` 时**不能插在两条 import 之间**
   （报 `invalid 'import' command, it must be used in the beginning of the file`），必须放在全部 import 之后。

**仍缺一步**：`icosahedral_char_sum : ∑ g, χ(g)χ(g⁻¹) = 60` 的组装（`univ` = 五段 disjoint union），
以及代入 `FDRep.simple_iff_char_is_norm_one` 关闭 `icosahedral_simple`。

## 第 4 步（三）：总装 —— `icosahedral_char_sum` 与 `icosahedral_simple`（2026-11-16，全库零 sorry）

| 定理 | 内容 | 落点 |
|---|---|---|
| `icosahedral_char_sum` | `∑ g : ↥G, χ(g)χ(g⁻¹) = 60` | ConjClasses 末尾「第 4 步（三）」 |
| `icosahedral_simple` | `Simple icosahedralRep`（**最后一条 sorry 关闭**） | CharValues:64 |

组装路线：5 次 `rw [← Finset.sum_filter_add_sum_filter_not]` 逐层拆 `univ.sum` →
四条桥 `hb2..hb5`（`filter_filter` + `filter_congr`）把累积 filter 化回裸 filter →
`hempty` 证末段空 → `rw [五条段定理]` + `ring`。

收尾：`rw [FDRep.simple_iff_char_is_norm_one]` → `rw [card_G]` → `exact icosahedral_char_sum`。

### 六个坑（总装阶段）

1. **`filter_filter` 叠两次以上的 ∧ 是右结合**：`rw [Finset.filter_filter, Finset.filter_filter]` 从外套到内，得 `¬p1 ∧ (¬p2 ∧ p3)`，取 p3 要 **`h.2.2`**；三层 `h.2.2.2`，四层 `h.2.2.2.2`。构造方向同步右嵌套 `⟨h1, ⟨h2, h3⟩⟩`。
2. **但 `simp only [Finset.mem_filter]` 展开累积 filter 得左结合**：`((¬p1 ∧ ¬p2) ∧ ¬p3) ∧ ¬p4`，投影要 `hg.1.1.1.1` / `hg.1.1.1.2` / `hg.1.1.2` / `hg.1.2` / `hg.2`。同一子句里两种结合方向并存，别一律套。
3. **`⟨...⟩` 内嵌 `by ...; tactic` 必须括号**：`⟨(by rw [h]; decide), h⟩`，否则 `by` 块吞掉 `, h`，报 `Invalid ⟨...⟩ notation: expected type (cy = 0 → False) is not an inductive type`。
4. **`intro h0` 之后 `decide` 无法证 `False`**：`decide` 证明的是命题真假，目标是 `False` 时它反过来证明「False 为假」。正确写法是**不 intro**，直接 `rw [h]` 把 `¬ P` 规约成 `¬ {3} = 0` 再 `decide`。
5. **`Finset.eq_empty_iff_forall_notMem`（大写 M）**——不是 `eq_empty_iff_forall_not_mem`。
6. **`G_cycleType_cases` 的 `rcases` 分支顺序是 0 / {3} / {5} / {2,2}**，第 3 支为 `{5}`（要 `G_fiveCycle_isConj_sG` 二分），第 4 支为 `{2,2}`。写成 0/{3}/{2,2}/{5} 会把 `hc : cy = {5}` 喂给 `¬cy={2,2}`。

### 一个 import 坑

`FDRep.simple_iff_char_is_norm_one` 需要 `IsAlgClosed ℂ`，实例在 **`Mathlib.Analysis.Complex.Polynomial.Basic`**（不是 `Mathlib.Analysis.Complex.Polynomial`，后者无 olean）。

### 状态

- `lake build A5CharQ5`：**3509 jobs，EXIT=0**；
- A5Defs / ConjClasses / CharValues / 根模块 **真实 sorry 计数 = 0**；
- 击破清单 #4 关闭。
