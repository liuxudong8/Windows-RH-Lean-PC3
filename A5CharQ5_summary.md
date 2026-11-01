# A5CharQ5：A₅ 三维不可约特征标的特征标域 = Q(√5)（层 2 定理形式化）

> **定理目标（层 2）**：A₅ 的 3 维不可约特征标在 5 阶元上取值 (1±√5)/2，全部特征标值 ∈ Q(√5)。

**数学背景**：A₅ ≅ PSL(2,5) ≅ 二十面体旋转群。其 3 维不可约表示即二十面体表示，特征标域 Q(√5) 来自黄金比 φ = (1+√5)/2；5 阶元上的特征标值正是 2cos(2π/5) 的共轭对。

---

## 1. 项目结构与编译环境

| 项 | 值 |
| --- | --- |
| 项目根 | `C:\proj2`（lake 项目，toolchain `leanprover/lean4:v4.34.0-rc2`） |
| 库 | `A5CharQ5`（lakefile.toml 注册，依赖 `mathlib4` → 符号链接 `C:\proj\mathlib4-master`） |
| 主源文件 | `A5CharQ5/A5Defs.lean`（约 650 行，63 条声明） |
| 特征标主体 | `A5CharQ5/CharValues.lean`（3 个 sorry 待击破） |
| 聚合入口 | `A5CharQ5.lean`（import 上述两者） |
| TC 数值验证 | `A5CharQ5/tc_check.py` |
| 编译命令 | `$env:PATH = "C:\Users\shtcl\.elan\bin;..."`; `lake build A5CharQ5`（3085 jobs） |

---

## 2. 六项击破清单状态

| # | 项 | 状态 |
| --- | --- | --- |
| #1 | `goldenToComplex`（GoldenInt → ℂ 代数嵌入） | ✅ 无 sorry |
| #2 | 生成元 s=(12345)、t=(123)，closure{s,t} = A₅ | ✅ 无 sorry |
| #3 | `icosahedralRep` / `finrank` | ⏳ #3a/#3b 完成；#3c 进行中；`icosahedralRep`/`finrank` 仍 sorry |
| #4 | `icosahedral_simple`（不可约性） | ⬜ sorry（未动） |
| #5 | `exists_five_order_char_phi` | ⬜ sorry（未动） |
| #6 | 五黄金引理 + `char_values_in_Q5` | ✅ 代数骨架完成；`char_values_in_Q5` 主体 ⬜ |

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

### 3.5 #3c 呈现完备性 |P| = 60（549–641）
mathlib 无 Todd-Coxeter 工具，|P|=60 靠手工陪集枚举（H = ⟨a⟩ 的 12 左陪集 = 二十面体 12 顶点）：

- `orderOf_a = 5`、`orderOf_b = 3`、`orderOf_a2b = 2`（正方向 `one_of_mem` 关系元；反方向矛盾 / `by decide`）
- `pA`、`pB`、`cosetRep : Fin 12 → P`（12 个最短字代表）
- `pA_pow_five`、`pB_pow_three`、`pA2B_pow_two`（关系元直证模式）
- 样板作用引理 `coset_a_0`、`coset_b_3`（∃k, g·cᵢ = cⱼ·aᵏ 模式确立）

**Python 数值验证（tc_check.py）**：呈现 ⟨a,b | a⁵=b³=(a²b)²=1⟩ 生成恰 60 个元素（=A₅）；a=(12345) 的 12 左陪集；作用表与最短字全部确定。

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

交换表：双字母形仅 `b·a² = a³·b²`；`b·a`、`b·a³`、`b·a⁴` 需更长字（逐条独立约化）。

---

## 5. 当前状态与下一步

**当前主线：#3c**（呈现完备性）。已打通样板证明模式（`use k` + `simp [cosetRep]` + `rw [← mul_assoc]` + `change` + 幂引理）。待办：

1. 交换引理（从 `pA2B_pow_two` 推，试 `group` 战术）
2. 24 条作用引理逐条证明（数据已全部数值确定）
3. 陪集覆盖 → 满射 `P →* A₅` → 单射 → |P| = 60
4. **#3d**：`icosahedralRep : FDRep ℂ G`（`FDRep.of` 需整个 G 上的 `Representation`，经 `QuotientGroup.kerLift`/`quotientKerEquivOfSurjective` 因子化下降）+ `finrank = 3`
5. **#4/#5/#6**：CharValues.lean 三个 sorry（`icosahedral_simple`、`exists_five_order_char_phi`、`char_values_in_Q5`）

---

## 6. 关键调试经验（已确认的坑与模式）

- **矩阵定义**用 `!![...]`（非 `![]`）；幂展开靠 `change` + `rw [pow_succ]` 链，每层乘法恰好一次 `simp`
- **√5 多项式收尾**：`ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num`；重复 simp 报 "made no progress"
- **呈现群阶**：`PresentedGroup.mk (x^5)` 需显式 `rels`；关系元引理用 `one_of_mem` + `simpa [rels]` 最稳
- **幂引理**：`simpa [orderOf_x] using pow_orderOf_eq_one` 会过化简成 True → 用 `have h := pow_orderOf_eq_one` + `rw [orderOf_x] at h` + `exact h` 或直接 `one_of_mem`
- **存在量化指数**：`∃ k : Fin 5, ... ^ k` 需 `k.val`（Fin 5 非 Nat）；引入用 `use (k : Fin 5)`
- **结合律方向**：右结合形 `x·(y·z)` 要 `rw [← mul_assoc]`（`mul_assoc` 正向只匹配左结合形）
- **G 中子群乘法**的 `congrArg Subtype.val` 深层 whnf 会心跳超时 → 用 `by decide`
- **编译反馈**：`lake build` 吞错误详情；单文件用 `lake env lean A5CharQ5\A5Defs.lean`；日志用 `Out-File -Encoding utf8`

---

## 7. 与三主线（QRH/BSD/RH）的关系

本定理是"可读证明"路线的一块拼图：不追求 43M 行巨无霸，而是把经典有限群论事实（二十面体群、呈现完备性、特征标域）小步形式化，每条引理带数学注释，可直接用人话读通。特征标域 Q(√5) 与结理论、五边形/黄金比结构同源（用户早期"结"理论笔记的收敛点之一）。
