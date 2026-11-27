# BSD 主定理 axiom 闭包审计（weak_BSD_37a1）

日期：**2026-11-27**（现行口径）｜`BSD.Main` import 闭包 = 9 模块、**85 条 axiom**（其中 8 条属 `Main.lean` 本体）｜`weak_BSD_37a1` 端到端闭包实测 = **13 条数学 axiom + 3 条逻辑公理 + 161 条 native_decide 计算信任公理**｜sorry = 0

> 本文件在 2026-11-27 重写。2026-10-06 的旧口径（"库 axiom 16"、"Main 9 + LSeries5 7"、"`mwRank` / `rank_E_Q_ge_one` / `rank_E_Q_le_one` 均为 axiom"）已全部失效：`mwRank` 现为 `def`，两条秩断言现为 theorem，`GrHChain389` 与 `SelmerLayer` 已入库。旧表格的原文摘录保留在 §4（历史沿革），仅供参考，**不得作为当前状态引用**。

## 0. 主定理闭包链（2026-11-27 实测形态）

```
weak_BSD_37a1 : mwRank E/K = analyticRank E/K          （BSD namespace，Main:313 前）
├─ algebraic_rank_K_eq_one（theorem）
│  ├─ twist_decomposition                          [C] rank E(K) = rank E(ℚ) + rank E⁵(ℚ)
│  ├─ rank_E_Q_eq_one（theorem，le_antisymm）
│  │  ├─ rank_E_Q_ge_one（theorem，C6 三件套）
│  │  │  ├─ InfinitePointWitness                   [C] 谓词
│  │  │  ├─ rank_ge_one_of_infinite_point          [C] 自由群含无限阶点 ⟹ 秩 ≥ 1
│  │  │  └─ has_infinite_point_37a1                [C] 数据锚点（#E(𝔽₂)=5、#E(𝔽₃)=7、gcd=1，Count37a1）
│  │  └─ rank_E_Q_le_one（theorem，C7）
│  │     ├─ sel2_order_two_37a1                    [B] |Sel₂(37a1)| = 2
│  │     └─ SelmerLayer.sel2_rank_bound            [C] 2^rank ≤ #Sel₂（K 形参须取 ℚ）
│  └─ rank_E5_Q_eq_zero_of_L_E5_ne_zero            [C] 条件：L(E⁵,1)≠0 ⟹ 秩 0（Kolyvagin）
└─ analytic_rank_K_eq_one（theorem）
   ├─ analytic_rank_K_eq_one_of_LK_prime_ne_zero   [C] ε_K = −1 函数方程
   └─ LK_prime_pos（theorem）
      ├─ Lprime_E1_pos（theorem，B3-min 已删除区间 axiom）
      └─ L_E5_one_pos（theorem）
         ├─ LSeries5.L_E5_series_split             [C] Dokchitser 反射公式 N-截断
         └─ LSeries5.Lambda_E5                     [C] 反射公式形态
```

与 10-06 版的结构差别：`rank_E_Q_ge_one` 不再是一条黑箱，而是"谓词 + 结构 + 数据锚点"三件；`rank_E_Q_le_one` 不再是 2-下降黑箱，而是"Selmer 阶上界 + |Sel₂| 数据锚点"两件；两者都不再出现在自己的闭包里。

## 1. 分模块 axiom 账（2026-11-27 实测，`^\s*axiom ` 计数）

| 模块 | axiom 条数 | 说明 |
|---|---|---|
| `Main.lean` | 8 | 见 §2 表；`mwRank` 已转 def |
| `LSeries5.lean` | 9 | 局部因子 / 反射公式 / 可和性 |
| `LPrime.lean` | 0 | B3-min + ①c 后清零 |
| `Count37a1.lean` | 0 | 2026-11-27 新建，有限域点计数（`native_decide`） |
| `RankTwo389.lean` | 3 | `sel2_rank_bound` 已下沉为别名 |
| `SelmerLayer.lean` | 8 | 2026-11-27 新建（4 对象 + 4 结构） |
| `Sha11_389.lean` | 30 | 2026-11-27 由 34 降至 30 |
| `GrHChain389.lean` | 9 | 3 数值对象 + 2 区间锚点 + 4 断言（环 4 已转 theorem） |
| `EulerSystem.lean` | 18 | 未动；`rank_389a1` 仍在，但 ℚ 侧路径已绕开 |
| **合计（Main 闭包内）** | **85** | 9 模块 |

旁支模块（不在 `BSD.Main` 闭包内，单独记账）：`Positivity/Positivity.lean` 78、`SymmetryFormula4.lean` 25、`ShaFreeLayer.lean` 17、`LSeries5_43.lean` 3。

## 2. Main.lean 的 8 条（现行分类）

| # | axiom | 类别 | 说明 |
|---|---|---|---|
| A1 | `analyticRank` | [A] 口径占位 | 解析秩（mathlib 无自守 L） |
| A2 | `analytic_rank_K_eq_one_of_LK_prime_ne_zero` | [C] 数学钉死 | ε_K = −1 函数方程 + 一阶零点判定 |
| A3 | `InfinitePointWitness` | [A] 谓词占位 | "含无限阶点"的谓词 |
| A4 | `rank_ge_one_of_infinite_point` | [C] 数学钉死 | 自由阿贝尔群含无限阶点 ⟹ 秩 ≥ 1（Mordell–Weil） |
| A5 | `has_infinite_point_37a1` | [B] 数值/计算钉死 | P₀ = (0,0) 无限阶（`Count37a1`：gcd(#E(𝔽₂), #E(𝔽₃)) = gcd(5,7) = 1 ⟹ torsion trivial） |
| A6 | `sel2_order_two_37a1` | [B] 数值钉死 | \|Sel₂(37a1)\| = 2（LMFDB / Magma 一致） |
| A7 | `rank_E5_Q_eq_zero_of_L_E5_ne_zero` | [C] 现代数论 | 条件 axiom：L(E⁵,1)≠0 ⟹ 秩 0（Kolyvagin + BCDT） |
| A8 | `twist_decomposition` | [C] 教科书 | E(K)⊗ℚ ≅ E(ℚ)⊗ℚ ⊕ E⁵(ℚ)⊗ℚ |

已消失的三条：`mwRank`（→ `noncomputable def mwRank := EulerSystem.Rank`）、`rank_E_Q_ge_one`（→ theorem，A3–A5 组装）、`rank_E_Q_le_one`（→ theorem，A6 + `sel2_rank_bound`）。

## 3. `weak_BSD_37a1` 闭包实测（`BSD/_audit_20261127.out`）

| 类别 | 条数 | 名单 |
|---|---|---|
| 数学 axiom | **13** | Main 8（§2）+ `EulerSystem.Rank` + `LSeries5.Lambda_E5` + `LSeries5.L_E5_series_split` + `SelmerLayer.SelPOrder` + `SelmerLayer.sel2_rank_bound` |
| 逻辑公理 | 3 | `propext`、`Classical.choice`、`Quot.sound` |
| 计算信任 | 161 | `aE_bound` 等 `native_decide.ax_*`（只信任具体整数比较的执行，**非数学假设**） |

单点闭包（三条同族，均不含自身）：

| 定理 | 闭包 | 判定 |
|---|---|---|
| `rank_E_Q_ge_one` | `InfinitePointWitness`、`has_infinite_point_37a1`、`rank_ge_one_of_infinite_point`、`EulerSystem.Rank` | 无自身 ⟹ 已降定理 |
| `rank_E_Q_le_one` | `sel2_order_two_37a1`、`EulerSystem.Rank`、`SelmerLayer.SelPOrder`、`SelmerLayer.sel2_rank_bound` | 无自身 ⟹ 已降定理 |
| `sha11_order_one_389` | 见 `_check_g2.out` / `_check_debt.out`；**不含** `EulerSystem.rank_389a1` | 环债已断（24 号） |
| `sha11_one_of_grh_fine_bsd_389` | 3 对象 + 2 区间 + `mellin_tail_bound_389` + `fine_bsd_389` + `sha_square_389` + `sha_order_at_least_one` + `ShaPOrder` | 条件定理（G5） |
| `omega_reg_min_bound_389` | `Omega389`、`Reg389`、`omega_bracket_389`、`reg_bracket_389` | **不含自身** ⟹ 环 4 axiom→theorem |

## 4. 历史沿革（2026-10-06 旧口径，仅存档）

- 当时报"库 axiom 16 = Main 9 + LSeries5 7"，其中 `[A]` 结构占位 4（`analyticRank`、`mwRank`、`GammaUpper`、`ap_E`）、`[B]` 数值钉死 3（`ap_E_values`、`Lprime_E1`、`Lprime_E1_interval`）、`[C]` 数学钉死 9、`[D]` 已消除 2（`coefficient_bound_aE5`、`summable_fE5`）。
- 该表的三处错误已在后续轮次暴露：(i) `Lprime_E1` / `Lprime_E1_interval` 于 10-07 整体删除（B3-min），表内仍列；(ii) `mwRank` 于 11-27 转 def；(iii) `rank_E_Q_ge_one` / `rank_E_Q_le_one` 于 11-27 转 theorem。**旧表的计数与分类不得再用。**

## 5. 风险排序（2026-11-27）

1. **`rank_E5_Q_eq_zero_of_L_E5_ne_zero`（Kolyvagin）**：主定理最深的数论输入，前件由真定理 `L_E5_one_ne_zero` 供给；风险在"引用正确性"，不在数值。
2. **`LSeries5.Lambda_E5` / `L_E5_series_split`**：自守 L 解析延拓 + 反射公式，mathlib 无理论，永久 axiom 风险。
3. **`SelmerLayer` 四条结构**（`sel_dim_eq_rank_add_sha_corank`、`sha_p_descent_order`、`sel_p_order_eq_p_pow_dim`、`sel2_rank_bound`）：标准算术，但 `sel2_rank_bound` 的 `K` 形参**必须取 ℚ**，取大扩域即为假——审计注已写入文件。
4. **`GrHChain389` 的 9 条**：3 数值对象不可定义（只能声明）、2 区间锚点依赖 G3 数值（四源 10⁻¹⁹）、4 断言中精细 BSD 最深。**教训：axiom 不检查可满足性**——10-16 版把 `OmegaReg389` 定义成 0 同时断言 `0.759291598 ≤ Ω·Reg`，整链由 `False` 推出，回执干净但零信息（11-27 已拆，见 `_rh14_zeroside\25_...docx`）。
5. **`EulerSystem.rank_389a1`**：仍在库里，但 `sha11_order_one_389` 已改走 ℚ 侧真证，不再引用它；保留只为旧调用点兼容。

## 6. 结论

- 主定理 `weak_BSD_37a1` 端到端只依赖 **13 条数学 axiom**，其中"数值已钉死"的两条（`has_infinite_point_37a1`、`sel2_order_two_37a1`）都是可复算的有限域/descent 数字，其余 11 条是 mathlib 缺理论式的诚实保留。
- 本轮把两个黑箱（`mwRank`、两条秩断言）换成了"def + theorem + 可复算锚点"，代价是 raw axiom 数在 Main 端 7 → 8（拆黑箱的标准代价，如实记账）。
- 无可 sorry；无假前提（`GrHChain389` 的空壳已清零，并以 `anchor_consistent_389` 钉死前提可满足）。
