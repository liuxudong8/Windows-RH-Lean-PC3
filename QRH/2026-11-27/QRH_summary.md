# QRH 项目总结（攻防 XLII「干到 1」主线 + Lean 形式化）

> 2026-10-27 定稿。数学层 S0–S7.6 已闭环落档 d1；Lean 形式化 Main (L3)(L4) 已落位、2604 jobs 全绿；S7.7 击破清单四连已落档；(L1)(L2) 长线攻坚第一轮已落档 S7.8（真实定义件 + Abel–SW 组装真证 + trivialTerm 收敛件，2604 全绿）。
> 2026-10-29 增量：Core 清单项 `C_MT<4/3` 纯有理链真证确认（sin_lower_five + cos_upper_four + C_MT_lt_four_thirds；√2 全程消去、无积分、无聚合依赖）；真证链 26→29；build_verify_cmt43.txt 增量全绿。
> 2026-10-29 增量②：`prime_weight_bounds` axiom 降为真证定理 `prime_weight_bounds_Khat`（Khat 特化）——Core 增 `abs_sin_div_two_mul_le_half` + `khat_global_bound`（全局一致界 |K̂u| ≤ 1/(√2·|sin(1/√2)|)，用 |sin t| ≤ |t| 绕开 `Khat_abs_le` 分母 |√2±2πu| 零点）；Main 真证四引理（log_succ_sub_le_inv / inv_sqrt_succ_le / inv_sqrt_sq_eq_inv / inv_sqrt_succ_sub_le）→ `prime_weight_bounds_Khat`（M = L·δ + B）→ `prime_sum_bound` 特化 K := Khat（bgs5 前移）；新挂账命名 axiom `fourierCos_Khat`（连接件）+ `khat_lipschitz`（光滑件）；全量 **2704 jobs 绿**（dbg_build.txt），无 warning（清理 6 处历史 unused）。落档 d1 S7.10（中英，audit 0 errors、渲染逐页通过）。
> 2026-10-29 增量③：**(L1) x=1 边界口径闭环（S7.11）**——trivialTerm 在 x=1 为调和型发散（Σ 1/(2ℓ+r) ~ ½Σ 1/ℓ），`landau_explicit_L` 前提由 1 ≤ x 收紧为 1 < x（防假命题陷阱：原宽松前提在 x=1 断言 trivialTerm(1) = −logDeriv(r)，而发散点 ∑' 默认值 0 无数学意义）；新增约定件 `trivialTerm_one_term` + `trivialTerm_one`（真证，simp / tsum_congr）；发散性正式证明（¬ Summable）留可选后续。真证链 +2（31+→33+）；全量 **2704 绿**（dbg_build_x1.txt）。落档 d1 S7.11（中英，audit 0 errors、渲染 3+3 页逐页通过）。
> 2026-10-29 增量④：**arXiv 英文草稿《QRH-arXiv-draft-single-family-pairing-constant-L(s,chi5).docx》（d1\en）六处统一口径，C_MT<4/3 已证首次入稿**——摘要（35+ lemmas / 2704 jobs passing (2026-10-29), including the proved constant bound C_MT < 4/3）、引言贡献 (iii)（同口径）、§3 变分机制段尾（"The bound C_MT < 4/3 is proved in Lean (Section 9; pure rational chain, 2026-10-29)"）、§9 Lean 章节（2704/35+ + C_MT_lt_four_thirds 纯有理链细节：cos 四阶上界 73/96、sin 下界 11/(12√2)−√2/800 在 x₀=1/√2 处 ⟹ cot < 1825/(1097√2) ⟹ C_MT < 2922/2194 < 4/3，无积分层、无聚合依赖；fourierCos Bochner 真定义 + fourierCos_scale 真证入稿）、Conclusion（35+/2704 + C_MT < 4/3）、参考文献 [11]（dbg_build_fourier.txt 2704 jobs green, 2026-10-29）。旧口径（26 lemmas / 2604 jobs / main_l2_full.txt）全文清零。audit --source 对比 0 errors（新增 run 格式继承一致）、render 8 页逐页通过、catalogue 无 TOC 不动作。编辑脚本 s712_work\edit_arxiv_cmt.py（含 add_run_after_last 继承末个 w:r rPr），SOURCE 备份 s712_work\SOURCE_arxiv_draft.docx。
> 2026-10-30 增量⑤：**`f0_sub_feps_L1_bound` 真证出账（axiom → theorem；Core 口径修正，2026-10-30）**——f0 补支撑截断 1_{|x|≤1/2}（原全实轴 cos(√2x)/(√2·sin(1/√2)) 绝对不可积 ∫|f0| = ∞，Bochner 惯例归 0，直接真证空洞；S7.9/S7.11 同款"先修口径再真证"模式），Core 删 f0_continuous、增 `f0_den_abs`（分母模件）/`f0_abs_le`（|f0| ≤ (√2·|sin(1/√2)|)⁻¹）/`f0_measurable`（if 截断 + 闭集 {|x|≤1/2} = Icc 可测 + 连续/常数分支），Core 单编 exit=0；Stage3 证明块 = 7 辅助件（w_eps_nonneg / w_eps_le_one / abs_one_sub_w_le_one / w_eps_continuous / w_eps_eq_one / indicator_Icc_integral / f0_sub_feps_abs_le）+ 主定理：f₀−f_ε = f₀·(1−w_ε) 点界（过渡区外差=0）→ 过渡区 I1∪I2 = [−1/2,−1/2+ε)∪(1/2−ε,1/2] 测度 2ε（indicator_Icc_integral：integral_indicator + setIntegral_const + Real.volume_Icc + toReal_ofReal）→ integral_mono_ae（两侧可积：RHS 走 integrableOn_iff_integrable_of_support_subset + IntegrableOn.congr_fun，LHS 走 aestronglyMeasurable_iff_aemeasurable 桥 + Integrable.mono）→ integral_const_mul + integral_add → ring。**全量 2704 jobs 绿、0 warning**（dbg_build_f0.txt；Core 三处 if_pos/if_neg/mem_setOf_eq 弃用同步清理为 ite_eq_left/ite_eq_right/mem_ofPred_eq）。挂账 axiom −1：Stage3 积分层仅剩 n2_linkage / n3_remainder_uniform / N_L / N_L_lower_bound（数论件）+ pair_const_eps_bias（待 pairConstant 真实定义）。
> 2026-10-30 增量⑥：**`khat_lipschitz` 真证出账（axiom → theorem；S_smooth 奇点延拓修口径，2026-10-30）**——原 axiom 陈述 `∃L, 0≤L ∧ ∀u v, |Khat u − Khat v| ≤ L|u−v|` 在 Khat 原闭式下**为假**（`(sin((√2−2πu)/2)/(√2−2πu) + …)/(√2·sin(1/√2))` 在 u=±√2/(2π) 除零，Lean 惯例取 0，数学延拓应为 1/2）；修口径：`S_smooth x = if x = 0 then 1/2 else sin(x/2)/x`，`Khat u = (S_smooth (√2−2πu) + S_smooth (√2+2πu))/(√2·sin(1/√2))`；**原 axiom khat_lipschitz 已删**。Core §3b 新增 S_smooth 件 ~12 条：均值定理三辅助（abs_cos_sub_one_le_sq_of_nonneg / abs_sin_sub_id_le_cube_of_nonneg / abs_sin_sub_mul_cos_le_sq，`Convex.norm_image_sub_le_of_norm_deriv_le` 全命名实参 (𝕜:=ℝ)(G:=ℝ) 版）、`S_smooth_hasDerivAt_zero`（**夹逼 slope 口径**：hasDerivAt_iff_tendsto_slope + ‖slope‖≤|y|/8 界 + tendsto_of_tendsto_of_tendsto_of_le_of_le + tendsto_zero_iff_norm_tendsto_zero）、`S_smooth_deriv_bound`（|deriv S_smooth| ≤ 1/4，n≠0 走 |sin t − t cos t| ≤ t²）、`S_smooth_lipschitz_1_4`；§3c 新增 khat 件：`khat_hasDerivAt`（商法则域化简：h_eq1 纯 ring 分子重组 + h_eq2 逆元链（`hcc : c⁻¹ = c·c⁻¹^2` 经 pow_two+mul_inv_cancel₀，`h_div` 独立声明后 rw [← inv_pow]）+ 全程 `hdiv : √2·sin(1/√2) ≠ 0` 分母件）、`khat_deriv_bound`（‖deriv Khat u‖ ≤ π/(√2·|sin(1/√2)|)，rw [hd.deriv] + S_smooth_deriv_bound + norm_mul_le 三角）、**`khat_lipschitz` theorem**（L = **π/(√2·|sin(1/√2)|)** ≈ 3.42，Convex.norm_image_sub_le_of_norm_deriv_le 组装 + `simpa [Real.norm_eq_abs, abs_sub_comm]`）。Stage3 `Khat_closed_form` 适配新定义（S_smooth 展开两件 hsa/hsb：unfold + `ite_eq_right hd1/hd2` 后 rw，闭式链其余不动）。**全量 2704 jobs 绿、0 warning**（dbg_build_khat.txt；Core 单编 core_khat10.txt exit=0）。挂账 axiom −1：残余命名 axiom 仅 `fourierCos_Khat`（连接件，定义一致件非本任务范围）+ `bgs5_khat_fourier_supp`（积分层窄支撑）；`prime_weight_bounds_Khat` 的 L 实参已由真证定理给出（M = L·δ + B 全真证）。
> 2026-10-30 增量⑦：**`pair_const_eps_bias` 真证出账（axiom → theorem；N2b 层，2026-10-30）**——三段真证链：`f_eps_abs_le`（|f_ε x| ≤ M，压缩继承 f0_abs_le）/ `abs_tsum_sub_le_tsum_abs`（|Σf−Σg| ≤ Σ|f−g|：hf.tsum_sub hg + norm_tsum_le_tsum_norm，显式 f 命名绕 tsum 隐参）/ `pairConst_sub_pairL1`（pairConstant 展开常数抵消 → 逐项 sq_sub_sq_abs_le + `Summable.tsum_le_tsum` 三参数）→ (2M/N)·Σ'y；积分层「离散配对和 ≤ D·δ·normL1」精确化为新命名 axiom **`pairCount_L1_bound`**（可和性三件打包 + D·N·normL1 界，不做 axiom→axiom 空换名）；组装 C₁ = **4M²D** 口径修正（旧注释 2M·D 漏 L¹ 界常数 2εM 因子）；单编 stage3_pceb11.txt 空 + 全量 lake build QRH 绿（2026-10-30）。
> 2026-10-31 增量⑧（task #74 闭环）：**`pairCount_L1_bound` 真证出账（axiom → theorem；截断零点集口径修正，2026-10-31）**——原 axiom 数学不可证，两硬伤（用户确认方案，项目惯例「先修口径、再真证」）：(i) 原用临界带全零点集 `zerosLChi5`（无限）+ 竖直差带窗口 2πε/logT 内配对无限多 ⟹ Summable 假；修正 `Z_T := zerosLChi5UpTo T := {z ∈ zerosLChi5 | |z.im| ≤ T}`（有限 ⟹ Summable 自动为 Finset 和）；(ii) RHS 归一化由 D·δ·‖g‖₁（δ 非零点数、对 T 不一致）修正为 **D·N_Z(T)·‖g‖₁**（N_Z = 截断零点数，与文档 S7.1 §2 口径一致）。新增数论结构 axiom 两件承载 RvM/计数：`zerosLChi5_bounded_finite`（Z_T 有限）+ `pair_count_bound`（计数 ≤ Dcnt·N_L T，hT0:1<T0）；`pair_const_eps_bias` 组装同步 N:=N_L T、Z:=Z_T、门槛 `1≤T0`→`1<T0`，Bound 仍 = ε。**真证块**（行 763）：hsum/hcnt 有限支撑件（support 包含 + `summable_of_finite_support`）→ 逐项界 hterm（支撑内 |f0−f_eps| ≤ 2M 继承全局界 + 计数 1；支撑外 0 ≤ 2M·0）→ `hg_sum`（`Summable.of_norm_bounded`：逐项 |·| ≤ 三项和，abs_of_nonneg 去嵌套 abs + linarith 结合律）→ hle_sum（`Summable.tsum_le_tsum` 三参数）→ hle2（tsum_mul_left + mul_le_mul_of_nonneg_left）→ hle3（unfold D + hform ring + `le_div_iff₀ hLpos` + ring_nf + le_rfl）→ `exact ⟨hsum, le_trans hle2 hle3⟩`；D = 2M·Dcnt/normL1(f₀−f_ε)，M = (√2|sin(1/√2)|)⁻¹。**v4.34 引理名勘误**：import 修正 `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`（目录拆分，非旧全名）+ 补 `MeasureTheory.Measure.Restrict`；`Continuous.max/min`（无 continuous.max）、`Set.uIoo`（无 intervalIntegral.uIoo）、`MeasureTheory.Measure.restrict_le_self`（namespace Measure 内）、`intervalIntegral.intervalIntegral_pos_of_pos_on`（限定命名空间）、`le_div_iff₀`（非 le_div_iff）、`integral_mono_measure`（3 显式参数；restrict_le_self 方向 = restrict ≤ volume）。N_L/N_L_lower_bound 前移至 N2b 挂钩前（原后部 ~1403–1411 留注释占位）。**单编 stage3_pceb12.txt 空 + 全量 build_qrh_lake.txt 2719 jobs 绿、0 error**（较 2704 增 15 job：新 def/真证件）。残余 axiom 更新：pairCount_L1_bound 已出账（theorem）；新增结构 axiom `zerosLChi5_bounded_finite`/`pair_count_bound` 入残余清单（Stage3 六件：n2_linkage / n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound）。
> 2026-11-23 增量⑩（A 方案，口径搬运）：**`zerosLChi5_bounded_finite` axiom → theorem，残余 axiom 由 6 件降为 5 件**——做法：不碰 `opaque LFun`，改为 `theorem zerosLChi5_bounded_finite (χ : DirichletCharacter ℂ 5) (hL : ∀ z, LFun z = DirichletCharacter.LFunction χ z) (T : ℝ)`，证法 `集合等式 + QRHZeroWindow.finite_zeros_of_eq_LFunction χ LFun hL 0 T`；搬运件来自归档 `DirichletLZerosInWindowFiniteAndPosOrder`（对任意模 q、任意 χ、任意窗口成立），抽为零依赖模块 `OrderPreservingBijection.DirichletLZeroWindow`（7 条 Mathlib 具体 import，7 条定理公理全 `[propext, Classical.choice, Quot.sound]`）。传染面仅 2 个签名（`pairCount_L1_bound`、`pair_const_eps_bias` 各加 `(χ)(hL)`，两个调用点同步）。**实测 `#print axioms`**：`zerosLChi5_bounded_finite` = `[propext, Classical.choice, Quot.sound]`（零 axiom）；`pairCount_L1_bound` / `pair_const_eps_bias` = `[propext, Classical.choice, QRH.N_L, QRH.N_L_lower_bound, QRH.pair_count_bound, Quot.sound]`。全量 `lake build QRH` **3624 jobs 绿、0 error**（2719→3624 的增量系新增 `DirichletLZeroWindow` 的 Mathlib 依赖闭包，非语句膨胀）。代价：债务形态由「一条平坦假设」变为「一条同一性假设 `hL` + 已证定理」，`hL` 本身待 B 方案（`LFun := DirichletCharacter.LFunction chi5Dirichlet` 真定义，须与 `lfun_series` 口径同时改）。
> 2026-11-23 增量⑪（假 axiom 撤除，B 方案前置）：**`S7_1_Main.lean:76 axiom lfun_dirichlet_series` 已删**——它断言 `0 < s.re` 时 `LFun s = Σ χ₅(n) n^{-s}`，但原始 Dirichlet 级数只在 `re s > 1` 收敛，故该命题在 `0 < re s ≤ 1` 为**假**；且全库 **0 处代码引用**（仅文档提及），删除不动任何证明。全量 `lake build QRH` 仍 **3624 jobs / 0 error**。留档注释原位保留（`:75`），B 方案时以真定理形式回归：`1 < s.re → LFun s = LSeries χ₅ s`（mathlib `DirichletCharacter.LFunction_eq_LSeries` 直接给）。
> 2026-11-23 增量⑫（B 方案主体落地：`opaque` → mathlib 真定义）：
> （i）`S7_1_Main.lean:62/66` 两处 `opaque` 换成真定义——`chi5 : ℕ → ℝ := fun n => (OrderPreservingBijection.chi5Dirichlet (n : ZMod 5)).re`；`LFun : ℂ → ℂ := fun z => DirichletCharacter.LFunction OrderPreservingBijection.chi5Dirichlet z`（mathlib `DirichletContinuation.lean:61`，Hurwitz ζ 线性组合的解析延拓）；`S7_1_Main` 新增 `import OrderPreservingBijection.stage_3` + `import Mathlib.NumberTheory.LSeries.DirichletContinuation`（无 import 环：stage_3 侧只 import Mathlib 与 OPM 件）。
> （ii）Stage3 三处签名去掉 `(χ : DirichletCharacter ℂ 5) (hL : ∀ z, LFun z = LFunction χ z)`：`zerosLChi5_bounded_finite (T : ℝ)`、`pairCount_L1_bound (T0 ε …)`、`pair_const_eps_bias (T0 ε …)`；同一性由 `rfl` 自动给出，故 `zerosLChi5_bounded_finite` 由「同一性假设 + 已证定理」升级为**无条件定理**。
> （iii）实测 `#print axioms`：`zerosLChi5_bounded_finite` = `[propext, Classical.choice, Quot.sound]`（**零 axiom**）；`pairCount_L1_bound` / `pair_const_eps_bias` = 3 基础 + `N_L`、`N_L_lower_bound`、`pair_count_bound`；`s71_main` = 3 基础 + `bgs3_pair_expansion`、`bgs5_khat_fourier_supp`。
> （iv）全量 `lake build QRH`：**3834 jobs / 0 error**（jobs 从 3624 增至 3834，因 Main 现在拉入 `OrderPreservingBijection.stage_3` 闭包）。
> （v）唯一残余口径洞：`lfun_conj_symm`（`:87`，真命题、仍 axiom；mathlib 无 `LFunction_conj`，须自证 `1<s.re` 上系数实 ⟹ 逐项共轭 + `LFunction` 全纯（`χ₅ ≠ 1`）唯一性延拓）。
> （vi）摩擦一处：import stage_3 后 `sqrt` 在 `S7_1_Main:525/529` 变歧义（`√2` 记号与 `Real.sqrt` 冲突），改为 `Real.sqrt` 全限定解决。
> 2026-11-23 增量⑬（`vonMangoldt` 真定义）：`S7_1_Main.lean:115 opaque vonMangoldt : ℕ → ℝ` → `noncomputable def vonMangoldt := fun n => ArithmeticFunction.vonMangoldt n`（mathlib `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:65`，`Λ n = if IsPrimePow n then Real.log (minFac n) else 0`）；新增 `import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`。全量 `lake build QRH` **3834 jobs / 0 error**，公理集不变（`zerosLChi5_bounded_finite` 仍零 axiom；`s71_main` 仍只 `bgs3_pair_expansion` + `bgs5_khat_fourier_supp`）。收益是**工具面**：Λ 的 mathlib 引理接入（`vonMangoldt_apply`、`vonMangoldt_nonneg`、`vonMangoldt_apply_prime`、`vonMangoldt_ne_zero_iff`、`vonMangoldt_le_log`、`vonMangoldt_sum`、`log_mul_moebius_eq_vonMangoldt`），为 `siegel_walfisz_chi5` 的 PNT-in-AP 攻坚提供可证接口。
> （摩擦一处：模块路径不是 `Mathlib.NumberTheory.VonMangoldt`，而是 `Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`。）
> 2026-11-23 增量⑭（`logDerivTerm` 真定义）：`S7_1_Main.lean:138 opaque logDerivTerm (r : ℝ) : ℝ` → `noncomputable def logDerivTerm (r : ℝ) : ℝ := (logDeriv LFun (r : ℂ)).re`（mathlib `logDeriv f := deriv f / f`，`Mathlib/Analysis/Calculus/LogDeriv.lean:32`）；新增 `import Mathlib.Analysis.Calculus.LogDeriv`。全量 **3834 jobs / 0 error**，公理集不变（`_b_ax.txt` 与增量⑫⑬逐字一致）。口径边界：`.re` 投影的严格合法性依赖 `lfun_conj_symm`（实点处 L、L′ 实值），故本定义**不消解**该 axiom，而是把它变成「口径前提」；同时 `offCriticalError` / `offcritLow` / `offcritHigh` / `offcritSum` 仍为抽象算子（BGS 引理 4 机制，非 mathlib 对象）。
> 2026-11-23 增量⑮（`lfun_conj_symm` 第 ① 步：χ₅ 实数性，**真证**）：新模块 `OrderPreservingBijection/Chi5Real.lean`，4 条定理全部公理干净（`[propext, Classical.choice, Quot.sound]`）：`chi5UnitFun_eq_one_or_neg_one`（`chi5UnitFun` 三分支 ⟹ 取值 ∈ {1,-1}）、`chi5Dirichlet_eq_unit`（单位点 `χ₅ = chi5UnitFun`，`MulChar.ofUnitHom_coe` + `IsUnit.unit` 的可定义相等）、`chi5Dirichlet_apply_im_zero`（全 `x : ZMod 5` 虚部 0：单位点 ±1、非单位点 0）、`chi5Dirichlet_eq_re`（`χ₅(n) = (χ₅(n)).re`）。QRH 侧加接口自检 `chi5_eq_chi5Dirichlet : (chi5 n : ℂ) = chi5Dirichlet ↑n`（证明 `chi5` 的 `.re` 投影无信息损失）。`S7_1_Main` 新增 `import OrderPreservingBijection.Chi5Real`；全量 **3835 jobs / 0 error**。口径变化：`lfun_conj_symm` 三段中的第 ① 段（系数实）**已从「待证」变为「已证」**，该 axiom 本身仍在，但降为「两步可攻」。
> 2026-11-23 增量⑯（`lfun_conj_symm` 第 ② 步：收敛半平面共轭，**真证**）：新模块 `OrderPreservingBijection/LSeriesConj.lean`，4 层定理全部公理干净（`[propext, Classical.choice, Quot.sound]`）：`conj_eq_self_of_im_eq_zero`、`term_conj_of_real_coeff`（`ℂ.cpow_conj` + `natCast_arg = 0 ≠ π`）、`LSeries_conj_of_real_coeff`（`Complex.conj_tsum` 换序，**无条件成立**）、`LFunction_conj_of_real_coeff`（`1 < re s` 上 `LFunction χ (conj s) = conj (LFunction χ s)`，经 `LFunction_eq_LSeries`）。QRH 侧落成定理 `lfun_conj_symm_of_one_lt_re (z) (hz : 1 < z.re)`；原 `axiom lfun_conj_symm` **保留但负担缩小**至 `re z ≤ 1`（`zerosLChi5` 恰在 `0<re<1` 带内，故 `zerosLChi5_conj_closed` 仍未受益——不夸大）。全量 **3836 jobs / 0 error**。
> 2026-11-23 增量⑰（`lfun_conj_symm` 第 ③ 步前置·1：χ₅ 非平凡 + 全纯，**真证**）：`Chi5Real.lean` 增 3 条公理干净的定理——`chi5Dirichlet_two`（`χ₅(2) = -1`，走单位 `u = ⟨2,3⟩` + `chi5UnitFun_val` + `chi5 2 = -1`）、`chi5Dirichlet_ne_one`（`χ₅ ≠ 1`，用 `MulChar.one_apply` 与 `2` 为单位撞出 `1 = -1`）、`differentiable_LFunction_chi5`（`Differentiable ℂ (LFunction χ₅)`，由 `differentiable_LFunction` + 非平凡性直接落地——这是解析延拓唯一性在 `s = 1` 处的前提）。全量 **3836 jobs / 0 error**。摩擦：`Units ℂ` 的 `DecidableEq` 是 classical 的，`decide` 卡在 `Classical.choice`，必须改走「先强转到 ℂ（`chi5UnitFun_val`）、再算 ℤ 值」的路径；旧 `if_neg` 已废弃（改用 `simp` 收口）。
> 口径基准（2026-11-23 增量㉛ 终审，**取代旧行「7/8 为既定目标」**）：**当前封顶 = 0.6725 = 2 − C_MT**（C_MT = 1.3274992963）；7/8（0.875，等价于要求 C ≤ 1.125）在受证类（2λ ≤ 1）内**已被 CCLM Cor.14 定理排除，不是待办目标**（缺口 15%，成因见增量㉛）。31/32 已于更早被否。7/8 只能在三条越墙路下作远期目标：① α > 1（PPC / 强 Montgomery，即 S6 的 (H2′_λ) 超支撑）；② 换非二次矩类泛函（Remark 3.3：Claude 的矩阵路线与 Lamzouri 同归 Montgomery–Taylor 极值问题，换装不换核）；③ 引入类外信息（素数侧 / BGS 余项 —— 正是 QRH 的入口）。**A 是数据而非定理；「证到 1」≠ 接近 RH（统计口径 vs 实际描述），且「证到 1」同样要越墙**——1 也低于 1.3275，它不是受证类内的极限。

## 1. 项目定位

目标：证明 L(s, χ₅) 单族配对常数 A(λ) → 1。这是 QRH（拟随机假设）常数机制攻坚的唯一现实通道：
QRH 常数 0.6725 → 7/8 需要 A ≤ 1.125。A→1 远强于 A ≤ 1.125，故「干到 1」一次性打通 7/8。
2026-11-23 重算后**先撤数**：三角核的 C = 1.1564940 是「ρ₂ 积分泛函」的合法值，但「常数 2 − C」这个减法只对「密度泛函」成立，两者拼出来的 0.8435060 已撤回（见增量㉘）；按密度泛函，Γ 给出的常数是 **2/3 = 0.66667 < 0.6725**。

**㉚ 再进一步（同日）**：这两个泛函**本身都不是 A 的泛函**——S6/Lamzouri 的核是 **K = f̂**（密度的余弦变换，∫f = 1、K(0) = 1、支撑无限、按 1/u 衰减），不是 f\\*f（自相关，支撑 [−1,1]、在 ±1 归零）。故 1.1564940 / 4/3 / μ₁ = 0.6755169 全部退为「别的泛函里的数值」，不进论证链。按真泛函（已用 f₀ 校准到 S6 实测 2% 内），**7/8 只需 λ_eff ≈ 1.13–1.15**，而非此前估的 2.0363。

**㉛ 同日第三次核正（拿到原文后）**：这条「λ_eff ≈ 1.13」也撤回。Lamzouri Lemma 3.1 给的是**恒等式**（Σ/N = C_η + O(1/√logT)），不是界；C_η = Q(0) + 2∫₀¹αQ(α)dα 只在 2λ ≤ 1 成立，且这类内的极小值 = C_MT = 1.3274993 已由 CCLM Cor.14 封顶。故 7/8（需 C ≤ 1.125）在受证类里**被定理排除**，不是「门槛还没算准」。详见增量㉛。

**㉜ 同日第四次核正（数值侧收口）**：① ㉛ 的「实测与定理差 12%」已钉死——**截断不是元凶**（H = 40 → 400 只差 0.0016），**δ 口径是主因**（S6 用的 logT/2π 比真实间距密度 log(T/2π)/2π 大 15.6%，压掉 27% 的超出部分）；修正后 A 饱和 **1.3078**，与 C_MT = 1.3275 差 **1.5%**（残差为有限 T 效应，本机表到分辨极限）。② 顺手拿到 **C_η = 1 + ∫_{-∞}^{∞}(1 − sinc²πu)·K(u)²du**（K = f̂）这条**初等 Fourier 恒等式**（第 1 步就是已机检的 A4）⟹ **「ρ₂ = 1 − sinc² 是猜想」这句话回收**：ρ₂ 在这里不是零点分布的猜想，而是恒等式的核；λ > ½ 失效的是 C_η 本身，不是 ρ₂。详见增量㉜。

## 2. 判定链

- 配对常数（**S6/代码原口径，2026-11-23 经 `xlii_s6_lambda.py` 原文核正**）：A(K) = 1 + (Σ_{Δ>0} K(δΔ)²)/N_Z，δ = logT/(2π)；**K = f̂，即密度 f 的余弦变换（∫f = 1 ⟹ K(0) = 1）**，f 的支撑 supp f ⊂ (−λ,λ)；配对和取双向、截断 half = 40（归一单位）。δ 是平均间距的倒数，u = δΔ 已是归一间距，**不存在额外的 1/δ**。【**㉜ 口径警示**：δ 的物理值是 `log(T/2π)/(2π)`（RvM），S6 脚本第 105 行的 `logT/2π` 在 T = 8×10⁵ 处比它大 **15.6%**（比 1.1564）⟹ 一切与真实零点对表的计算必须用 δ_loc，否则系统性压低 27% 的超出部分。`pairConstant` 的 δ 是参数，代码语义不受影响。】
- 常数机制（**增量㉛ 改写：不是「界」，是恒等式**）：C_η = Q(0) + 2∫₀¹ α Q(α)dα，Q = f\\*f，f = η² ≥ 0、∫f = 1、supp f ⊂ (−λ,λ)（Lamzouri Lemma 3.1/3.2，BGS Lemma 5）。它把配对和**钉死**，只在 2λ ≤ 1（supp Q ⊂ [−1,1]，Montgomery α ≤ 1 段）成立。**计数口径（㉛ 更正，勿再混）**：S6 的 `pair_hist`（脚本 63–74 行）对每个零点取 `z−half … z+half` **两侧**邻点、只滤掉自身 ⟹ 每个无序对被记两次 ⟹ **有序对**，故 **A_s6 ≡ C_η，S6 侧没有换算因子**；只有连续模型（ρ₂ 偶、只积 u>0 半边）才是单边，换算为 **C = 2A_model − 1**（锚点：flat 模型 1.1667 ⟹ 1.3333 = 4/3 精确 ✓；f₀ 模型 1.162882 ⟹ 1.325764，对 1.3275 差 0.13% ✓）。类内极小 = C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963，由 f₀ 取得，⟹ 2 − C_MT = 0.6725007 是**封顶**（CCLM Cor.14），不是我们估的界。
- **作废（增量㉚）**：㉗/㉘/㉙ 的 F1（K = f\\*f 的 ρ₂ 积分）与 F2（2 − ∫(f\\*f)·Γ）**都不是 A 的泛函**，差别在核形状：f̂ 支撑无限、按 1/u 衰减（配对和靠这个尾巴才非零）；f\\*f 支撑有限 [−1,1]、K(±1) = 0（「λ_eff = 1 处配对和退化为 0」是我们口径造出来的假现象）。故 C_A = 1.1564940、4/3、μ₁ = 0.6755169434、λ_eff\\* = 2.0363 全部退为「F2 泛函内的数值」，**不进论证链**。
- **收回（增量㉛，两条）**：① **λ_eff\* ≈ 1.124–1.150**（GUE/ρ₂ 模型 A = 1 + ∫₀^∞ρ₂|f̂|²du，单边计数）——定理口径下 7/8 ⟺ C ≤ 1.125 < 1.3275，**落在受证类极小值之下，属不可达区，不是「没算准」**；② **μ₁ = 0.6755169434**（㉙）——它解的是「max⟨f\\*f,Γ⟩ / ‖f‖₂², supp ⊂ [−1/2,1/2]」，约束错成 ‖f‖₂ = 1，而 C_η 的合法约束是 ∫f = 1、f ≥ 0；cos(2v₁x) 按 ∫f = 1 归一后给 C_η = 1.3290640 > 1.3274993，CCLM 的极小仍由 f₀ 取得（**不是我们赢 0.003，是解错了问题**）。
- **7/8 判决（增量㉛）**：受证类（2λ ≤ 1）内 C_η ≥ 1.3275，而 7/8 要 C ≤ 1.125，**缺口 15% —— 定理级排除**。越墙三条路：α > 1（PPC / 强 Montgomery，即 S6 的 (H2′_λ) 超支撑）、换非二次矩类泛函（Remark 3.3：Claude 矩阵路线与 Lamzouri 同归 Montgomery–Taylor 极值问题，换装不换核）、类外信息（素数侧 / BGS 余项 = QRH 入口）。另撤一条误判：「λ 增大就能救」不成立——λ 增大 K 变窄、计入的对数变少，C 反向趋 1（界退化为空话），二次矩强度在 λ = 1/2 取极大（此段为同机制外推，**属推断**，λ > 1/2 无定理）。
- 定理 S7.1（L 版 BGS 型配对公式，弱实部假设下）：A_L(K) ≤ C_MT + O(ε) + o(1)。
- A ≤ 1.125 ⟺ 7/8 成立（**A_s6 ≡ C_η，同一门槛，无因子 2**）；A → 1 是平凡极限（Σ/N → 0 只说明界退化为空话，不给信息）。**刻度只剩一个**：C_η（定理口径）；连续模型值要乘 2 减 1 才回到它。

- 现阶段数值：Fejer 窄核 λ→0 极限 A → 1.0079（T = 6×10⁵）；窄核专项推进后 A ≈ 0.990；5 子区间漂移 ≤ 0.005。

## 3. 数学主线（攻防 XLII S0–S7.6，d1 已落档）

| 阶段 | 内容 | 判定 |
|---|---|---|
| S0 | 全尺度 GUE 配对与在线比例 1−o(1) 数值定向；口径修正与超 GUE 排斥 | 生死门：A→1 在数值上可见 |
| S1a | Parseval 归因：δF/δR 分解与核依赖 | 配对常数残差结构归因 |
| S1b | λ(T) 构造与核依赖常数 p 的量化（定理骨架） | 干到 1 的定理框架 |
| S2(i) | Weil 显式公式实部口径注入敏感性（与 S1 左尾威胁闭合链） | 威胁窗收窄 |
| S2(ii) | 跨 T 衰减律判别（配对常数误差律） | S1b 速率标度钉死 |
| S3 | Δ 常数指纹排除交叉验证（同虚部成对注入爆炸响应） | 威胁排除 |
| S4 | 正向构造：窄核实测与配对常数残差结构 | λ(T) 构造数值定锚 |
| S5 | ε 定理级控制：跨族 f(0) 形态实测与并集配对公式无条件化构造 | 并集公式无条件化 |
| S6 | λ_eff ≤ 1 卡点解除：λ ≤ 1/2 最优核族的 0.6725 严格化判定 | 唯一硬卡点解决 |
| S7 | Yildirim 方法移植闭路：L(s,χ₅) 单族 BGS 型配对公式存在性判定 | H2 闭路 |
| S7.1 | 形式化证明 Lean 落地（Yildirim 公式 (7) L 版展开 + BGS 引理 3–5 逐条移植） | 见 §5 |
| S7.2 | 数值件 F：超支撑素数项可忽略性实测 | S(X) = O(√X·poly(log X)) |
| S7.3 | 骨头 1（N1）：BGS 引理 5 超支撑推广（缩放自同构） | A→1 路径 |
| S7.4 | 骨头 2（N2）：ε–λ 联动（正则化撑宽与有效核宽标度律） | 撑宽缺口闭合 |
| S7.5 | 骨头 3（N3）：离线项一致版本（BGS 余项跨 λ 一致） | 跨 λ 一致性 |
| S7.6 | SW 常数显式化：L(s,χ₅) 素数项显式界 (C,c) | 常数显式 |
| S7.7 | 击破清单四连：BGS 引理 3–5 移植（Main）+ N1/L1 真证（Stage3）+ BGS 引理 4 T^{3/8} 切割链（Main）+ 落档 | (L3)(L4) 落位 |

## 4. 三硬骨头与 SW 常数（推 1 断层闭合）

「推 1」撞上的理论断层：XLII 路线要求 λ_eff(T) = (logT)^q → ∞（核越来越窄、谱支撑无限扩大），而 S7 闭路只覆盖 λ ≤ 1/2（BGS 引理 5 硬条件）。λ → ∞ 时实空间核宽 a → 0，差型配对中 ĥK(δ·log p) 支撑变宽，素数项 S(X) 可能失去频域窄支撑保护。三个硬骨头：

- **N1（BGS 引理 5 超支撑推广）**：缩放自同构 scaleKernel a r 支撑保持；λ→∞ 超支撑下素数项仍被 χ₅ 振荡抵消，A→1 路径打通。
- **N2（ε–λ 联动）**：λ = (logT)^q、a = (logT)^{−q}、ε = c·(logT)^{−q} ⟹ 偏差 O((logT)^{−q})——正则化撑宽与有效核宽联动。
- **N3（离线项一致版本）**：BGS 余项 O(T√logT) 对 supp⊂[−1,1] 一切核一致（外层 ∃R 对 K 一致）。
- **SW 常数显式化（S7.6）**：Siegel–Walfisz 素数项界 |Σ_{n≤x} Λ(n)χ₅(n)| ≤ C·x·e^{−c√log x}，理论 c = 1/√R₀ ≈ 0.3954（Kadiri R₀ = 6.3970）；实测 C_obs = 1.70e−3 另记；L(1,χ₅) = 0.430409 > 0；β ≥ 0.9029。

数值件 F 实测：S(X) = Σ_{p≤X} Λ(n)χ₅(p)p^{−1/2}·K̂_a(δ·log p) = O(√X·poly(log X))，相对 N_L ~ (X/2π)·logX 为 o(1)，**无需** e^{−c√logX} 指数级；|S_a| ≈ 2.05 有界收敛（强于理论上界），|S_a|/N_L 单调衰减至 1e−8（X = 10⁸）。

## 5. Lean 形式化状态（C:\proj2\QRH，mathlib v4.34.0-rc2）

构建：`lake build QRH` **2604 jobs 全绿**（exit=0；2026-10-27，build_qrh_l4b.txt）；Windows 侧 mathlib 聚合 Mathlib.olean 未生成，仅具体模块 import。**架构（2026-10-27）**：为打破 import 环（Stage3⇄Main），fourierCos 与 normL1 迁至 Core 新增 4b 节，依赖链 Core→Main→Stage3 单向；Core 增 import `MeasureTheory.Measure.Haar.NormedSpace`（积分变量替换引理系，Bochner 无条件）。

**误差界宏（弃 Asymptotics.IsBigO 与 ε–N）**：`Bound C T0 err f := 0≤C ∧ ∀T≥T0, |err T| ≤ C·f T`；`BoundBall C δ err f := 0≤C ∧ ∀|x|≤δ, |err x| ≤ C·f x`。

**真证链（2026-10-30 现状，38+ 件）**：

- Core（S7_1_Core.lean）：`sin_inv_sqrt2_ne_zero`（分母良定义）、`Khat_neg`（偶性）、`Khat_zero`（K̂(0)=1，sin/x 极限延拓）、`Khat_abs_le`（频域衰减三角不等式界）、**`f0_den_abs`/`f0_abs_le`/`f0_measurable`（f0 支撑截断 [−1/2,1/2] 的分母模件/全局界件/可测件，2026-10-30 增量⑤；删 f0_continuous——截断后 ±1/2 处跳跃不连续）**；**`normL1`（Bochner 积分真定义 ‖f‖₁=∫|f|，axiom 降级）**；**`sin_lower_five`/`cos_upper_four`/`C_MT_lt_four_thirds`（C_MT<4/3 纯有理链：cos 四阶上界 73/96 经 cos x=1−2sin²(x/2)+平方单调自证，sin 五阶损失并入，√2 消去，无积分依赖）**；**`abs_sin_div_two_mul_le_half`/`khat_global_bound`（S7.10，2026-10-29：|sin t/(2t)| ≤ 1/2（|sin t| ≤ |t|，t=0 分支 subst）→ 全局一致界 |K̂u| ≤ 1/(√2·|sin(1/√2)|)——`Khat_abs_le` 分母 |√2±2πu| 在 u=±√2/(2π) 为零、非全局界，故换道）**；**§3b S_smooth 件（2026-10-30 增量⑥，~12 条）**：`S_smooth`（if 延拓 def：0 处 1/2，否则 sin(x/2)/x）、`S_smooth_hasDerivAt` / `S_smooth_hasDerivAt_zero`（夹逼 slope 口径：hasDerivAt_iff_tendsto_slope + ‖slope S_smooth 0 y‖ ≤ |y|/8（unfold slope + rw [sub_zero] + smul_eq_mul + mul_comm + rfl，不用 ring）+ hconv 上下界（tendsto_const_nhds 须 term 模式带完整类型标注）+ tendsto_zero_iff_norm_tendsto_zero.mpr + inf_le_left 降 𝓝Within→𝓝）、`S_smooth_deriv_bound`（|deriv S_smooth| ≤ 1/4：0 处 0，n≠0 走 |sin t − t cos t| ≤ t² 均值定理）、`S_smooth_lipschitz_1_4`（Convex.norm_image_sub_le_of_norm_deriv_le）、均值定理三辅助 `abs_cos_sub_one_le_sq_of_nonneg` / `abs_sin_sub_id_le_cube_of_nonneg` / `abs_sin_sub_mul_cos_le_sq`；**§3c khat 件（2026-10-30 增量⑥）**：`khat_hasDerivAt`（商法则域化简四段：h_eq1 纯 ring 分子重组 2π(d2−d1)=d1·(−2π)+d2·(2π) + h_eq2 逆元链（hcc : c⁻¹ = c·c⁻¹^2 经 pow_two+mul_inv_cancel₀+one_mul；h_div 独立声明 `(f'·c)/c² = (f'·c)·c⁻¹^2` 后 rw [← inv_pow]——主目标直接 rw 会因 RHS 仍是 `/c²` 表示失败）+ rw [h_eq1, h_eq2] + exact hd）、`khat_deriv_bound`（‖deriv Khat u‖ ≤ π/(√2·|sin(1/√2)|)：rw [hd.deriv] + hpos + hnum ≤ π）、**`khat_lipschitz` theorem（L = π/(√2·|sin(1/√2)|) ≈ 3.42：Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℝ)(G:=ℝ) 全命名 + `simpa [Real.norm_eq_abs, abs_sub_comm]`）**。
- Stage3（S7_1_Stage3.lean）：`scaleKernel_support`（N1 支撑保持）、`f_eps_support`（N2 支撑 [−1/2,1/2]）、`Khat_a_even`（一阶校正恒零）、`sum_abel`（Abel 求和归纳）、`khat_second_order_bound`（K̂ 二阶一致界真证，2026-10-26 迁入替换 axiom）、**`n1_diag_invariant`**（r̂_a(0)=r̂(0)，z=0 取点真证）、**`n1_offdiag_scale_eq`**（K̂_a(2δ)²=r̂(2aδ)²，两层 congr 1 真证）、**`n1_offdiag_vanishes`**（结构件真证：scale_eq 重写 + 频域衰减件 |r̂(2aδ)|²≤a²C 假设闭合）、**`scaleKernel_L1_invariant`**（abs_mul + integral_const_mul + integral_comp_inv_mul_left + field_simp，Haar 变量替换链）、**`fourierCos_scale`**（**真证，2026-10-29**：fourierCos 本体 axiom→Bochner 真定义后，四段 calc——integral_const_mul 提 1/a → div_eq_inv_mul 重构 x/a=a⁻¹·x → Measure.integral_comp_inv_mul_left Haar 变量替换（全空间、无正则性前提，任意 r 成立）→ cos 参数 ring + field_simp 消 |a|；**推翻旧判断"需 IntervalIntegral"**——v4.34 Bochner 重构至 Integral/Bochner/ 子目录，缩放律无需聚合，n1_diag_invariant/n1_offdiag_scale_eq 使用点无损）、**`f0_sub_feps_L1_bound` 证明块（axiom → theorem，2026-10-30 增量⑤）**：7 辅助件 w_eps_nonneg / w_eps_le_one / abs_one_sub_w_le_one / w_eps_continuous / w_eps_eq_one（max/min 截断性质 + 连续 + 平区恒 1）/ indicator_Icc_integral（∫1_{Icc a b} = b−a：integral_indicator + setIntegral_const + Real.volume_Icc + toReal_ofReal）/ f0_sub_feps_abs_le（点界：f₀−f_ε = f₀·(1−w_ε)，过渡区 |x|∈(1/2−ε,1/2] 内 |f₀| ≤ C 且 |1−w_ε| ≤ 1，I1/I2 指示函数承载体；区外差=0）→ 主定理（normL1 展开 → hpoint 点界 → RHS 可积（support_indicator + integrableOn_iff_integrable_of_support_subset + IntegrableOn.congr_fun + integrableOn_const(C:=1)）+ LHS 可积（f0_measurable.mul/sub + w_eps_continuous.measurable → aestronglyMeasurable_iff_aemeasurable + measurable_norm.comp → Integrable.mono）→ integral_mono_ae → integral_const_mul + integral_add → 体积 2ε（indicator_Icc_integral 两端）→ ring）、**`pair_const_eps_bias` 证明块（axiom → theorem，2026-10-30 增量⑦，N2b 层）**：三段真证链——`f_eps_abs_le`（|f_ε x| ≤ M，f_ε = f₀·w_ε 压缩，全局界继承 f0_abs_le）、`abs_tsum_sub_le_tsum_abs`（|Σf−Σg| ≤ Σ|f−g|：have hsub = (hf.tsum_sub hg).symm（v4.34 点式 protected）→ simpa [hsub, Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := f−g) hfg——**无 calc、显式 f 命名绕开 tsum 隐参 isDefEq/whnf 爆炸**）、`pairConst_sub_pairL1`（核心归约：pairConstant 展开常数 1 抵消 → |Σx2−Σx0|/N ≤ Σ|x2−x0|/N（逐项 sq_sub_sq_abs_le + 全局 2M 界：hterm 显式逐项不等式 + `Summable.tsum_le_tsum` 三参数 (h)(hf)(hg)——v4.34 需 f 可和第三参数）→ (2M/N)·Σ'y（tsum_mul_left rw 无参））；可和性链 `Summable.of_norm_bounded`（hybd/hx2bd/hx0bd 自写 |·| 逐项界 + simpa [Real.norm_eq_abs] 转换；let a + rw [← ha] 消 ℂ.im 线性 linarith 死点；sq 界 rw [← sq_abs, pow_two] 替换 simpa）→ 积分层「离散配对和 ≤ D·δ·normL1」精确化为新命名 axiom **`pairCount_L1_bound`**（可和性三件打包 + D·N·normL1 界，D 对数配对密度——不做 axiom→axiom 空换名）；**`pairCount_L1_bound` 已于 2026-10-31 真证出账（增量⑧：截断零点集 Z_T:=zerosLChi5UpTo T 修口径 + 归一化 D·N_Z(T) + 结构 axiom zerosLChi5_bounded_finite/pair_count_bound，全真证块行 763，见头注）**；组装 C₁ = **4M²D**（旧注释 2M·D 漏 L¹ 界常数 2εM 因子已修），calc 链 = pairConst_sub → pairCount 挂钩（simpa [δ] 首步对齐）→ f0_sub_feps_L1_bound → ring；**单编 stage3_pceb11.txt 空 + 全量 lake build QRH 绿（2026-10-30）**；2026-10-31 口径同步后单编 stage3_pceb12.txt 空 + 全量 build_qrh_lake.txt 2719 绿（0 error）。
- Main（S7_1_Main.lean）：**`Khat_admissible`**（K(0)=1 真证 Khat_zero + 频域支撑件）、**`pair_sum_expansion`**（由大 axiom 降为 bgs3_pair_expansion 组装定理）、**`offcritical_small`**（由 axiom 降为 bgs4_offcrit_split/low/high 组装真证，R=R₁+R₂）、`s71_main` 组装真证（2026-10-27，接实参 Khat_admissible）；**(L2) 区（2026-10-27 晚）**：`sum_abel_partial`（Icc 口径部分和版 Abel，hIcc' = insert N 分解真证）、`prime_sum_bound`（量子项组装真证，C = c·M·(C₂+C₃)）；**(S7.10 prime_weight_bounds 降定理，2026-10-29)**：`log_succ_sub_le_inv`（|log(n+1)−log n| ≤ 1/n）、`inv_sqrt_succ_le`（(√(n+1))⁻¹ ≤ (√n)⁻¹）、`inv_sqrt_sq_eq_inv`（C·C = n⁻¹）、`inv_sqrt_succ_sub_le`（|A−C| ≤ C³，有理化 √(n+1)−√n = 1/(√(n+1)+√n)）→ **`prime_weight_bounds_Khat`**（theorem：有界 |b_n| ≤ M·(√n)⁻¹ + 平滑 |Δb_n| ≤ M·C³，M = L·δ + B，L 来自 `khat_lipschitz`、B 来自 `khat_global_bound`）→ **`prime_sum_bound` 特化 K := Khat**（签名去 K/hKs、体内 rcases prime_weight_bounds_Khat δ hδ、`bgs5_khat_fourier_supp` 前移到 primeSum 后）；**(L1) 区**：`primePowerSum_half_eq_sqrt`（n^{−1/2} = (√n)⁻¹）、`primePowerSum_half`（r=1/2 展开，衔接 primeSum K≡1 特例）、`trivialTerm_term_nonneg`、`trivialTerm_term_le`、`trivialTerm_summable`（x>1、r>0 收敛：rpow 分解 + inv 界 + 几何级数比较）。

**khat_second_order_bound 真证链**（BoundBall 1 (1/24)）：K̂(u) 乘形式闭式 Khat_closed_form = [cos m − √2·m·cotR·sin m]/(1 − 2m²)，m = πu；|u| ≤ 1/24、π < 16/5 ⟹ |m| ≤ 2/15 ⟹ m² ≤ 4/225 ⟹ 分母 1−2m² ≥ 217/225 > 0；分子拆分 N = m²(3/2 − √2·cotR) + cos 二阶余项 − √2·m·cotR·(sin 一阶余项)；cos/sin 余项用 Real.cos_bound/sin_bound、c0_bound（|3/2 − √2·cotR| ≤ 9/50，cotR ∈ [1, 237/200]）；拼接得 |K̂−1| ≤ (194/1000)·m² ≤ 2u² ≤ 2u²+u⁴。数值核对：½|K̂″(0)| ≈ 1.53 < 2（2u² 系数来源）。

**主定理 s71_main（组装真证，2026-10-27，替代 sorry）**：A_L(K) ≤ C_MT + C₁ε + C₂，C₂ = 2 显式。证明链 = pair_sum_expansion 分解 A_L = diag + prime + offcrit → diag ≤ C_MT + C₁ε（n2_linkage O(ε)）+ |prime|,|offcrit| ≤ 1 并入 C₂（linarith + ring）；(L3) axiom 语义已强化（diag 界入陈述）。全量 **2604 jobs 全绿**（build_qrh_l4b.txt）。2026-10-27 更新：pair_sum_expansion 由大 axiom 降为 bgs3_pair_expansion 组装定理，核可容许谓词 KernelAdmissible（K(0)=1 ∧ supp K̂⊂[−1,1]，λ≤1/2 核族）显式进入主定理链，s71_main 增加实参 Khat_admissible。

**长线 (L1)(L2) 攻坚第一轮（2026-10-27 晚，2604 全绿 main_l2_full.txt）**：
- **(L2) 半形式化落位完成**：`sum_abel_partial`（Icc 口径部分和版 Abel，真证）、`prime_sum_bound`（量子项组装真证：primeSum → Abel → SW 部分和 → 权重/衰减件，C = c·M·(C₂+C₃)）；`siegel_walfisz_chi5` 仍命名 axiom（PNT-in-AP 量级），内部结构已由 `prime_weight_bounds_Khat`（**真证，2026-10-29 降定理**，单常数 M 兼 |b_n|≤Mn^{−1/2} 与 |Δb_n|≤Mn^{−3/2}）、`sum_weight_decay`（C₂）、`sum_sqrt_decay`（C₃）三件显式化——裸 axiom 升级为「真实素数项 + Abel 组装」，SW 本体为下一步击破目标。
- **(S7.9 支撑截断口径 + 窗外拆窗，2026-10-29，两衰减件 axiom 降级 theorem）**：原裸 Σ n^{∓1/2}·e^{−c′√log n} 数学上发散（e^{−c′√log n} 亚多项式衰减，积分检验 u=√log x 发散），根因三层：K̂ 频域窄支撑截断（|δ log p|≤1 ⟹ p≤e^{1/δ}，有限和）+ χ₅ SW 振荡 + Abel 差分。新口径：`sum_weight_decay` theorem（C₂ = 2√(e^{1/δ})，链 = 逐项望远镜 `inv_sqrt_telescope_le`（(a−b)(a+b)=1）+ `sum_sqrt_telescope`（Icc 归纳）+ `sum_inv_sqrt_le_two_sqrt`（Σ_{n≤N} n^{−1/2} ≤ 2√N））；`sum_sqrt_decay` theorem（C₃ = e^{3/(2δ)}，链 = 逐项 e^{−c′√log n} ≤ 1 + `sum_le_card_nsmul`（card(Icc 1 N)=N 手写归纳：Icc∪{N+1} 分解 + `card_union_of_disjoint`）+ `mul_le_mul` + `Real.sqrt_le_iff` 平方单调（√(e^{1/δ}) ≤ e^{1/(2δ)}，无 Real.sqrt_exp 需绕））。**窗外拆窗（同轮完成）**：拆窗暴露出权重/支撑件空间错位——primeSum 权重原为时域 K(δ log n)，而窗外零性（|δ log n|>1 ⟹ 权重=0）只能由频域支撑件 `∀u, 1<|u| → fourierCos K u = 0` 给出，故全局改权重为频域核 `fourierCos K (δ log n)`（=K̂，与 S7.9 文档「素数项=K̂(δ log p)」口径一致，prime_weight_bounds 注释同步）；新增真证 `primeSum_window_eq`（by_cases min 拆窗：窗内 rw [hmin]；窗外 `Finset.sum_subset` + `Nat.floor_lt` + `Real.exp_lt_exp` + `mul_lt_mul_of_pos_left` ⟹ 窗外项 K̂=0 ⟹ 和式收缩到 ⌊e^{1/δ}⌋₊）。`prime_sum_bound` 去窗内前提 hXw：X' = min X (e^{1/δ}) 自动满足窗内（min_le_right），签名改 `(hKs : ∀ u, 1<|u| → fourierCos K u = 0)`，对任意 X ≥ 1 成立，C = c·M·(C₂+C₃)。真证链 +3（含拆窗），挂账 axiom −2。**落档**：S7.9 文档补拆窗小节（§6，含 6.1 空间错位口径 / 6.2 拆窗引理 / 6.3 无窗内版 / 6.4 验证），d1 惯例，audit errors=0，5 页渲染逐页通过。
- **(L1) 真实定义件**：`zeroWeightedSum`（复和取实部 Complex.cpow）/ `primePowerSum`（Finset 有限和 + Real.rpow）/ `trivialTerm`（∑' 实级数，χ₅ 偶特征 a=0）由 opaque 升级为真实定义；`logDerivTerm` 保持 opaque（导数件，下一轮）。
- **(L1b) 真证两件**：`primePowerSum_half_eq_sqrt` + `primePowerSum_half`（r=1/2 代数桥：n^{−1/2} = (√n)⁻¹，衔接 (L2) primeSum K≡1 特例）；`trivialTerm_summable`（x>1、r>0 级数可和：rpow 分解 x^{−(2ℓ+r)} = x^{−r}·(x^{−2})^ℓ + inv 界 + 几何级数比较）。
- **(L1b-C) x=1 边界口径（S7.11，2026-10-29）**：trivialTerm 在 x=1 为调和型发散（Σ 1/(2ℓ+r) ~ ½Σ 1/ℓ）；`landau_explicit_L` 前提由 1 ≤ x 收紧为 1 < x（防假命题陷阱：x=1 时 primePowerSum/zeroWeightedSum 为 0 而 logDerivTerm 一般非零，发散点 ∑' 默认值 0 无数学意义）；约定件 `trivialTerm_one_term`（x=1 逐项等式，simp）+ `trivialTerm_one`（trivialTerm r 1 = Σ 1/(2ℓ+r)，tsum_congr）真证；发散性正式证明（¬ Summable）留可选后续（"口径决定，非深证明"）。

**(L3)(L4) 移植（2026-10-27，Main 击破清单核心，已落位）**：
- 引理 5（核构造）→ KernelAdmissible + axiom bgs5_khat_fourier_supp（频域支撑，积分层件）+ Khat_admissible 组装。
- 引理 3（配对和展开）→ axiom bgs3_pair_expansion（A_L = diag+prime+offcrit；diag ≤ C_MT+C₁ε；|prime|,|offcrit| ≤ 1，Montgomery–Vaughan 均值口径）。
- 引理 4（离线误差）→ T^{3/8} 切割链：opaque offcritLow/offcritHigh + bgs4_offcrit_split/low/high（|·| ≤ R₁√log s / R₂√log s），offcritical_small 组装真证（abs_add_le + add_le_add + ring，R = R₁+R₂）。
- **数学诚实修正**：N1 vanishing 原 ∀N 陈述过宽（r̂(0)=1 不消失，fourierCos_scale 只给等式），改为带正参数 C 的显式衰减件假设。

**挂账 axiom（2026-10-29 现状，如实记录）**：
- Core 清单项：`C_MT<4/3`——**已真证出账**（2026-10-29；sin_lower_five + cos_upper_four + C_MT_lt_four_thirds；cos 四阶上界 73/96 经 cos x=1−2sin²(x/2) 自证，避开 mathlib cos_bound 余项 (5/96)|x|⁴ 不足；纯有理链、无积分、无聚合依赖）。**`fourierCos` 本体已真定义出账（2026-10-29）**：axiom → Bochner 积分真定义 fourierCos K z := ∫ x, K(x)·cos(2πzx) dx（不可积惯例 0，与 normL1 同机制；调用签名未变，primeSum/prime_weight_bounds 使用点无损）。**`khat_lipschitz` 已真证出账（2026-10-30 增量⑥）**：S_smooth 奇点延拓修口径（原闭式 u=±√2/(2π) 除零、Lean 惯例取 0 使原 axiom 陈述为假）→ L = π/(√2·|sin(1/√2)|) ≈ 3.42 显式定理，原 axiom 已删；**残余命名 axiom 仅**：`fourierCos_Khat`（连接件：fourierCos Khat = Khat 解析式挂钩——定义一致件，非本任务范围）、`bgs5_khat_fourier_supp`（积分层窄支撑）。
- Stage3：`n3_remainder_uniform`、`N_L`、`N_L_lower_bound`（数论件，陈述完整；真证挂 mathlib 聚合 Mathlib.olean）+ **`zerosLChi5_bounded_finite`（Z_T 有限）、`pair_count_bound`（计数 ≤ Dcnt·N_L T）（2026-10-31 增量⑧新增数论结构 axiom，承载 RvM/计数）**。已真证出账：`n1_diag_invariant`、`n1_offdiag_scale_eq`、`n1_offdiag_vanishes`（结构件，衰减件为带 C 假设）、`scaleKernel_L1_invariant`、**`fourierCos_scale`（2026-10-29，真证；其"需 IntervalIntegral/聚合"旧判断已实证否决——v4.34 Bochner 重构后 Measure.integral_comp_inv_mul_left 全空间可用）**、**`f0_sub_feps_L1_bound`（2026-10-30，axiom → theorem 真证出账；f0 支撑截断口径修正 + 7 辅助件，‖f₀−f_ε‖₁ ≤ 2ε·(√2|sin(1/√2)|)⁻¹ 完整链）**、**`pair_const_eps_bias`（2026-10-30 增量⑦，axiom → theorem：f_eps_abs_le/abs_tsum_sub_le_tsum_abs/pairConst_sub_pairL1 三段真证 + pairCount_L1_bound 组装，C₁=4M²D 口径修正，L¹ 界 + Lipschitz ⟹ 配对常数偏差；单编 stage3_pceb11 + 全量 lake build QRH 双绿）**、**`pairCount_L1_bound`（2026-10-31 增量⑧，axiom → theorem 真证出账：截断零点集 Z_T 修口径（原全零点集无限 ⟹ Summable 假）+ 归一化 D·N_Z(T)；D = 2M·Dcnt/normL1(f₀−f_ε)，M = (√2|sin(1/√2)|)⁻¹；hsum/hcnt 有限支撑 → hterm 逐项界 → hg_sum（of_norm_bounded）→ hle_sum/hle2/hle3 → ⟨hsum, le_trans hle2 hle3⟩；单编 stage3_pceb12 空 + 全量 build_qrh_lake 2719 绿）**、**`n2_linkage`（2026-10-31 增量⑨，axiom → theorem 真证出账：S7.4 定理 N2(iii) ε–λ 联动——λ=(logT)^q、a=(logT)^{−q}、ε=c·(logT)^{−q} ⟹ 总偏差 O((logT)^{−q})，C=2cM（M=(√2|sin(1/√2)|)⁻¹）显式；cos(2π·0·x)=1 ⟹ fourierCos z=0 化归 ∫f（hz+cos_zero）；|∫(f_ε−f₀)| ≤ normL1(f₀−f_ε)（Bochner 全空间积分绝对界 MeasureTheory.norm_integral_le_integral_norm + integral_sub；可积性四辅助件 f0_integrable（紧支撑有界，IntegrableOn restrict 口径）/ f0_sub_feps_abs_integrable / f0_sub_feps_integrable（f0_sub_feps_L1_bound L¹ 界压制）/ fourierCos_sub_f0_feps_abs_le）→ ≤2εT·M（f0_sub_feps_L1_bound 真证件）→ = C·(logT)^{−q}（unfold εT C M + ring）；单编 stage3_n2.txt 空 + 全量 build_qrh_lake 2719 绿 0 error）**。
- Main：`siegel_walfisz_chi5`（命名 axiom——PNT-in-AP 量级；内部三件显式化，2026-10-27 晚）；`landau_explicit_L`（组成项三件真实定义完成 + (L1b) 两件真证出账 + **(L1b-C) x=1 边界口径闭环**（S7.11，前提 1≤x→1<x，约定件两件真证）；logDerivTerm 仍 opaque、零点无条件收敛挂 (L1c) N(T) 计数）；`bgs5_khat_fourier_supp`、`bgs3_pair_expansion`、`bgs4_offcrit_split/low/high`（命名 axiom，2026-10-27 落位）；`offcritLow/offcritHigh` opaque。已真证出账：`pair_sum_expansion`（组装定理）、`offcritical_small`（组装真证）、`sum_abel_partial`、`prime_sum_bound`、**`prime_weight_bounds_Khat`（2026-10-29）**、`primePowerSum_half_eq_sqrt`、`primePowerSum_half`、`trivialTerm_term_nonneg`、`trivialTerm_term_le`、`trivialTerm_summable`、**`trivialTerm_one_term`/`trivialTerm_one`（2026-10-29，S7.11）**。

**文件结构**：C:\proj2\QRH.lean（根，import Core/Main/Stage3）；QRH\S7_1_Core.lean（4b 节：fourierCos **Bochner 积分真定义**（2026-10-29，axiom 降级）+ normL1 Bochner 定义 + fourierCos_Khat 命名 axiom（连接件）；§3b/§3c **S_smooth 延拓定义 + Khat 新闭式 + khat_hasDerivAt/khat_deriv_bound/khat_lipschitz 真证件**（2026-10-30 增量⑥，原 axiom khat_lipschitz 已删）；import Haar.NormedSpace）；QRH\S7_1_Stage3.lean（N1/L1 真证链 + Khat_closed_form S_smooth 适配 + **N2b pair_const_eps_bias 真证链（2026-10-30 增量⑦）+ pairCount_L1_bound 真证出账（2026-10-31 增量⑧：截断零点集 Z_T + 结构 axiom 两件 + 有限支撑/逐项界/of_norm_bounded/tsum_le_tsum 链）**）；QRH\S7_1_Main.lean（zerosLChi5、pairConstant、WeakRealPart 抽象 + (L3)(L4) 移植 + s71_main 组装真证）；QRH\Dbg_Khat.lean（khat 真证开发档案）。编译证据：build_core1..12.txt、build_main1..9.txt、build_stage3.txt、build_qrh_full{,2,3,_khat,_khat2,_s71}.txt、dbg_khat.txt、dbg_probe3.txt（IntervalIntegral.olean 缺失确认）、main_precise.txt、stage3_precise.txt、build_qrh_precise.txt、build_qrh_l1.txt、**build_qrh_l4b.txt（2026-10-27 全量 2604 绿）**、**main_l2_full.txt（2026-10-27 晚 (L1)(L2) 全量 2604 绿）**、**build_verify_cmt43.txt（2026-10-29 C_MT<4/3 增量全绿）**、**dbg_build.txt（2026-10-29 prime_weight_bounds 降定理全量 2704 绿）**、**dbg_build_x1.txt（2026-10-29 x=1 口径全量 2704 绿）**、**dbg_build_fourier.txt（2026-10-29 fourierCos 真定义 + fourierCos_scale 真证全量 2704 绿）**、**dbg_build_f0.txt（2026-10-30 f0_sub_feps_L1_bound 真证全量 2704 绿、0 warning）**、**core_khat1..10.txt（khat_lipschitz 单编轮次，core_khat10.txt 空=exit=0）+ dbg_build_khat.txt（2026-10-30 khat_lipschitz 真证全量 2704 绿、0 warning）**、**stage3_pceb12.txt（2026-10-31 pairCount_L1_bound 真证单编空=exit=0）+ build_qrh_lake.txt（2026-10-31 全量 2719 绿、0 error）**。

## 6. 下一步（按依赖序）

1. **Stage 4 已达成**（2026-10-27）：s71_main 组装真证 + (L3)(L4) 移植落位（Main 击破清单仅剩 (L1)(L2) 长线）——Lean 侧可核查的最远合理点已达。
2. **条件封口（2026-10-30 推进）**：积分层剩余——Stage3 `fourierCos_scale`（频域变量替换）**已于 2026-10-29 真证出账**（fourierCos 本体同步 axiom→Bochner 真定义；Measure.integral_comp_inv_mul_left 全空间变量替换，无需聚合；"需 IntervalIntegral"旧判断否决）；**`f0_sub_feps_L1_bound` 已于 2026-10-30 真证出账**（axiom → theorem；f0 支撑截断口径修正 + integral_const_mul/integral_add/indicator_Icc_integral 链，2704 绿 0 warning；原"真证挂聚合"旧判断否决——normL1 已 Bochner 真定义，无需聚合）。`C_MT<4/3` **已于 2026-10-29 真证出账**（纯有理链，√2 消去）。
3. **长线（第一轮攻坚完成 2026-10-27 晚；x=1 口径闭环 2026-10-29）**：(L1) 真实定义件 + (L1b) 两件真证出账（r=1/2 代数桥、trivialTerm 收敛）+ (L1b-C) x=1 边界口径（前提收紧 1<x、约定件两件真证）；(L2) Abel–SW 组装真证出账、SW 本体仍命名 axiom = PNT-in-AP 量级工程；下一步候选：logDerivTerm 导数件（deriv LFun）、SW 本体击破（挂 Ben Green 5 页证明机制核验）。
4. **prime_weight_bounds 降定理已闭环（2026-10-29）**：`prime_weight_bounds_Khat` 真证 + `prime_sum_bound` 特化 K:=Khat（2704 jobs 绿、无 warning）；**`khat_lipschitz` 已真证出账（2026-10-30 增量⑥）**——光滑件 axiom 删除，L = π/(√2·|sin(1/√2)|) ≈ 3.42 显式定理（S_smooth 奇点延拓修口径 + §3b/§3c ~15 件真证，2704 全绿 0 warning，dbg_build_khat.txt）——`prime_weight_bounds_Khat` 中 M = L·δ + B 的 L 实参现为真证常数，链条无 axiom 缺口；残余命名 axiom 仅 `fourierCos_Khat`（连接件）+ `bgs5_khat_fourier_supp`（积分层窄支撑，挂 mathlib 聚合）。
5. **`pair_const_eps_bias` 已真证出账（2026-10-30 增量⑦）**：N2b 层 L¹ 界 + Lipschitz ⟹ 配对常数偏差——`f_eps_abs_le` / `abs_tsum_sub_le_tsum_abs` / `pairConst_sub_pairL1` 三段真证链，积分层「离散配对和 ≤ D·δ·normL1」精确化为 `pairCount_L1_bound` 命名 axiom（含可和性三件打包），C₁ = 4M²D 口径修正（旧注释 2M·D 漏 L¹ 常数因子）；单编 stage3_pceb11.txt + 全量 lake build QRH 双绿，0 warning。**`pairCount_L1_bound` 已真证出账（2026-10-31 增量⑧，task #74 闭环）**：截断零点集口径修正（原全零点集 `zerosLChi5` 无限 + 竖直带配对无限 ⟹ Summable 假；新 `zerosLChi5UpTo T` 有限 ⟹ Finset 和）+ 归一化 D·N_Z(T)（δ→零点数，与 S7.1 §2 一致）+ 结构 axiom `zerosLChi5_bounded_finite`/`pair_count_bound`；真证块 = 有限支撑 → hterm 逐项界 → of_norm_bounded → tsum_le_tsum → le_div_iff₀ → ring；单编 stage3_pceb12 空 + 全量 build_qrh_lake 2719 绿 0 error。**`n2_linkage` 已真证出账（2026-10-31 增量⑨，task #75 闭环，axiom → theorem）**：S7.4 定理 N2(iii) ε–λ 联动——λ=(logT)^q、a=(logT)^{−q}、ε=c·(logT)^{−q} ⟹ 总偏差 O((logT)^{−q})，C=2cM 显式（M=(√2|sin(1/√2)|)⁻¹）；链 = cos(2π·0·x)=1 ⟹ fourierCos z=0 化归 ∫f（hz+cos_zero）→ |∫(f_ε−f₀)| ≤ normL1(f₀−f_ε)（Bochner 全空间积分绝对界 norm_integral_le_integral_norm + integral_sub，四辅助件 f0_integrable / f0_sub_feps_abs_integrable / f0_sub_feps_integrable / fourierCos_sub_f0_feps_abs_le 供可积性）→ ≤2εT·M（f0_sub_feps_L1_bound）→ = C·(logT)^{−q}（unfold εT C M + ring）；单编 stage3_n2.txt 空 + 全量 build_qrh_lake 2719 绿 0 error；残余命名 axiom：`fourierCos_Khat`（连接件）+ `bgs5_khat_fourier_supp`（积分层窄支撑）+ Stage3 数论件五件（n3_remainder_uniform / N_L / N_L_lower_bound / zerosLChi5_bounded_finite / pair_count_bound）+ Main SW/Landau 件。
6. **GitHub**：2026-10-27 已推送 7d77e55（QRH 快照 + d1 文档 + 数值件）；summary 随新提交同步。

## 7. 文件索引

- 文档（d1 根 C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\）：XLII 系列 22 份（S0–S7.12，含 S1a/S1b/S2(i)/S2(ii)/S3/S4/S5/S6 与「全尺度 GUE 配对 S0」）；英文 d1\en\（XLI、XLII-S0、S7.10、S7.11、S7.12 已译 + **arXiv 草稿**（C_MT 已证六处口径，2026-10-29 改进））；前置攻防 XL/XLI（0.6725→7/8 常数机制闭合）。**公式格式惯例（2026-10-27 起）**：d1 文档公式一律 Word 原生 OMML（LaTeX→MathML→OMML 管线，可编辑），禁 LaTeX 源码文本。
- 数值件（qrh_work\、new-chat\xlii_work\）：xlii_s7g_sw_constant.py/json/log、xlii_s7g_fig.py/png、xlii_s7f_bone1/2.py/json/fig、xlii_s7f_supersupport.py/json、xlii_s7_prime.json、xlii_s6_lambda.py/json（**㉚ 的真泛函来源，第 22–29/54–86/105 行**）；s7X 文档生成脚本（gen_s7_7_doc.py 含 OMML 支持）+ render-s7X\ 权威渲染。
- QRH 常数核正脚本（C:\proj2\ 根，㉚㉛㉜）：**`_ceta_check.py`（㉛ 的决定性件：C_η = Q(0)+2∫₀¹αQ 对三个锚点 4/3、C_MT、CCLM 下界）**、**`_s6_halfscan.py`（㉜：half 扫描 + δ 两口径对表 + GUE/g≡1 参考曲线；含 `rfft` 相位 `(−1)^k` 修正）**、**`_s6_Tscan.py`（㉜：H = 200 下 T 依赖六点表 + 噪声探针）**、**`_z_inspect.py`（㉜：零点表体检 / RvM 计数对照）**、`_s6_func.py`（真泛函反推/校准）、`_s6_var.py`（有号 KKT，证退化）、`_s6_qp2.py` + `_s6_ncheck.py`（非负 FISTA + n 收敛）、`_s6_unif.py` + `_s6_bis.py`（flat 端与二分）、`_s6_comb.py`（梳状端）、`_s6_smooth.py`（光滑核对照）；旧族 `_cmt_families2.py`、`_cmt_lambda_eig.py`、`_cmt_mu_exact.py`、`_cmt_lam_gt1.py` 保留为「F2 内部」记录。
- 零点表（本机，㉜ 体检目录 `…\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter`）：`zeros_T6e5.npz`（zeta 999,492 / L 1,150,050）、`zeta_T800000.npz`（1,369,279，对 RvM ✓）、`L_D5_T800000.npz`（1,570,290）、分级 `zeta_T40000/100000/200000/400000.npz`。
- Lean：见 §5。

### 增量⑱（2026-11-23）：`lfun_conj_symm` 第 ③ 步闭环 —— axiom 14 → 13

- **主定理**：`OrderPreservingBijection/LSeriesConj.lean` 新增 `LFunction_conj_global {N} [NeZero N] (χ) (hχ : ∀ n, (χ ↑n).im = 0) (hne : χ ≠ 1) (s) : LFunction χ (conj s) = conj (LFunction χ s)`——**全平面、无条件、零 sorry**。证明同 mathlib `riemannZeta_conj`（`ZetaAsymp.lean:461`）的解析延拓唯一性，但利用「χ ≠ 1 ⟹ `LFunction χ` 整函数（无极点）」**省掉了 `s = 1` 的显式值分情形**：`hf_an`/`hg_an` 均在 `univ` 上解析（后者经 `differentiableAt_conj_conj_iff`）→ 在 `{1 < re z}` 上相等（第 ② 步取共轭）→ `AnalyticOnNhd.eq_of_eventuallyEq`（`[PreconnectedSpace ℂ]`）→ 全平面相等 → `congrArg conj`。
- **QRH 落刀**：`S7_1_Main.lean:94-105` 的 `axiom lfun_conj_symm` **原位改成 `theorem`**，体一行：`LSeriesConj.LFunction_conj_global chi5Dirichlet chi5Dirichlet_im_zero chi5Dirichlet_ne_one z`（`LFun` 是 `def`，定义透明，无需 unfold）。`zerosLChi5_conj_closed` 调用点**零改动**。
- **审计**：`_conj_ax2.lean` 实测 `QRH.lfun_conj_symm` = `[propext, Classical.choice, Quot.sound]`、`QRH.zerosLChi5_conj_closed` = 同（原先含 axiom 名，现已消失）；`_conjglobal_ax.lean` 同；`_b_ax.lean` 三条（`zerosLChi5_bounded_finite` 零 axiom / `pairCount_L1_bound`、`pair_const_eps_bias` 3+N_L 三件 / `s71_main` 3+两件）**无回归**。
- **环境坑（写进 Findings §14.2）**：`differentiable_LFunction` 在 `namespace DirichletCharacter` 内（须全限定）；`eventuallyEq_of_mem` 在 `namespace Filter`（须 `open Filter`，zeta 模板文件顶部有）；`𝓝` 记号须 `open scoped Topology`。
- **命名 axiom 现状 13 条**：Core `fourierCos_Khat`；Main 7 条（`landau_explicit_L`、`siegel_walfisz_chi5`、`bgs5_khat_fourier_supp`、`bgs3_pair_expansion`、`bgs4_offcrit_split/low/high`）；Stage3 5 条（`N_L`、`N_L_lower_bound`、`pair_count_bound`、`offcritSum`、`n3_remainder_uniform`）。opaque 仍 4 个。
- **证据文件**：`build_qrh_H.txt`（3836 jobs / 0 error）、`_conjglobal_ax.lean`、`_conj_ax2.lean`。
- **诚实边界**：本条只是「口径硬前提」出账（`logDerivTerm` 的 `.re` 合法性不再挂假设），**不构成向 RH 推进的数学进展**；BGS 引理 4 的 4 个 opaque 与 Stage3 数论三件均未动。

### 增量⑲（2026-11-23）：`N_L` 数据型 axiom → 真定义（axiom 13 → 12）

- **改动**：`S7_1_Stage3.lean` 的 `axiom N_L : ℝ → ℝ` 删除，改为
  `noncomputable def N_L (T : ℝ) : ℝ := ((zerosLChi5UpTo T).ncard : ℝ)`（真实零点计数，`Set.ncard`），
  并新增真证 `N_L_nonneg`。定义移到 `zerosLChi5_bounded_finite` 之后、`N_L_lower_bound` 随之后移（避前向引用）。
- **口径后果**：`N_L_lower_bound` / `pair_count_bound` 从「对某个未知算子成立」变为「对真实零点数成立」——
  `c·T·logT ≤ #{ρ : L(ρ,χ₅)=0, |Im ρ|≤T}`、配对数 `≤ Dcnt·#{ρ}`。**陈述更强、不可兑换子回避**。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_J.txt`）；`_nl_ax.lean` 显示
  `pairCount_L1_bound` / `pair_const_eps_bias` 公理集从「3+`N_L`+`N_L_lower_bound`+`pair_count_bound`」
  降为「3+`N_L_lower_bound`+`pair_count_bound`」（`N_L` 名消失）；`N_L`、`N_L_nonneg` = 3 基础公理。
- **命名 axiom 现状 12 条**：Core `fourierCos_Khat`；Main 7；Stage3 4（`N_L_lower_bound`、`pair_count_bound`、`offcritSum`、`n3_remainder_uniform`）。opaque 仍 4 个。
- **坑（第二次踩）**：删 axiom 后原位只能留 `/- -/`，不能留 `/-- -/`，否则紧跟 docstring 时解析器报 `unexpected token '/--'; expected 'lemma'`。
- **难度标定**：`N_L_lower_bound` 降级需要 L 函数的 RvM 计数（幅角原理 + `arg` 连续化），是本工程第一条真解析数论活。

### 增量⑳（2026-11-23）：撤除 N3 空条目（`offcritSum` + `n3_remainder_uniform`），axiom 12 → 10

- **判定**：① 零下游引用（`offcritSum` 仅 2 处、`n3_remainder_uniform` 仅 1 处，均为自身声明）；② 内容空——「自由算子 + ∃R 有界」可被 `offcritSum ≡ 0` 同时满足；③ 文档对象（S7.5 `Roff = O((logT)^{-1/2})·N_L`，配对公式减去主项的余项）依赖 `w(ρ−ρ')`、复自变量 `r̂`、`x` 尺度相减三件未形式化机制，按字面写原始两两求和会得到 `O((T logT)²)` 而声明 `O(T√logT)` ⟹ 假命题。
- **落刀**：`S7_1_Stage3.lean` N3 节整块删除、原位留 `/-! -/` 存档（含原语句与勿复活警告）；`S7_1_Main.lean:1265` 清单 `[x]→[ ]`；`Stage3:2138` 清单拆分为 `N_L_lower_bound`（仍 axiom）+ `n3_remainder_uniform`（划掉）。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_K.txt`）；列 0 `axiom` 声明 = **10**；`_n3_ax.lean` 五条无回归（`pairCount_L1_bound`/`pair_const_eps_bias` = 3+`N_L_lower_bound`+`pair_count_bound`；`offcritical_small` = 3+`bgs4` 三件；`s71_main` = 3+`bgs3`+`bgs5`；`zerosLChi5_bounded_finite` 零 axiom）。
- **台账更正**：`offcritSum` 原为 `axiom` 而非 `opaque`，此前「4 个 opaque」记录有误——现 opaque 为 3 个（`offCriticalError`、`offcritLow`、`offcritHigh`）。
- **明账**：N3 状态 = **未形式化**（非「已证」）。补真前置：引理 5 本体（`w` + 复自变量 `r̂`）、`x` 尺度参数、主项相减口径。
- **当前账目**：9 条命名 axiom + 2 个 opaque + 1 条明确登记的未形式化项（N3）。

### 增量㉑（2026-11-23）：`bgs3_pair_expansion` 口径手术（含 `s71_main` 与根模块自检连带）

- **缺陷**：旧语句 `pairConstant K δ (logT/2π) zerosLChi5` 把 δ 当零点数当分母，且在全库零点集（无穷）上跑 `∑'` ⟹ 语句层缺陷（非「未证」）。
- **修正**：`pairConstant K δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offcrit`；`diag ≤ C_MT + C₁ε`、`|prime|,|offcrit| ≤ 1` 保留。`s71_main` 结论与 `QRH.lean` 自检 `example` 同步。
- **前置结构改动**：`zerosLChi5UpTo` / `N_L` / `N_L_nonneg` 从 Stage3 **上移至 Main**（Stage3 依赖 Main，不可反向 import）；Stage3 仅留注释占位，`zerosLChi5_bounded_finite` / `N_L_lower_bound` / `pair_count_bound` 仍在 Stage3。
- **语义**：归一化改为真实零点计数（与 Stage3 `pair_const_eps_bias` 口径统一）；求和域改为有限截断集（`tsum`→有限和，无须 Summable 假设）。**陈述变强**。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_L.txt`）；`_s71_ax.lean` 显示 `s71_main` 公理集与术前相同（3 + `bgs3_pair_expansion` + `bgs5_khat_fourier_supp`）；`pair_sum_expansion` = 3 + `bgs3`；`N_L` = 3 基础（定义）；axiom 总数 9、opaque 2（经增量㉒）。
- **备忘（第三次）**：删除声明后的原位注释必须 `/- -/`，不能 `/-- -/`（否则紧跟 docstring 报 `unexpected token '/--'; expected 'lemma'`）。

### 增量㉒（2026-11-23）：第四刀——`bgs4_offcrit_split` axiom → theorem（`offcritHigh` 降为定义）

- **病灶**：`offCriticalError` / `offcritLow` / `offcritHigh` 三件都是自由算子，不是某个真实数论对象的切片；于是「余项 = 低频 + 高频」不是数学事实，而是**命名约定**。用 axiom 声明命名约定 ⟹ 既不可被推翻、也不提供任何证明信息。
- **落刀**：`noncomputable def offcritHigh (T : ℝ) : ℝ := offCriticalError T - offcritLow T`（高频段 = 余项减低频段）；`bgs4_offcrit_split` 原位改 `theorem`，`intro s; unfold offcritHigh; ring`。
- **内容守恒**：`bgs4_offcrit_low` / `bgs4_offcrit_high` 两条 √log 段界仍在 axiom 层（未弱化）；`offcritical_small` 的证明与结论逐字未改（`abs_add_le` + `add_le_add` + `ring`，R = R₁+R₂）。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_M.txt`）；`#print axioms bgs4_offcrit_split` = `[propext, Classical.choice, Quot.sound]`（公理级清零）；`#print axioms offcritical_small` = `[propext, Classical.choice, bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]`；列 0 计数 axiom **10 → 9**、opaque **3 → 2**。
- **顺手抓到的缺口（未动）**：`offcritical_small` 全库**零下游消费**；而 `bgs3_pair_expansion` 注释里「离线项 `|offcrit| ≤ 1` 由 `offcritical_small` 除以 `N_L`」是文档层承诺、形式层无连线（`bgs3` 的 `offcrit` 是 `∃` 绑定的自由实数）。两条收尾（接线 / 退役）见 `Findings_GRH_Interface.md` §十八.5，需拍板后再动。**该缺口已在增量㉓接线消除。**
- **当前账目**：9 条命名 axiom + 2 个 opaque + 1 条明确登记的未形式化项（N3）。

### 增量㉓（2026-11-23）：第五刀——L4 链接入主定理（`bgs3` 离线项改为具体项）

- **病灶**：`bgs3_pair_expansion` 的离线项是 `∃ offcrit` 绑定的自由实数，与 `offCriticalError` 无名可通，「`|offcrit| ≤ 1`」只是公理里的一句话；同时 `offcritical_small` 全库零下游（L4 链悬空）。
- **改动**：① `bgs3`/`pair_sum_expansion` 的离线项改为具体项 `offCriticalError T / N_L T`，**删掉 `|offcrit| ≤ 1`**；② `bgs4_offcrit_low/high` 改为**绝对常数**（`∃R, ∀T, …`——原 `∀T, ∃R` 允许常数随 T 增长，比 BGS 原文弱且不可用）；③ 新增真证 `offcrit_remainder_le_one : T ≥ offcritThreshold → |E T / N_L T| ≤ 1`；④ `N_L_lower_bound` 从 Stage3 **上移**到 Main（收尾定理需要，且 Main 不可 import Stage3），Stage3 留注释。
- **阈值显式化**：`offcritConst := Classical.choose offcritical_small`、`NLc := Classical.choose N_L_lower_bound`、`offcritThreshold := max (exp 1) (max 1 (offcritConst / NLc))`，配 `offcritConst_spec` / `NLc_spec` / `one_le_offcritThreshold`。
- **证明链**：`R·√log T ≤ R·log T`（`√x ≤ x`，`log T ≥ 1` 由 `T ≥ e`）`≤ c·T·log T`（`R ≤ c·T` 由阈值）`≤ N_L T`（`N_L_lower_bound`）；再 `abs_div` + `div_le_one`（`N_L T = 0` 分支 Lean `x/0 = 0` 平凡成立）。
- **代价（诚实记账）**：`s71_main` 增加前提 `hbig : offcritThreshold ≤ T`（「T 足够大」）；`QRH.lean` 自检 `example` 同步。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_N.txt`）；`#print axioms s71_main` = 3 + `N_L_lower_bound` + `bgs3_pair_expansion` + `bgs4_offcrit_low` + `bgs4_offcrit_high` + `bgs5_khat_fourier_supp`（**闭包由 2 条 axiom 扩到 5 条，L4 首次进入主定理依赖**）；`pair_sum_expansion` = 3 + `bgs3`；`offcrit_remainder_le_one` = 3 + `N_L_lower_bound` + 两条段界。列 0 计数：axiom 仍 **9**（换内容不换条数）、opaque **2**。

### 增量㉔（2026-11-23）：第六刀——`bgs3` 不能降定理（它是假命题），改为固定核 `Khat`

- **纠正上一轮误判**：`bgs3` 不是「组合恒等式」——恒等式部分可空（任意 A 都能拆），内容全在 `diag ≤ C_MT + C₁ε` 与 `|prime| ≤ 1` 两条界；合起来即 `pairConstant ≤ C_MT + C₁ε + 1 + E/N_L`，是分析心脏（MV 大筛 + SW），不可由当前定义证出。
- **更严重的病灶（机器证据）**：`KernelAdmissible K := K 0 = 1 ∧ ∀ u, 1 < |u| → fourierCos Khat u = 0`，第二个合取项**与 K 无关**。新增真证 `kernelAdmissible_of_apply_zero : K 0 = 1 → KernelAdmissible K`，说明「可容许」对 K 的唯一约束是 `K 0 = 1`。而 `pairConstant` 是 K 在配对点上的取值平方和 ⟹ 取 `K := fun u => if u = 0 then 1 else M` 可使配对和无界，结论界与 M 无关 ⟹ **原语句对一般 K 为假**（同 `lfun_dirichlet_series` 病灶：自由参数进量词）。
- **修法**：`bgs3_pair_expansion` / `pair_sum_expansion` 固定核为 `Khat`（去 `K`/`hK`），与 Stage3 `prime_sum_bound` 的既定做法一致；`s71_main` 调用点同步。
- **审计**：`lake build QRH` 3836 jobs / 0 error（`build_qrh_O.txt`）；`#print axioms s71_main` = 3 + `N_L_lower_bound` + `bgs3` + 两条段界（**用户 axiom 5 → 4，`bgs5_khat_fourier_supp` 退出主定理闭包**）；`pair_sum_expansion` = 3 + `bgs3`；列 0 计数 axiom **9**、opaque **2**（`bgs5` 仍在账、仍被 Stage3 使用）。
- **待定口径（未动）**：`ε` 在形式层空转——`pairConstant` 不含 `ε`，`C₁` 与 `ε` 同在一个 ∃，`C₁ε` 松弛可任意吸收；N2 联动尚未接线。对外说「C_MT + O(ε)」时须注明该项当前不承载内容。

### 增量㉕（2026-11-23）：第七刀——`fourierCos_Khat` 是假命题（且使整库不一致），S7.6 换三角核，axiom 9 → 7

- **机检先赢一次**：`axiom fourierCos_Khat : fourierCos Khat u = Khat u`（Core 原 :705）为**假**。`Khat` 只按 `1/|u|` 衰减（合并 sinc 主导项常数 ≈ 0.767 ≠ 0）⟹ `∫|Khat| = ∞` ⟹ mathlib 按 `integral_undef` 取 0 ⟹ `fourierCos Khat ≡ 0`，而 `Khat (4/3) < 0`。
- **库级不一致（这是本条真正的分量）**：`bgs5_khat_fourier_supp`（`1<|u| → fourierCos Khat u = 0`）因 `fourierCos Khat ≡ 0` 对一切 `u` 成立——不是「频域窄支撑」，是**空话**；两条合起来给 `∀ u, 1<|u| → Khat u = 0`。根级探针 `_incons_ax.lean` 真证 `qrh_axioms_inconsistent : False`，`#print axioms` = `[propext, Classical.choice, bgs5_khat_fourier_supp, fourierCos_Khat, Quot.sound]`。**第七刀前账本上的 9 条不是 9 条假设，是 8 条 + 1 条使库不一致的假命题。**
- **先试「符号替换 1→2」并失败（记录在案）**：把权重区间 30 处 `fourierCos Khat (e)` 直接改成 `Khat (e)`，`Main:985` 类型不匹配（`dsimp [primeSum]` 展开出 `fourierCos Khat` 与 `hps` 的 `Khat` 不合），并暴露结构性问题：`K` 在 S7.6 被当成两种东西（`pairConstant` = 频率 profile、`primeSum` = 时域核再取变换）；素数项 `b_n ≈ 0.767/(πδ√n log n)` 配 `|Λ| ~ log n` 后 $\sum$ 发散如 $\sqrt X$，全靠 `X' = min(X, e^{1/δ})` 截断硬撑，而截断之正确性又依赖「Khat 支撑紧」这个 `bgs5` 假装给出、实际没给的性质。已整体回滚（`build_qrh_P0.txt` 3836 绿；回滚点 `bak_20261123_142148`）。
- **方案 (A)：三角核**。`def triKer (u : ℝ) : ℝ := max 0 (1 - |u|)`（Core §4c）。归一/紧支撑/有界/1-Lipschitz 四条全真证（3 基础公理），**无需 sin 估计、无需 `S_smooth` 奇点延拓**——原 `khat_lipschitz` 要 `π/(√2|sin(1/√2)|)` + 均值定理，三角核只要 `abs_max_sub_max_le_max` + `abs_abs_sub_abs_le_abs_sub`。
- **A2**：`prime_weight_bounds_tri`，`M = δ + 1`（B = sup Γ = 1、L = Lip Γ = 1），证明结构同构、sin 估计换成 `triKer_abs_le_one`/`triKer_lipschitz`，3 基础公理（`_tri_ax.txt`）。
- **A3 九处**：① `primeSum` 定义改为直接取 profile（`(√n)⁻¹·K(δ log n)`，不再外套 `fourierCos`），消掉「一个 K 两种含义」；② 撤 `axiom bgs5_khat_fourier_supp`（改存档块，替代物 `triKer_supp`）；③ `primeSum_window_eq` 前提改 `∀ u, 1<|u| → K u = 0`，调用点 `(fun _ h => triKer_supp h)`——**求和截断第一次有真实依据**；④ 删 `prime_weight_bounds_Khat`（109 行）；⑤ `prime_sum_bound` 区间替换；⑥ `KernelAdmissible` 重定义为 `K 0 = 1 ∧ ∀ u, 1<|u| → K u = 0`（第二个合取项从此真的关于 K），删 `Khat_admissible` 与 `kernelAdmissible_of_apply_zero`，新增 `theorem triKer_admissible`；⑦ `bgs3`/`pair_sum_expansion`/`s71_main`/`QRH.lean` 根自检换核；⑧ 撤 `axiom fourierCos_Khat`（存档块含两路证伪 + 真命题 `fourierCos f0 u = Khat u` 的四段真证路线）；⑨ `:585` 措辞改「与已撤的 Khat 版同构」。
- **审计**：`lake build QRH` **3836 jobs / 0 error**（`build_qrh_R.txt`、`build_qrh_R2.txt`，job 数与术前一致）；`_a3_ax.lean`/`_a3_ax.txt`：`triKer_admissible`、`primeSum_window_eq` = 3 基础；`prime_sum_bound` = 3 + `siegel_walfisz_chi5`；`pair_sum_expansion` = 3 + `bgs3`；`s71_main` = 3 + `N_L_lower_bound` + `bgs3` + `bgs4_offcrit_low` + `bgs4_offcrit_high`（**用户 axiom 仍 4，换核没让主定理多背假设**）。列 0 计数：**axiom 7**、**opaque 2**。
- **新账**：`siegel_walfisz_chi5`、`landau_explicit_L`、`bgs3_pair_expansion`、`N_L_lower_bound`、`pair_count_bound`、`bgs4_offcrit_low`、`bgs4_offcrit_high`；opaque `offCriticalError`、`offcritLow`；未形式化 N3。撤掉的两条：一条假、一条空。
- **连带义务（㉗ 做、㉘ 撤、㉚ 再撤）**：`C_MT` 与 `0.6725 = 2 − C_MT` 的三角核重算做了三步：①拼出了两个泛函（C_A 出自 ρ₂ 积分、`2 − C` 只在密度泛函）⟹ 0.8435059964 作废；②按密度泛函 Γ 给 4/3 ⟹ 常数 2/3、类上确界 0.6755169；③**㉚ 核正原始件：A 的核是 K = f̂ 而非 f\\*f，①②整族作废，真泛函下 7/8 的 λ 门槛为 1.13–1.15**。三步既没使 7/8 成立，也没带来常数上调。`ε`/`C₁ε` 空转未动。

### 增量㉖（2026-11-23）：A4 真证——三角核余弦变换闭式（明账 2 → 1）

- **目标语句**：`fourierCos triKer u = if u = 0 then 1 else (Real.sin (πu) / (πu))²`。此前它只写在 `triKer` docstring 的注释层（被审计台登记为明账 A4）。
- **A4 组 11 件全部机检通过**（`QRH/S7_1_Core.lean` §4c′，紧随 `triKer_lipschitz` 之后）：
  `triKer_eq_zero_of_notMem_Icc`、`triKer_of_abs_le_one`、`continuous_triKer`、`integral_one_sub_mul_cos`、`integral_symm_zero_one`、`integral_triKer_mul_cos`、`integral_triKer`、`integral_eq_intervalIntegral_of_support`、`fourierCos_triKer_zero`、`fourierCos_triKer_ne`、`fourierCos_triKer`。
- **`#print axioms`**（`_a4_ax.txt`）：上述 11 件**全部 = `[propext, Classical.choice, Quot.sound]`**；`s71_main` 闭包不变（3 基础 + `N_L_lower_bound` + `bgs3_pair_expansion` + `bgs4_offcrit_low` + `bgs4_offcrit_high`），**A4 不进主定理依赖闭包**（它是 `C_MT` 重算的前置输入，不在 S7.6 语句里）。
- **数学路线（与注释层原推导一致）**：支撑落于 [−1,1] ⟹ 全空间积分化到 `∫₋₁¹`（`setIntegral_eq_integral_of_forall_compl_eq_zero` + `integral_Icc_eq_integral_Ioc` + `intervalIntegral.integral_of_le`）⟹ 偶性降半区间（`integral_comp_neg` + 相邻区间可加）⟹ 反导数 `F(y) = c(1−y)sin(cy) − cos(cy)`，`F' = c²((1−x)cos cx)`，清分母后走 `eq_div_iff` ⟹ `∫₀¹(1−x)cos(cx)dx = (1−cos c)/c²` ⟹ `1 − cos a = 2sin²(a/2)`（`Real.sin_sq_eq_half_sub`）⟹ sinc²。`u = 0` 分支单算 `∫Γ = 1`。
- **审计**：`lake build QRH` **3836 jobs / 0 error**（`build_qrh_T.txt`）；列 0 计数 **axiom 7、opaque 2、明账 1**（只剩 N3）。
- **环境备注（推翻旧结论）**：`Mathlib.MeasureTheory.Integral.IntervalIntegral` 聚合 olean 本机仍缺，但其子模块 olean 齐备，`import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` 可用；`setIntegral_eq_integral_of_forall_compl_eq_zero` 在 `Mathlib.MeasureTheory.Integral.Bochner.Set`（`Bochner/Set.lean:488`）。两条已加入 Core 头部 import；Core 内新增 `open MeasureTheory`（仅此块需要 `volume` 裸名）。
- **剩余义务（已于增量㉗ 执行）**：`C_MT` 与 `0.6725 = 2 − C_MT` 的三角核重算已做，见增量㉗；A4 在此口径下不做常数输入（详见 ㉗ 末条）。



### 增量㉗（2026-11-23）：C_MT 按三角核重算——C_A = 1.1564940036【其中「常数 0.8435059964」已于同日撤回，见增量㉘】

- **口径裁定（用户拍板）**：三角核 `triKer` 在库里作**配对核**（A3 后的 `pairConstant triKer`），即 K = Γ 直接入 Σ K(δΔ)²，记为口径 A。口径 B（Γ 作密度、配对核取 sinc²，即旧文「配对侧 sinc⁴」那句）**暂留旧文，日后单独改**。
- **泛函（原始版本，两个锚点分属两个不同泛函——这正是㉘ 抓到的错位）**：当时写作 C(K) = 1 + ∫ K(u)² ρ₂(u) du，ρ₂(u) = 1 − (sin πu/πu)²。
  - 锚点 1：cos-window 最优核 f₀（supp [−1/2,1/2]）→ C = 1.3274983，与账面 1.3274992963 = 1/2 + (1/√2)cot(1/√2) 差 1e−6 —— 但这条锚点其实属于**密度泛函**（2 − ∫f*f·Γ），不在 ρ₂ 积分泛函里；
  - 锚点 2：均匀核（[−1/2,1/2] 上取 1）→ C = 4/3 精确 —— 这条属于**密度泛函**（2 − ∫Γ·Γ = 4/3），也不在 ρ₂ 泛函里（ρ₂ 泛函下它给 1.1564940）。
- **三角核算术**：∫Γ² du = ∫₋₁¹ (1−|u|)² du = 2/3（精确）；J₁ = ∫₋₁¹ (1−|u|)²·(sin πu/πu)² du = 2[−½log(4π²) − γ + Ci(2π) + ½ + π Si(2π)]/π² = 0.5101726630（20 位；sympy 闭式与 mpmath 分裂积分独立吻合到 20 位）。
  ⟹ **C_A = 1 + 2/3 − 0.5101726630 = 1.1564940036**（ρ₂ 积分泛函下的合法值）。**但「QRH 常数 2 − C_A = 0.8435059964」不成立**：那段减法只在密度泛函下是常数，而 C_A 来自 ρ₂ 泛函，见增量㉘。
- **对 7/8 的判定（修正后；㉚ 再降级）**：ρ₂ 泛函**不可用于判定**（其下确界为 1，K 越窄越小，见㉘）；按密度泛函，Γ ⟹ 常数 0.66667、类上确界 0.6755169，距 0.875 差 **0.1995**。〔㉚：这一行的泛函本身不是 A 的（A 用 K = f̂），故 0.1995 作废，真泛函下差 0.034–0.040。〕，**7/8 不是核形状能解决的**。无条件分支不变：λ ≤ 1/2 的 C_MT = 1.3274993 ⟹ 0.6725。
- **为何 Γ 超出无条件域**：supp Γ = [−1,1] ⟹ λ_eff = 1 > 1/2（Lamzouri 变分域端点之外），属超支撑分支，需拟随机前提 (H2′_λ)。这不是口径错误，而是 7/8 通道本来就付的价；反过来说，A3 用 Γ 换来的「K 紧支撑 ⟹ 截断有依据」也正是超支撑域的入场券。
- **口径 B（保留旧文，未采用；其数属另一词法，未独立复核）**：若把 Γ 当密度、配对核取 sinc²，则 ∫K² = ∫ sinc⁴(πu) du = 2/3、⟨Γ*Γ,Γ⟩ = ∫ sinc⁶(πu) du = 11/20（经典 ∫₀^∞ sinc⁶ = 11π/20，独立数值复核 0.5500000000），得 C = 67/60 = 1.1166667 ⟹ 常数 53/60 = 0.8833333（过 7/8，余量 1/120）。未采用的代价条款：sinc² 非紧支撑，A3 的求和截断 `min ⌊X⌋ ⌊e^{1/δ}⌋` 立刻失去依据，素数侧要重证一份 sinc² 版 weight bounds。**【㉘ 追加】这个 0.8833 与 0.8435 犯了同一类错：它把「1 + ∫K² − ∫K²sinc²」的 C 直接减成常数，而未确认该式的 1/δ 归一与 λ_eff 词法；在改用前必须先过㉘ 的判据。**
- **形式状态（必须注明）**：以上两数是**解析闭式 + 20 位数值复核**，**未经 Lean 机检**；不改变 axiom 7 / opaque 2 / 明账 1 的计数，也暂不登记为明账。若日后要机检，需把 J₁ 的 Ci/Si 闭式与 sinc 积分形式化，属独立一件活（成本不低于 A4）。
- **A4 的处置（口径 A 下的连带结论）**：`fourierCos triKer` 在 C_A 里不再出现（C_A 只用 ∫Γ² 与 J₁），故「A4 是 C_MT 重算前置件」这句话在口径 A 下作废——A4 实际是**口径 B 的预备件**。A4 本身不是废件（sinc² 仍是 profile 的频域描述，也是日后改 B 时的唯一入口），但账上要如实改成：A4 = 已机检、消费者 = 口径 B（待启用）。

### 增量㉘（2026-11-23）：撤回「常数 0.8435059964」——两个泛函被拼成一个数

- **撤回对象**：`2 − C_A = 0.8435059964`，以及由此得出的「与 7/8 差 0.0314940」「常数从 0.6725 提到 0.8435」全部表述。C_A = 1.1564940036 本身**保留**（它是下面 F1 的合法值）。
- **错在哪**：这一轮把两个不同的泛函当成同一个 C 在用。
  - **F1（ρ₂ 积分泛函，与代码 `pairConstant triKer` 同词法）**：C = 1 + ∫K(u)²ρ₂(u)du，ρ₂ = 1 − (sin πu/πu)²。Γ ⟹ ∫Γ² = 2/3、∫Γ²sinc² = J₁ = 0.5101726630 ⟹ C_A = 1.1564940036。**这个数没错。**
  - **F2（密度泛函，文档「等价密度形式」与「常数 = 2 − C」这个减法真正的归属）**：C = 1 + ∫f² − ⟨f*f,Γ⟩ = 2 − ∫K·Γ。Γ（常密度 f≡1）⟹ ∫Γ·Γ = 2/3 ⟹ C = **4/3**。
  - 结论：`1.1564940` 属 F1，`2 − C` 属 F2，**拼接出来的 0.8435060 不对应任何泛函**。F2 词法下 Γ 的常数是 **2/3 = 0.66667 < 0.6725**，即「三角核把常数抬高了」这件事从未发生，实际是**下降**。
- **F1 为什么根本不能用来判定 7/8**：ρ₂ ≥ 0 且 ρ₂(0) = 0，K 越往 u=0 挤积分越小。实测（a=1/2 固定）：Γ 1.15654、cos-window 1.15143、cos(πx) 1.08531、exp(−16x²) 1.03980、exp(−256x²) 1.00071；支撑缩到 a=0.0625 时任何核都给 ≈1.00003。**F1 的下确界就是 1**，所以「C ≤ 1.125 算过 7/8」在 F1 下是空赢——它只说明核变窄，不说明任何关于零点配对的事。
- **F2 下的核族排序（同一泛函、同一类 supp f ⊂ [−1/2,1/2]，μ = 2 − C）**：变分最优 0.6755169 > cos-window 0.67454（闭式 0.6725）> Γ（常密度）0.66667 > exp(−4x²) 0.66216 > (1/4−x²)¹ 0.61905 > cos(πx) 0.60793 > (1/4−x²)² 0.54849 > exp(−16x²) 0.49907。
- **变分最优的真实答案**：F2 最大化即算子 T f(x) = ∫_{[−a,a]} Γ(x−y)f(y)dy 的 Rayleigh 商，答案 = 最大特征值。分片常数 Galerkin（单元双重积分解析、整区校核 ∫∫Γ = 2/3），N = 25→400 单调升、误差 O(h²)：**μ₁(a=1/2) = 0.67551694（外推），C_min = 1.32448306**；a=1/4 得 0.41752274。旁证：常密度 f 的 Rayleigh 商 = 2/3，与上表 Γ 行完全吻合。**（㉙ 已把这条答案解成闭式：`v tan v = 1`、μ₁ = 1/(2v₁²) = 0.6755169434，最优核 f\\*(x) = cos(2v₁x)；下述「外推 0.67551694」由此升为解析值。）**
- **判定（取代旧判定）**：supp f ⊂ [−1/2,1/2] 这一类里，形状优化的全部收益是 0.6725 → 0.6755169（**+0.0030**），距 7/8 的 0.875 差 **0.1995**。**7/8 不可能靠核形状解决**：要么动 λ_eff（超支撑，需 (H2′_λ)），要么动配对密度的归一（离散求和里的 1/δ 因子）。
- **一条必须写进的保留（2026-11-23 已由㉚ 改写，旧判错误）**：旧文说「F2 的连续形式丢掉了离散求和的 1/δ 与 N 归一」——**这句错**。查 S6 原文与其脚本：δ = logT/2π 本身就是平均间距的倒数，u = δΔ 已是归一间距，A 就是「1 + 每对 1/N」，**没有 1/δ，也没有别的归一因子**。真正的错位不在归一，而在**核的形状**（K = f̂ 而非 f\\*f），见增量㉚。结论仍然成立：F2 数不能直接用于判定 7/8，但理由换了。
- **新判据（进审计台）：「一个常数只能有一个泛函」**。凡出现 C 与常数，必须同时写明：①哪个泛函（F1 还是 F2）、②归一（δ 的含义、有无 1/δ）、③λ_eff 与支撑、**④核的定义（K = f̂ 还是 f\\*f？支撑有限还是无限？）**。缺一项即判为口径漂移。本轮前三项缺两项，故 ㉗ 的数当天撤回；**㉚ 则是前三项齐全、只缺第④项——判据必须随病迭代。**
- **证据**：`_cmt_families2.py` / `_cmt_families2.txt`（两泛函表 + 锚点自检，F1(Γ)=1.1565398 对 1.1564940 差 4.6e−5 为网格误差）、`_cmt_lambda_eig.py` / `_cmt_lambda_eig.txt`（特征值与 2/3 校核）。均为数值，**未 Lean 机检**；不改变 axiom 7 / opaque 2 / 明账 1。

### 增量㉙（2026-11-23）：变分最优核的特征方程解出（μ₁ = 1/(2v₁²)，v₁ tan v₁ = 1）——全谱变闭式

- **结论（先给数）**：在 supp f ⊂ [−1/2,1/2]（λ_eff ≤ 1）这一类里，密度泛函 `C = 1 + ∫f² − ⟨f*f,Γ⟩ = 2 − ∫K·Γ` 的最大值由算子 `T f(x) = ∫₋₁/₂^{1/2} (1−|x−y|) f(y) dy` 的最大特征值给出，而它是**闭式**的：
  - **v₁ = 0.8603335890193797624838934** 是 `v tan v = 1` 的最小正根；
  - **μ₁ = 1/(2v₁²) = 0.6755169434391893120**，**C_min = 2 − μ₁ = 1.3244830565608107**；
  - 距 7/8（0.875）差 **0.1994830566**；相对 cos-window 的 0.6725007037 增益 **+0.0030162**（其中 0.6725007037 = 2 − [1/2 + (1/√2)cot(1/√2)] 的精确值，不是四舍五入的 0.6725）。
- **推导（两步分部积分，精确而非近似）**：a = 1/2，
  - `(Tf)′(x) = ∫ₓᵃ f − ∫₋ₐˣ f`，`(Tf)″(x) = −2 f(x)`（因为 |x−y| ≤ 1 在整个区段内成立，核恒为 1−|x−y|）；
  - 由 μf = Tf 得 `f″ + k²f = 0`，`k² = 2/μ`；令 `g = Tf − μf`，则 g″ = 0 ⟹ g 线性，故 **g ≡ 0 只差两个端点条件**。
- **两支边界条件（谱的全部来源）**：
  - **偶支** f = cos kx：g′(0) 自动为 0，要求 g(0) = 0 ⟹ `Tf(0) = 2/k²` ⟹ **`(1−a)k sin(ka) = cos(ka)`**，即 `tan v = a/((1−a)v)`（v := ka）；
  - **奇支** f = sin kx：g′(0) = −2cos(ka)/k = 0 ⟹ **`cos(ka) = 0`** ⟹ ka = π/2 + nπ。
- **特征方程的三种等价写法（a = 1/2）**：`v tan v = 1`；`tan v = 1/v`；以 μ 直接写 `√(2μ)·tan(1/√(2μ)) = 1`（因 v = 1/√(2μ)），μ₁ ∈ (2/π², ∞)。
- **全谱（闭式，两支交替）**：偶支 `μ = 1/(2v_n²)`（v_n 为 v tan v = 1 的正根：0.8603335890、3.4256184595、6.4372981792、9.5293344054、…）；奇支 `μ = 2/((2n+1)²π²)` = 0.2026423673、0.0225158186、0.0081056947、…。排序后前五个：0.6755169434（偶₁）、0.2026423673（奇₀）、0.0426080858（偶₂）、0.0225158186（奇₁）、0.0120659842（偶₃）。
- **三重校核**：
  1. 点值校验：对 f\\*(x) = cos(2v₁x) 有 `max|Tf\\* − μ₁f\\*| = 2.7e−10`（f 峰值归一为 1），Rayleigh 商 = 0.6755169432；
  2. 与独立数值谱对照：解析 0.675516943439 vs 分片常数 Galerkin 外推 0.67551694，差 **3.4e−9**；前五个本征值与 Galerkin 的五位数字逐个吻合；
  3. 一般 a 的公式在 a = 1/4 处给 μ = 0.4175227354，与先前 Galerkin 的 0.41752274 一致。
- **最优核的形状（这次是具体的）**：f\\*(x) = cos(2v₁x) = cos(1.7206671780·x) 于 [−1/2,1/2]，K = f\\*\\*f\\*。对照 S6 的 cos-window 核（k = √2 = 1.4142136），它的频率高 **21.7%**——即最优核在端点处衰减得更狠，把质量更紧地压在 u=0 附近（ρ₂(0)=0 正是这个方向）。这解释了 cos-window 为什么不是最优、以及 +0.0030 的来源。
- **适用域（必须与数一起写）**：以上全部只在 **2a ≤ 1（即 λ_eff ≤ 1）** 内成立。λ_eff > 1 时核 Λ 的紧支撑会截掉 |x−y| > 1 的耦合，`(Tf)″ = −2f` 不再成立，ODE 与边界条件须重推——**不要用这条公式外推 a > 1/2**（已试过，数不可信）。
- **账本意义（㉚ 后降级）**：0.6755169 从「机算外推」升为「闭式谱的第一个根」，且因 T 是紧自伴正算子，该 sup **被 f\\* 真正达到**——但这一切都只在 F2 泛函内成立。**㉚ 已判定 F2 不是 A 的泛函，故「7/8 不可由核形状达成」这句话在 F2 内为真、对 A 无效**；对 A 的对应结论是 λ 门槛 0.562–0.575（见㉚）。闭式本身（v tan v = 1、全谱、三重校核）作为数学结果保留。
- **形式状态**：仍**未 Lean 机检**；axiom 7 / opaque 2 / 明账 1 不变。若日后要形式化，所需的是「一元超越方程 v tan v = 1 在 (0, π/2) 内有唯一根」+ 该算子的谱展开，属独立一件活（比 A4 轻，比 J₁ 的 Ci/Si 闭式重）。
- **证据**：`_cmt_mu_exact.py` / `_cmt_mu_exact.txt`（特征方程求解、全谱、点值校验、Galerkin 对照）；`_cmt_lambda_eig.py` / `.txt`（Galerkin 侧，含 ∫∫Γ = 2/3 校核）。

### 增量㉚（2026-11-23）：核正 A 的真泛函——K = f̂（不是 f\\*f）；F1/F2 整族作废，7/8 的 λ 门槛从 2.0363 收到 1.13–1.15

- **起因**：用户质疑「归一仍未确定 ⟹ 可能方程（方案）还不对」。本轮不辩论，直接查原始件：S6 docx 原文（`_dump_s6.py` 段 [11]/[21]/[25]/[29]/[112]）+ **S6 的原始脚本** `…\2026-10-16\new-chat\qrh_work\xlii_s6_lambda.py`（此前未纳入过分析）。
- **原文口径（按脚本行号，可复查）**：
  - 第 22–29 行 `make_K_mt`：`K(u) = ∫ f(x) cos(2πux) dx`，`f₀ = cos(√2x)/(√2 sin(1/√2))`，支撑 [−1/2, 1/2]，**∫f₀ = 1 ⟹ K(0) = 1**。即 **K 是密度的余弦变换**，不是自相关。
  - 第 31–39 行尺度族：`f_λ(x) = f₀(x/λ)/λ`、支撑 [−λ/2, λ/2]，并显式 `K /= K[0]` 归一到 K(0) = 1。
  - 第 54–76 行 `pair_hist`：对 Δ 做直方图、`binw = 0.02`、`half = 40`、**双向都收**（`np.abs(z[L:H] − za[i])`）。
  - 第 85 行：`A = 1 + Σ(hist · K²)/n`；第 105 行：`δ = log T/(2π)`。
  - 文档段 [11] 写的「K = η²̂」要按代码读作 **K = f̂**（f 为密度）；段 [21] 的「A = 1 + Σ_{Δ>0} K(δΔ)²/N」与代码一致。
- **归一判定（撤旧判）**：δ = logT/2π 本身是**平均间距的倒数**，u = δΔ 已是归一间距，A 就是「1 + 每对 1/N」。**没有 1/δ，也没有别的归一因子**。㉘ 里「F2 丢掉了 1/δ 与 N 归一」这句当场撤回（已改），㉗/㉘ 的核心结论（数不能拼、F2 不可判定）仍然成立，但理由换成核形状。
- **真泛函（连续模型）**：A(f) = 1 + ∫₀^∞ ρ₂(u)|f̂(u)|²du，ρ₂(u) = 1 − sinc²(πu)（GUE 配对密度），f 为概率密度、supp f ⊂ (−λ,λ)。
- **模型校准（关键一步，模型能否用全靠这一步）**：f₀ 在 λ = 1/2 给 **A_model = 1.162882**，S6 实测 **1.1868**，差 **2.0%**——同一对象，可用（**㉛ 撤回：这是拿「单边模型」对「有序实测」造成的假吻合，真差额 12%，见㉛**）。反证：λ-尺度族（支撑 λ/2）模型系统低 13–24%（实测/预测的「超出 1 的部分」比 1.44→1.35），故模型只在校准点附近可信，绝对数按**区间**用。
- **边界读数（a = 0.5，同一泛函）**：梳状最优 A = 1.1588（2−A = 0.8412）｜flat 核 A = 1.1654（0.8346，解析锚点 ∫₀^∞ρ₂sinc² = 1/6 精确）｜f₀ 实测 1.1868（0.8132）｜C_MT = 1.3275（0.6725）。四行顺次一致，说明 **C_MT 是最坏情况上界，不是实际值**。
- **变分（可容许类：f ≥ 0、∫f = 1、supp ⊂ [−a,a]，FISTA + 单纯形投影）**：
  - 极小元是**梳状密度**（峰/均值随 n 增：1.09→8.10 于 n = 50→400），必须先排除「网格假象」：Q_min 随 n = 50/100/200/400 为 0.16280/0.16100/0.15958/0.15881（a = 0.5）与 0.11033/0.10991/0.10863/0.10808（a = 0.6），**收敛到有限值**。
  - **7/8 临界**：梳状端 a\\* = **0.562**（a = 0.560 ⟹ Q 0.12597；0.570 ⟹ 0.12132）；flat 端 a\\* = **0.5752**（40 次二分，Q = 0.12500000）。⟹ **λ_eff\\* ≈ 1.124–1.150**。
  - **光滑度只值 0.013（2.3%）**：门槛不是靠病态核撑出来的，flat 核本身就够。这条直接消解了「梳状解不可容许」的顾虑。
- **顺手否掉的两个「看起来更平滑」的核**：抛物 (1−(x/a)²) 在 a = 0.575 给 Q = 0.1696、半周期余弦 cos(πx/2a) 给 0.1801，都远高于 0.125。原因：它们把 ‖f‖₂² 抬高（3/(5a)、π²/(8a)，flat 是 1/(2a)）。**「更平滑更好」不成立；关键变量是支撑宽度，不是光滑性。**
- **两个刻度必须分开写**：
  - **典型（GUE）刻度**：λ_eff ≈ 1.13–1.15 即够 7/8（A ≈ 1.125）；
  - **定理刻度** ~~要证的是「对所有可容许零点配置 A ≤ 1.125」，须最坏情况上界（C_MT 就是 λ = 1/2 处的那个界）；粗测最坏形（无排斥 ρ₂ ≡ 1）下 A = 1 + ‖f‖₂²/2，flat 在 a = 0.5 已是 1.5，故真实定理门槛必大于 1.13，且没有解析件定不下来。~~ **〔退役，2026-11-23 增量㉛〕本句「没有解析件定不下来」被原文取代：Lamzouri Lemma 3.1 给的是恒等式而非界，且 2λ ≤ 1 类内极小 = C_MT = 1.3274993 已由 CCLM Cor.14 封顶。门槛不是「未定」，而是「已定在 1.3275」，7/8 的 1.125 在该类内被定理排除。本行旧文仅作口径演化存档。**
- **账本意义（撤的是一个族，不是一个数）**：F1（1 + ∫|f\\*f|²ρ₂）与 F2（2 − ∫(f\\*f)·Γ）**在账上标记「泛函不符，作废」**；C_A = 1.1564940、4/3、μ₁ = 0.6755169434、λ_eff\\* = 2.0363 均退为该族内部数值，不再作为 7/8 的判据。axiom 7 / opaque 2 / 明账 1 **不变**（这些都是解析与数值，未进 Lean）。
- **判据升级（进审计台）**：「一个常数只能有一个泛函」补第 ④ 项——**核的定义**（K = f̂ 还是 K = f\\*f？支撑是无限还是 [−1,1]？）。本轮三项齐全却仍错，就是缺第 ④ 项。
- **未决（下一步）**：① 最坏情况上界能否用 BGS 二次矩不等式写成一般 λ 的形式（这是把 1.13 变成定理的唯一路径）；② 连续意义下无光滑约束时 Q 的下确界是否有限（本轮 n-收敛支持「有限」，但未证明）；③ 模型在 λ-尺度族上的 13–24% 偏差来自何处（配对计数归一还是 ρ₂ 口径）——这是能否把区间收窄到三位数字的关键。
- **证据（全部纯数值，未 Lean 机检）**：`_dump_s6.py`（原文抽取，复用）；`_s6_func.py`（真泛函反推 + λ-尺度族对表 + uniform 锚点）；`_s6_var.py`（无约束 KKT，证明有号类退化：极小元为 ±10⁵ 振荡尖刺、Q 可压到 0.1447）；`_s6_qp2.py`（非负类 FISTA + 单纯形投影，含 n-收敛）；`_s6_ncheck.py`（n = 50/100/200/400 收敛检查）；`_s6_unif.py`、`_s6_bis.py`（flat 端 Q(a) 与 40 次二分）；`_s6_comb.py`（梳状端 a = 0.55/0.56/0.57/0.58）；`_s6_smooth.py`（抛物/余弦核对照）。

### 增量㉛（2026-11-23）：① 的答案——它不是「最坏情况界」而是无条件恒等式；类内极小 1.3275 由 CCLM 封顶，7/8 在受证类内被定理排除（撤回 μ₁ 与 λ\*）

- **问法先纠**：原问题「最坏情况上界能否写成一般 λ 的形式」隐含「存在一个随 λ 变化的界」。原文否掉这个隐含：Lamzouri（arXiv:2609.02882v1，2026-09-02，14 页）Lemma 3.1 = BGS（Acta Arith. 214 (2024) 357–376；arXiv:2306.04799）Lemma 5 是**等式**
  Σ_{0<γ,γ'≤T} K(δΔ)·w(Δ) = (T/2π)·logT·( f(0) + 2∫₀¹ α f(α)dα + O(1/√logT) )，w(z) = 4/(4−z²)
  去权（Lemma 3.2：把核换成 r_{δ,T} = Q_δ − Q_δ''/(4(logT)²)，因 Q_δ''^(z) = −4π²z²K_δ(z)²，正好抵掉 w）后常数不变，得
  **C_η = Q(0) + 2∫₀¹ α Q(α) dα，Q = f\\*f，f = η² ≥ 0、∫f = 1、supp f ⊂ (−λ,λ)** ——Lamzouri 式 (3.1)。
  故对每一支可容许核，配对和的值是被**钉死**的；「最坏情况」在 2λ ≤ 1 内是空概念。
- **可用域（硬墙的位置变了）**：supp Q ⊂ [−1,1] ⟺ 2λ ≤ 1 ⟺ Montgomery 的 α ≤ 1 段。λ > 1/2 时恒等式失效，缺的是 α > 1 段的配对相关（等价于 α>1 的 Montgomery 猜想）——不是缺技巧，是缺公开定理。前置条件还有：f 实偶、在 0 处 Lipschitz（η_ε 正则化就是为此）。
- **两个锚点机检（决定性，`_ceta_check.py`）**：自相关走 |FFT|²，dx = 2⁻¹⁸、滞后 [−1,1] 无回绕、f 定义在 [−4,4] 承载窗内。

  | 核 | Q(0) | J = 2∫₀¹αQ | C_η 实测 | 判定 |
  |---|---|---|---|---|
  | f ≡ 1（经典 Montgomery） | 1.0000038 | 0.3333371 | **1.3333410** | 4/3，差 +7.6e−6 ✓ |
  | f₀（Montgomery–Taylor） | 1.0061298 | 0.3213753 | **1.3275051** | C_MT = 1.3274992963，差 +5.8e−6 ✓ |
  | cos(2v₁x) 按 ∫f = 1 归一 | 1.0141047 | 0.3149594 | **1.3290640** | ≥ C_MT ✓（CCLM Cor.14 成立） |

  第二行把「C_MT 就是 f₀ 在这个泛函下的值」钉住（此前只当它是「已知常数」，没对过表）；第三行把 μ₁ 那条路判死。
- **撤回 μ₁ = 0.6755169434（㉙）**：该特征方程解的是「max ⟨f\\*f,Γ⟩ / ‖f‖₂²，supp ⊂ [−1/2,1/2]」，约束是 ‖f‖₂ = 1；而 C_η 的合法约束是 ∫f = 1、f ≥ 0。换归一化就换极值点：cos(2v₁x) 按 ∫f = 1 归一后 C_η = 1.3290640 > 1.3274993，极小仍由 f₀ 取得。**不是我们赢了 0.003，是解错了问题**。原式 μ₁ = 1/(2v₁²) = 1/(2·0.8603335890193798²) 的算术无误，但已无归属。
- **撤回 λ_eff\* ≈ 1.124–1.150（㉚）**：它由 A = 1 + ∫₀^∞ ρ₂|f̂|²du（ρ₂ = 1 − sinc² 是**猜想**）+ 单边模型得出。定理口径的 7/8 门槛是 C ≤ 1.125（A_s6 ≡ C_η，无因子 2），与类内极小 1.3275 差 15% ⟹ 该「临界支撑」落在受证类极小值之下，是**不可达区**，不是「精度不够」。同时撤「λ 增大就能救」：λ 增大 ⟹ K 变窄 ⟹ 计入的对数变少 ⟹ C 反向趋 1（极端 f 摊到 [−λ,λ] 给 C ≈ 1/(2λ) + 1 → 1，界退化为空话）；二次矩的强度在 λ = 1/2 取极大，与 CCLM 的最优性同向（此段为同机制连续外推，**属推断**，λ > 1/2 无定理）。
- **归一口径精确化（㉘ 的悬案闭合，并更正我上一段的错误说法）**：
  - **S6 侧是有序对，无因子**：`pair_hist`（脚本第 63–74 行）对每个零点取 `z−half … z+half` 两侧邻点、只滤掉 `ds ≤ 1e−12` 的自身项 ⟹ 每个无序对被记两次 ⟹ `A_s6 = 1 + Σ_{有序 z≠s}K²/N = Σ_{全部配对}/N ≡ C_η`。**故 A_s6 与 C_η 是同一个数，此前写的「C = 2A − 1 适用于 S6」是错的，撤回。**
  - **只有连续模型是单边**：A_model = 1 + ∫₀^∞ρ₂(u)|f̂(u)|²du 只积 u > 0 半边，ρ₂ 偶 ⟹ A_model = (C_η + 1)/2 ⟹ **C_η = 2A_model − 1**。两个锚点校核：flat 模型 1.16667 ⟹ 1.33333 = 4/3 精确 ✓；f₀ 模型 1.162882 ⟹ 1.32576（对 1.3275 差 0.13%）✓。
  - **实测与定理差 12%，未闭合**：S6 实测（f₀ 核）1.1868 按有序对读应等于 C_η = 1.3275，缺口 0.141（12%）。候选解释：零点表不全（本地 npz 缺失，数据在另一台机）、half = 40 对 1/u 型尾巴的截断、ζ 与 L 混族的 N 归一（nz / nl / N_K）。**此前「模型与实测差 2.0%」是拿单边模型对有序实测造成的假吻合，撤回。** 【**㉜ 已闭合**：表在本机、且完整（N(8×10⁵) = 1,369,279 对 RvM ✓）；截断已排除（H = 40 → 400 只差 0.0016）；主因是 δ 口径（logT/2π 应为 log(T/2π)/2π，影响 0.0823 = 58%），其次全局 δ 与 bin 的复合（0.0371 = 26%），残差 0.0195（1.5%）为有限 T 效应。修正后 A 饱和 1.3078，与 C_MT 差 1.5%。见增量㉜。】
- **结论（7/8 判决，与㉚ 同向、理由换硬）**：受证类（2λ ≤ 1）内 C_η 的极小 = C_MT = 1.3274992963（f₀ 取得），且 CCLM（Carneiro–Chandee–Littmann–Milinovich, J. Reine Angew. Math. 725 (2017) 143–182, Cor. 14；极值函数即 Montgomery–Taylor 1974）证明该类内**不能再小**。7/8 需 C ≤ 1.125（A_s6 ≡ C），**缺口 15%，是定理级排除，不是「暂未证出」**。三条出路：α > 1（PPC / 强 Montgomery，即 S6 的 (H2′_λ) 超支撑）；换非二次矩类泛函（Remark 3.3 已判：Claude 的矩阵路线 arXiv:2608.13637 Thm 5.7 与 Lamzouri 同归 Montgomery–Taylor 极值问题，**换装不换核**）；引入类外信息（素数侧 / BGS 余项 —— 正是 QRH 的入口）。
- **形式化意义（账本不变，语义变真）**：axiom 7 / opaque 2 / 明账 1 不变（本轮零代码、零 Lean 改动）。但 `bgs3_pair_expansion` 的身位变了：它不再是「配对和能拆三块」这条对一般核为假的组合恒等式，而可改写为 C_η 恒等式的具体语句（有 Lamzouri 定理支撑，带 O(1/√logT) 余项）。真正可形式化的硬核是 **Prop 2.1 本体**：λ > 0、η ∈ L²(ℝ) 实偶、supp η ⊂ (−λ,λ)、η²̂(0) = 1 ⟹ #(单重实元) ≥ 2#Z − Σ_{z,s}K(z−s)²、#(互异元) ≥ (3/2)#Z − ½Σ_{z,s}K(z−s)²（K := η²̂）；证法是 L²((−λ,λ)) 上三层嵌套 Gram–Schmidt（U ⊂ V ⊂ W）+ Bessel + a²+1 ≥ 2a、a²+4 ≥ 4a，α_j 求和恰好塌缩成 #Z。**注意它不是非负核论证**——这正是它能脱离 RH 的原因。mathlib 侧有件（L² 内积、Bessel、有限维 Gram–Schmidt、Finset 求和），是唯一能把「配对不等式」从 axiom 变真定理的入口。
- **文献锚点与对照件**：`https://arxiv.org/html/2609.02882v1`（Prop 2.1 (2.4)(2.5)、Lemma 3.1/3.2、Remark 3.3/3.4、Thm 1.1、附录 A）；BGS `https://arxiv.org/abs/2306.04799`；形式化对照件 `https://github.com/AxiomMath/ZetaZeros`（AxiomProver 对 Prop 2.1 + Thm 1.1 的机检证书，前提是 BGS Lemma 5 + Riemann–von Mangoldt）。Theorem 1.1：C₀ = 3/2 − (1/√2)cot(1/√2) = 0.6725007…，C₁ = (C₀+1)/2 = 0.83625…；摘要给的「simple 或在线 ≥ 88.76%、两者平均 ≥ 83.62%」是 Claude 版本之外的新增估计。
- **判据补第 ⑤ 项（进审计台）**：**「恒等式 vs 界」的类别**——凡声称「最坏情况上界」者，先问它在给定类内是等式还是不等式；若是等式，则「最坏」二字无内容，且等式的适用域本身就是硬约束。本轮三连撤（0.8435 → 4/3/μ₁ → λ\* 1.13）都栽在「拿一个等式或一个别的泛函当界用」。
- **证据**：`_ceta_check.py`（本机纯数值，未 Lean 机检；三行输出见上表）＋ Lamzouri HTML 全文（一次读完 11206 tokens，含 Prop 2.1 完整证明与 App. A 描述）。

### 增量㉜（2026-11-23）：12% 钉死——截断不是元凶，δ 口径是主因；并拿到 C_η 的初等 Fourier 表示（回收「ρ₂ 是猜想」那句）

- **数据先体检（推翻㉛ 的「本地 npz 缺失」）**：表在本机，早前误判为另一台机。目录 `…\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter`：`zeros_T6e5.npz`（keys `zeta` 999,492 条 [14.1347, 6e5] / `L` 1,150,050 条）、`zeta_T800000.npz`（`zeta` **1,369,279** 条 [14.1347, 799999.7]，对 RvM 预测 1.3694×10⁶ ✓ ⟹ 表完整）、`L_D5_T800000.npz`（1,570,290 条），另有 T40000/100000/200000/400000 分级表。**「表不全」这条候选解释当场排除。**
- **half 扫描（`_s6_halfscan.py`；ζ 于 8×10⁵ 取 [7.2e5, 7.95e5] 带内 8,215 个中心零点，partner 取全表，δ = δ_loc = 1.869787，H 掩码一次扫完，3.1 s）**：

  | H（归一单位） | A 实测 | GUE 参考 1+2∫₀^H(1−sinc²)K²du | g≡1 参考 1+2∫₀^H K²du |
  |---|---|---|---|
  | 2 | 1.274190 | 1.293528 | 1.972006 |
  | 5 | 1.294211 | 1.313665 | 1.992329 |
  | 10 | 1.301072 | 1.320559 | 1.999236 |
  | 20 | 1.304511 | 1.324022 | 2.002701 |
  | 40 | 1.306230 | 1.325756 | 2.004435 |
  | 80 | 1.307096 | 1.326623 | 2.005302 |
  | 400 | 1.307788 | 1.327317 | 2.005996 |

  **判决：H = 40 → 400 只涨 0.0016（A 的 0.12%、超出 1 的部分的 0.5%）⟹ 截断在 H ≈ 40 已饱和，不是 12% 的原因。** 附带：实测曲线与 GUE 参考曲线全程平行（间隔恒 0.0195–0.0197），而 GUE 参考在 H → ∞ 收敛到 **1.327317 ≈ C_MT（差 0.02%）** ⟹ 定理常数与「典型值」在该类内是同一个数（见下条恒等式）。
- **δ 对表（H = 40，同一批 i）**：δ_S6 = log(8e5)/2π = 2.162295 给 **A = 1.223878**；δ_loc = log(8e5/2π)/2π = 1.869787 给 **A = 1.306230**。比值 1.1564 = log T / log(T/2π)。**用错 δ 把「超出 1」的部分压掉 27%。**
- **0.141 的四项拆分（算术闭合到 1e−4）**：

  | 环节 | 增量 | 占比 |
  |---|---|---|
  | S6 原值 1.1868 → 带内 + δ_S6 的 1.2239 | +0.0371 | 26% |
  | → δ 换成真实间距密度（1.2239 → 1.3062） | +0.0823 | 58% |
  | → half 40 → 400（截断） | +0.0016 | 1% |
  | → C_MT 1.3275（残差） | +0.0195 | 14% |

  0.0371 这块是**复合效应**（全表 vs 带内 + 全局 δ 覆盖 [14, 8e5] + 直方图 binw = 0.02），未逐项分离；方向更正：全局 δ 使低零点区的 u 被放大（δ_loc(14) = 0.1276 而 δ_S6 = 2.162，差 17 倍）⟹ 低区配对被压成 0 ⟹ **A 被拉低**（此前叙述成「过度拉伸」，方向说反了，此处更正）。
- **T 依赖（`_s6_Tscan.py`，H = 200 饱和，δ_loc，每档 4–5 千个 i，4.3 s）**：

  | 表 | N_ζ | i 数 | δ_loc | A | 亏（C_MT − A） |
  |---|---|---|---|---|---|
  | zeta_T40000 | 49,395 | 5,265 | 1.392398 | 1.299265 | 0.0282 |
  | zeta_T100000 | 138,067 | 4,849 | 1.538232 | 1.305176 | 0.0223 |
  | zeta_T200000 | 298,196 | 4,456 | 1.648550 | 1.310277 | 0.0172 |
  | zeta_T400000 | 640,518 | 4,161 | 1.758868 | 1.306050 | 0.0214 |
  | zeros_T6e5 | 999,492 | 4,142 | 1.823400 | 1.303676 | 0.0238 |
  | zeta_T800000 | 1,369,279 | 4,044 | 1.869186 | 1.303925 | 0.0236 |

  噪声探针（同表、i 抽样错开一位）：1.303925 vs 1.306071，差 **0.0021** ⟹ 亏在 0.017–0.028 之间波动、无单调趋势；量级与 Lemma 3.1 的 O(1/√logT) 相符（系数 ≈ 0.055），但 log T 只从 10.6 走到 13.6，**不足以分离「1/√logT」与「1/logT 型归一差」两种解释**。结论写成：**残差 0.0195（占 A 的 1.5%、占超出部分的 6%）= 有限 T 效应，本机表已到分辨极限，不再往下追。**
- **顺手拿到的东西：C_η 的初等 Fourier 表示（这是本轮真正的数学收获）**

  **C_η = 1 + ∫_{-∞}^{∞} ρ₂(u)·K(u)² du，ρ₂(u) = 1 − sinc²(πu)，K = f̂。**

  四步推导（全部初等，无零点、无 RH、无猜想）：
  1. sinc²(πu) = Ĉ[Γ]，Γ(x) = max(0, 1−|x|) —— **这一步就是已机检的 A4（`fourierCos triKer`）**，符号约定差 2π：∫₋₁¹(1−|x|)cos(2πux)dx = sinc²(πu)；
  2. 余弦变换 Parseval：∫₀^∞K·G du = ½∫f·g dx ⟹ ∫₀^∞ sinc²·K² du = ½∫Γ·(f\\*f) dx = ∫₀¹(1−α)Q(α)dα；
  3. ∫₀^∞Q du = ½∫_{-∞}^{∞}Q = ½·Q̂(0) = ½·K(0)² = ½（因 ∫f = 1）；
  4. 2∫₀^∞ρ₂K² = 2∫₀^∞K² − 2∫₀^∞sinc²K² = Q(0) − 2∫₀¹(1−α)Q dα = Q(0) + 2∫₀¹αQ dα − 1 ⟹ 移项即得。

  两个锚点对表（与 `_ceta_check.py` 的独立路径一致）：flat（Q = Γ）给 1 + (1 − 2/3) = **4/3 精确**；f₀ 给 **1.327317**（H = 400 截断值），H → ∞ 即 C_MT = 1.3274993。**故「GUE 参考曲线收敛到 C_MT」不是巧合，是恒等式在两端的同一句话。**
- **回收「ρ₂ = 1 − sinc² 是猜想」这句话（㉚ 与㉛ 各出现一次）**：**ρ₂ 在这里不是关于零点分布的猜想，而是恒等式里的一个 Fourier 核**——上式对任何 f ≥ 0、∫f = 1、supp f ⊂ (−λ,λ) 都成立（推导只用 ∫f = 1，未用任何零点统计）。真正失效的不是 ρ₂，而是 **C_η 本身**：λ > ½ 时 supp Q ⊄ [−1,1]，Lemma 3.1 的恒等式不再成立，`1 + ∫ρ₂K²` 仍是一个合法的数，但不再是配对和的值。**所以 ㉛ 撤回 λ_eff\* 的理由应改写成「λ > ½ 无定理」，而不是「ρ₂ 靠猜想」。** 被撤的只有两件：单边计数（模型 → 实测要 2A − 1）与 λ > ½ 的外推。
- **A4 的身位因此回升**：它不再只是「口径 B 的预备件」，而是**恒等式第 1 步的机检叶子**。若日后要把这条恒等式形式化，链条是 A4（已机检）+ cos-Parseval（mathlib 未必有）+ ∫Q = ½·K(0)²（Q̂ = K² 的卷积定理）——属独立一件活，**未机检**，本节所有推导均按解析论处。
- **口径警示（Lean 侧零改动，只加注释）**：`S7_1_Main.lean:38` 与 `:57` 的 docstring 写 `δ = logT/(2π)`，这是照 S6 脚本抄的**历史口径**；真实平均间距密度是 `log(T/2π)/(2π)`，两者在 T = 8×10⁵ 处差 **15.6%**。`pairConstant` 的 δ 是**参数**（`:60`），故代码语义不受影响——但**只要把 A 的值与真实零点对表，就必须用 δ_loc**。建议在这两行各加一句：`（δ 的物理值 = log(T/2π)/(2π)；本语句不固定 δ，见增量㉜）`。**此改动涉及注释表述，按用户规矩需拍板，本轮未动。**
- **账本**：零 Lean 改动、零 axiom 变化（7 axiom / 2 opaque / 明账 1）；本节全部结论为**纯数值 + 解析推导，未 Lean 机检**。
- **证据**：`_z_inspect.py`（表体检，含 RvM 计数对照）、`_s6_halfscan.py`（half 扫描 / δ 两口径 / GUE 与 g≡1 参考；含 `rfft` 相位 bug 修正：`(−1)^k`）、`_s6_Tscan.py`（T 表 + 噪声探针）；零点表见上列目录。


### 增量㉝（2026-11-24）：把 (i) 从「要证的恒等式」降成「定义」——A 线未证内容压成一条不等式 `DiagRate`；并定性：(i) 打不下 Abel 求和

- **这一刀（第十一刀；Lean 已编译 3836 jobs 全绿、已出探针）**：`pairConstant = diag + prime/N + E/N` 这条「配对分解恒等式」对**任意实数**都成立（`diag` 自由），本身不含数学内容；此前把它和「对角项 C_MT + O(1/logT)」一起塞进 `BGSDecompositionCore` 的 `∃ diag`，形成一条废话与一条真率的混合账，谁也看不清未证的是哪半。改法：
  - 新增**真定义** `diagTerm T := pairConstant triKer (physDelta T) (N_L T) (zerosLChi5UpTo T) − primeSum triKer (physWindow T) (physDelta T)/N_L T − offCriticalError T/N_L T`；
  - **删除** `BGSDecompositionCore`，换成单句 `DiagRate := ∃ C₁ ≥ 0, ∀ᶠ T, diagTerm T ≤ C_MT + C₁·(log T)⁻¹`；
  - `DiagRate_to_uniform : DiagRate → BGSLocalUniform`（**真证**：恒等式按 `diagTerm` 定义展开 + `ring`，素数槽由第十刀 `prime_normalized_le` 供出，常数 `2π·e^{2π}/NLc` 显式）；
  - `s71_main_tail_core` 更名 `s71_main_tail_diag`（只条件于 `DiagRate`）。
- **账本变化（A 线）**：S7.1 的未证内容从「配对恒等式 + 对角率 + 素数界」三件压成**一件**——`DiagRate`。`bgs3_pair_expansion` 不在尾部形状的依赖闭包里：它现在只是点形式 `s71_main` 自己的前件（A 的固定 T 形状需要它，尾部形状不需要）。
- **探针原文（`_probe_g1b.lean`）**：

  ```
  QRH.diagTerm              : [propext, Classical.choice, Quot.sound]
  QRH.DiagRate_to_uniform   : [propext, Classical.choice, N_L_lower_bound, Quot.sound]
  QRH.s71_main_tail_diag    : [propext, Classical.choice, N_L_lower_bound,
                               bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]
  ```

- **定性（本轮主要产出）：(i) 不能用 Abel 求和拿下。** 三个理由，逐条都是硬的：
  1. **作用域不对**。Abel 求和只把 Σ aₙbₙ 改写成部分和加权（同一个序列内部换写法），它不改变「被求和的对象是什么」。而 (i) 要把 Σ_{有序零点对} K(δ·Δγ)² 改写为「对角 + 素数和」，是**换掉了求和对象**（零点 → 素数幂），Abel 一步都不跨这一步。
  2. **(i) 的实质是二阶矩 Weil 显式公式**。链是这样的：把配对和对核求 Fourier（Plancherel/Parseval）⟹ 得到 ∫ K̂²·ρ₂ 型量 ⟹ 用显式公式把零点侧的求和换成素数侧 ⟹ 在 α ≤ 1 段算出 form factor = 1 +（素数项）⟹ 拆出 diag 与 prime。这正是 BGS 引理 3（Acta Arith. 214 (2024) 357–376）的内容，且它**只在 α ≤ 1**（λ 受限）成立——与我们 7/8 出局、λ 阈值那套完全咬合。
  3. **手上的零件是一阶矩，不够**。`landau_explicit_L` 给的是「一阶」：Σ_ρ x^{ρ−r}/(ρ−r) = trivial − Σ_n Λ(n)χ(n)n^{−r} − logDerivTerm。 (i) 需要「乘起来」的矩（乘积求和 ⟹ 二次型），二者之间缺的正是 Plancherel 与对相关密度这两件；`fourierCos` 那一族已因 `fourierCos_Khat` 假、`bgs5_khat_fourier_supp` 空话被撤，等于零件也没有。**所以 (i) 的正确登记不是「缺一条组合恒等式」，而是「缺二阶矩显式公式模块（含 triKer 的 K̂ 与对相关密度」**——月份级工程量，不是一刀能收的。
- **数值旁证（triKer 口径实算，只作旁证，不作定论）**：窗口法全表、δ = log(T/2π)/(2π)、K = triKer（支撑 |u| ≤ 1）、排除自配对、归一用 N_L，取 T = 8×10⁵：

  | 表 | 零点数 | N_L | A = pairConstant | C_MT − A |
  |---|---|---|---|---|
  | `zeta_T800000` | 1,369,279 | 1,369,304 | 1.119396 | 0.208103 |
  | `L_D5_T800000`（χ₅） | 1,570,290 | 1,369,304 | 1.188930 | 0.138570 |

  **三条警示必须随表走**：① `N_L` 在 Lean 里是**抽象参数**（只知 `NLc·T·logT ≤ N_L T`），本表用 ζ 的解析主项代入，代数上不是 Lean 的 `N_L T`（换成 χ₅ 自己的主项 A 会更低）；② 本表与**㉜ 的 1.3039/1.3062 不可并表**——㉜ 的核是 f₀（K = f̂）、截断 H = 200、归一是「除以带内中心点数 i」；本表核是 triKer、截断等价 H = 1、归一是「除以 N_L」；③ 结论只取**「富余」这一定性**：三种代入都给 A ≪ C_MT，故「数值上 `DiagRate` 宽松」这个判断对归一选择不敏感，但**具体数值不可作定论**。
- **本轮新暴露的风险点（下一轮必须核清）**：`s71_main` 的 A 用 **triKer**（支撑 |u| ≤ 1），而 `C_MT = 1.3274993` 出自 **f₀/λ-族**的类内极小（㉛，CCLM 封顶）。数值上 triKer 口径的 A 只有 1.12–1.19，距 C_MT 留 0.14–0.21 富余 ⟹ 「A ≤ C_MT」里有多大比例是**被更窄的核买下**的，而不是数学内容，目前分不清。两条出路：把 C_MT 换算到 triKer 族（即重解一次类内极小），或把主定理的核整体换成 f₀。**在核清之前，`s71_main` 的结论不能对外当「配对和 ≤ 1.3275」读。**
- **证据**：`_diag_numeric.py` + `_diag_numeric.txt`（T = 2e5/4e5/8e5 三档）、`_diag_cross.py` + `_diag_cross.txt`（ζ 与 χ₅ 同口径对表）、`_probe_g1b.lean`（6 条）。
- **账本**：axiom 7 条不变（`landau_explicit_L` / `siegel_walfisz_chi5` / `pair_count_bound` 仍未接通）、opaque 2 条不变；`BGSDecompositionCore` 从 def 表中消失，`diagTerm` / `DiagRate` 新入表。**本节数值部分为纯 Python，未 Lean 机检。**

### 增量㉞（2026-11-24）：A-R1 结案——核与密度错位；主链换 `sincKer`、常数换 `C_FLAT = 4/3`（第十二刀）

- **A-R1 判决（核层，非界层）**。Lamzouri/BGS 的类约束的是**密度 f**（f = η² ≥ 0、∫f = 1、supp f ⊆ (−λ,λ)，核 **K := f̂**），恒等式 `C_η = Q(0) + 2∫₀¹ αQ(α)dα`（Q = f\*f）只在 **2λ ≤ 1** 成立。据此三条：
  1. **`triKer` 作 K 不合法**。它的逆变换 f = sinc² 型，**无紧支撑**，既非 η² 形式也不满足 supp 条件 ⟹ 不在类内。旧值 A = 1.119396（ζ）/ 1.188930（χ₅）**不属于任何文献常数**，是类外数字。
  2. **`triKer` 作 f 则超域**。f = Γ（λ = 1，2λ = 2 > 1）⟹ 恒等式失效，理论常数不存在；对应 K = sinc²(πu)，实测 1.085822，同样无主。
  3. **受证域内的正确答案**：λ = 1/2 的 flat 支 f ≡ 1 ⟹ K = sinc(πu)，`C_η = Q(0) + 2∫₀¹α(1−α)dα = 1 + 1/3 = 4/3`（精确）。故 **C_MT 只属于 f₀ 那一支**；在 triKer/flat 两族里 `A ≤ C_MT` 不是「紧」，是「错对象」。
- **数值对表（T = 8×10⁵、ζ 表 1,369,279 零点、全表窗口法、除 N_L）**：

  | 核 | 对应 f | λ | 实测 A | 理论 |
  |---|---|---|---|---|
  | `sincKer`：sinc(πu) | f ≡ 1（flat） | 1/2 **受证域** | **1.266513** | 4/3 = 1.333333（差 −5.0%） |
  | sinc²(πu) | f = triKer | 1 超域 | 1.085822 | 无 |
  | `triKer` | f 无定义（逆变换无紧支撑） | — | 1.119396 | 无 |

- **⚠ 新登记：朴素求和口径有约 5% 系统偏差**。受证域 flat 支实测 1.2665 vs 定理 4/3 差 5.0%，而 ㉜ 的 f₀ + H = 200 + 除 i 数口径只差 1.5%。【**㉟ 已更正**：根因**不是**缺 w 去权（本节下半句原判断错误）。核对原文后确认 Σ K² 本身就是「去权后」的量（无权重），w 只出现在 Lemma 3.1 的**加权**形式（核 K 一次、带 w）；真正的根因是 **δ 全局化**，局部化后残差降到 1.5%。见增量㉟。】原判断留档：结论是**本口径只能定性（"富余"判断），不能做定理级判断**；这段在 ㉝ 的旁证表上同样适用，两表的"富余"一词都不许升级成证据。
- **第十二刀改动（Lean，已编译 3836 jobs 全绿、已探针）**：
  - 新增 `sincKer u := Real.sinc (π u)`、`sincKer_zero`、`sincKer_abs_le_one`（mathlib `Real.abs_sinc_le_one`）、常量 `C_FLAT : ℝ := 4/3`（§2.1a′，附 A-R1 结案说明）；
  - 主链换核换常数：`bgs3_pair_expansion`、`pair_sum_expansion`、`s71_main`、`BGSLocalUniform`、`diagTerm`、`DiagRate`、`DiagRate_to_uniform`、`primeSum_abs_le_floor`、`prime_normalized_le`、`s71_main_tail`、`s71_main_tail_diag`、`QRH.lean` 两条自检 example；
  - `KernelAdmissible` / `triKer_admissible` **降级为历史件**（该谓词把"可容许"定义成 K 自己紧支撑，与 Lamzouri 的密度类不同；`sincKer` 不满足它，主链不经过它），docstring 已记明"勿再用于新陈述"；
  - `triKer` 那一族 Abel/Lipschitz 引理**原样保留**（只服务 old-chain，不进新链）。
- **探针（`_probe_g1c.lean` 原文）**：

  ```
  sincKer                 : [propext, Classical.choice, Quot.sound]
  primeSum_abs_le_floor   : [propext, Classical.choice, Quot.sound]
  prime_normalized_le     : [propext, Classical.choice, N_L_lower_bound, Quot.sound]
  diagTerm                : [propext, Classical.choice, Quot.sound]
  DiagRate_to_uniform     : [propext, Classical.choice, N_L_lower_bound, Quot.sound]
  s71_main                : [propext, Classical.choice, N_L_lower_bound, bgs3_pair_expansion,
                             bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]
  s71_main_tail           : [propext, Classical.choice, N_L_lower_bound,
                             bgs4_offcrit_high, bgs4_offcrit_low, Quot.sound]
  s71_main_tail_diag      : 同 s71_main_tail
  ```

  **账本不变**：axiom 7 / opaque 2；`triKer` 族引理一条未删。
- **代价与收益记账**：界从 1.3274993 松到 1.3333333（**+0.44%**），换来「核合法 + λ ∈ 受证域 + 常数有定理 + 阈值常数是精确有理数」。这是**口径修正**，不是假设升级也不是减弱：旧陈述的对象本身不属于任何受证类。
- **遗留两件**：
  1. **要回到 C_MT 就必须引入 f₀ 的显式核**（Montgomery–Taylor 极值函数的 f̂），那是超越表达式，工程量约为本次的三四倍；届时 `sincKer → f₀Ker` 属增量替换，不返工。
  2. **数值口径要补 w(z) 去权**，才能把 5% 系统偏差消掉、与定理逐字对齐（`_ar1_kernel.py` 里加权重 `4/(4−z²)` 或按 Lemma 3.2 换核）。
- **证据**：`_ar1_kernel.py` + `_ar1_kernel.txt`（三支核同表对算，26.7 s）、`_diag_numeric.py` / `_diag_cross.py`（㉝ 的旧表）、`_probe_g1c.lean`（10 条）、`lake build QRH` 3836 jobs。

### 增量㉟（2026-11-25）：w(z) 核对完毕——它不该被「补」，真正缺的是 δ 的局部化（残差 5% → 1.5%）

- **原文（Lamzouri arXiv:2609.02882v1 §3，逐字核对）**：`w(z) = 4/(4−z²)`，此处 z = ρ − ρ'（纯虚）⟹ z² = −Δ² ⟹ **w(Δ) = 4/(4+Δ²)**，等价写法 `w(ρ−ρ') = (1 + π²ζ²/(logT)²)⁻¹`，ζ = Δ·logT/2π。
  - **Lemma 3.1**（= BGS Lemma 5）：`Σ_{0<γ,γ'≤T} f̂(i(ρ−ρ')logT/2π) · w(ρ−ρ') = (T/2π)logT · ( f(0) + 2∫₀¹ αf(α)dα + O(1/√logT) )`。**核是 f̂ 的一次方，带 w**。
  - **Lemma 3.2**（去权）：取 `r_{δ,T} = Q_δ − Q_δ''/(4(logT)²)`；由 `Q̂ = K²`、`Q_δ''^(ζ) = −4π²ζ²K²` 得 `r̂ = K²(1 + π²ζ²/(logT)²) = K²/w` ⟹ 与 w 相乘抵消 ⟹ **`Σ K²` 是无权重形式**。
- **结论一：`pairConstant` 的 `Σ K(δΔ)²` 就是 Lemma 3.2 的去权结果，本来没有权重可「补」。** 把 w 加进去反而错（那变成 Lemma 3.1 的加权量，核只该一次方）。此前「补 w 去权」的说法是把两个引理搞混——㉞ 已就地更正。
- **实算四格（ζ 表 T = 8×10⁵、6000 个均匀抽样中心 `γ ∈ [2.4e4, 7.85e5]`、partner 全表、除中心数）**：

  | 口径 | 核 | 权重 | δ = 2.1633（T 处） | δ = 逐点 δ_i | 理论 | 差 |
  |---|---|---|---|---|---|---|
  | 去权式（Lemma 3.2 = `pairConstant`） | sinc² | 无 | 1.19739 | **1.31200** | 4/3（Q̂=sinc² ⟹ f=Q 三角） | −0.0213（−1.6%） |
  | 加权式（Lemma 3.1） | sinc | 4/(4+Δ²) | 1.09877 | **1.23486** | 5/4（f=矩形 ⟹ 1+2∫₀^{1/2}αdα） | −0.0151（−1.5%） |

- **结论二：两个常数 4/3 与 5/4 不矛盾，属不同测试函数。** 去权式的核 sinc² 是「f = Q = 三角」的 f̂，常数 Q(0)+2∫₀¹αQ = 1+1/3 = 4/3；加权式的核 sinc 是「f = 矩形」的 f̂，常数 f(0)+2∫₀¹αf = 1+1/4 = 5/4。**两式残差同为 1.5%**，且与 ㉜ 的 1.5% 同量级 ⟹ 这是有限 T 残差（本机表极限），不是口径错误。
- **结论三（更正 ㉞）：5% 的根因是 δ 全局化，不是 w。** δ 是 γ 的函数：N'(γ) = (1/2π)log(γ/2π)，表内从 δ(2.4e4) = 1.311 到 δ(7.85e5) = 1.868。用 T 处的单值 δ 对全段求和，低端零点的 u = δΔ 被放大约 65% ⟹ sinc² 被压掉 ⟹ A 系统性偏低。改**逐中心 δ_i = log(γ_i/2π)/2π** 后，去权式残差 0.0645 → 0.0213（**4.8% → 1.6%**），加权式同步收到 1.5%。
- **未闭合项 P-δ（登记，不许当已闭合）**：定理字面写 `z = Δ·logT/2π`（**不是** log(T/2π)/2π，两者差 15.6%）。在 δ = 2.1633 下两式分别给 1.19739 / 1.09877，**对不上常数（差 13%–15%）**；能在 1.5% 上对上的只有逐点 δ_loc。故「定理字面尺度」与「零点表实际间距」之间还差一层换算，其数学内容未定（候选：z 尺度、w 在 |Δ| ~ T 的尾部压制、0<γ,γ'≤T 的边界计数，三者的叠加）。**在 P-δ 解开之前，任何"实测 = 定理常数"的说法只许说"在 δ_loc 口径下差 1.5%"**。
- **顺手的负面结果**：δ 扫描（1.40–2.25，10 档，`_wz_scan.py`）显示朴素全表 + 解析 N_L 口径下 A = 4/3 出现在 **δ ≈ 1.66**——既非 2.1633 也非 1.8708，第三个可疑口径。这条单独记：**"调 δ 直到对表"不是对表**，只能说明该口径缺一个因子。
- **意义与限制**：数值工具从「只许定性」升级到「可做 1.5% 级定量」。限制未变：`N_L` 在 Lean 里仍是抽象量（只知下界）、表只有有限 T、局部 δ 只是唯象（无定理支撑）。**故仍不得作为定理证据**，但可以当作「常数选得对不对」的体检。
- **证据**：`_wz_lemma31.py`/`.txt`（两式 × 两 δ，17 s）、`_wz_local.py`/`.txt`（局部 vs 全局，6000 中心 < 1 s）、`_wz_scan.py`/`.txt`（δ 扫描，87 s）。
### 增量㊱（2026-11-25）：P-δ 结案——δ 不是「缺一层数学」，是「分母用错」；判据换成定理自己的误差带

**换判据（这一步是本增量的核心）**

㉟ 留的 P-δ 问的是「为什么 δ = logT/2π 对不上常数」。这个问法本身有问题：定理自带误差项 O(1/√logT)，在 T = 8×10⁵ 时 1/√log(T/2π) = 0.292，带给 A 的带宽是 ±(1/√logT)/3 = **±9.7%**（去权）/ ±7.3%（加权）。**在这个带宽里，「A 是否精确等于 4/3」是一个没有答案的问题。** 正确判据只有一个：A 是否落在定理自己的误差带内。

**四口径 × 五个 T 的判决（全表，δ 逐点/常数，W_u = 50）**

| δ 口径 | T=4e4 | T=1e5 | T=2e5 | T=4e5 | T=8e5 | 判 |
|---|---|---|---|---|---|---|
| D1 常数 logT/2π | 1.1670 | 1.1780 | 1.1862 | 1.1938 | 1.1975 | **出界 5/5** |
| D2 常数 log(T/2π)/2π | 1.2487 | 1.2549 | 1.2604 | 1.2653 | 1.2664 | 界内 5/5 |
| D3 逐点 log(γ/2π)/2π | — | — | — | — | **1.3139** | 界内 |
| D4 逐点 log γ/2π | — | — | — | — | 1.2255 | 出界 |

带下界 = 4/3 − (1/√log(T/2π))/3，T = 8×10⁵ 时 = **1.2361**。**D1 在全部 5 个 T 上都低于下界** —— 它不是「差一点」，是**根本不在定理允许的读数范围内**。**结论：δ = logT/2π 不是合法刻度，用它读数得到的 13–15% 不是「缺一层换算」，是读错了刻度。**

**15.6% 的解析来源（一句话）**：Lamzouri 的主项写成 (T/2π)logT，而真实零点数是 N(T) ≈ (T/2π)log(T/2π) − T/2π，两者相差 log(2π) = 1.838 在 logT = 13.59 里 = **15.6%**。δ 与分母是同一个 log 的两个投影：δ 用 logT，分母就得用 (T/2π)logT；δ 用 log(T/2π)，分母就用 N(T)。**混搭（δ 取主项、分母取真 N）必然把 A 推出误差带。**

**界内残差是纯 O(1/logT)，不是噪声**

| T | 1/log(T/2π) | 去权残差 | 残差·log | 加权残差 | 残差·log |
|---|---|---|---|---|---|
| 4e4 | 0.1142 | −0.0297 | −0.260 | −0.0225 | −0.197 |
| 1e5 | 0.1034 | −0.0260 | −0.251 | −0.0205 | −0.198 |
| 2e5 | 0.0965 | −0.0236 | −0.245 | −0.0191 | −0.198 |
| 4e5 | 0.0904 | −0.0218 | −0.241 | −0.0180 | −0.199 |
| 8e5 | 0.0851 | −0.0194 | −0.228 | −0.0161 | −0.189 |

**残差·log(T/2π) 在 5 个 T 上稳定到 2% 以内**：去权 ≈ −0.24，加权 ≈ −0.198（几乎正好 −1/5）。这是「有限高度项」，不是口径缺陷 —— 它随 T 增大单向收缩，且**改抽头、改截断深度（W_u = 25→400）都不动它**（W 扫描：−1.03% → −0.74%，到此封顶）。

**P-δ 关闭。三条结论**

1. **δ 必须逐点**（1/局部密度）。全局常数在低端荒谬：γ=14 处 δ/局部密度 = 5.8，sinc² 完全失相。分段诊断（δ 固定 2.1633）显示残差随 γ 单调塌缩：−32%（γ~14–300）→ −28% → −24% → −17% → −11.8%（γ~3e5–8e5），**没有一段在正确值上**。
2. **正确刻度 = log(T/2π)/2π**（常数）或 **log(γ/2π)/2π**（逐点），两者都在带内。5.8% 的落位差是 O(1/logT)，属定理允许范围。
3. **「精确复现 4/3」这个目标永久作废**。带本身有 ±9.7%，任何数值在 T = 8×10⁵ 都不可能「等于 4/3」而不越出其他口径。目标改为：**落在带内 + 预测带内位置**（后者已被 −0.24/log 律给出）。

**对 Lean 的直接含义（待拍板，非本次改动）**

`physDelta T = logT/(2π)` 与 `N_L T`（真零点数）是**异源搭配**：δ 取主项刻度、分母取真值。二者差 log(2π)/logT ≈ 15.6%，恰好把 A 推出误差带。所以「用 physDelta 去对表」在原理上永远差 5–6%，且这个差不会因为任何数值手段变小。

**已执行（2026-11-25 落地，第十三刀·纯新增）**：保留 `physDelta`（文献字面，`s71_main` 依赖它），**新增** `physDeltaRvM T := log(T/(2π))/(2π)` 与 `physWindowRvM T := exp(1/physDeltaRvM T)`，docstring 写明 15.6% 与「后者才是合法读数」。**不动 axiom、不动结论形状、不动任何已有陈述。**

**落地时捞到一条精确恒等式（比预想的强）**：
`physDelta T − physDeltaRvM T = log(2π)/(2π)`，**与 T 无关**，已形式化为 `physDelta_sub_physDeltaRvM`（零 axiom，真证，`Real.log_div` + `field_simp` + `ring_nf`）。

这条把 P-δ 的核心写成了定理，而不是「差一层换算」的叙述：两刻度之差是**绝对常数 0.2925**（T = 8×10⁵ 实测 2.16329 − 1.87079 = 0.29250 ✓）。它看起来像 15.6%，只是因为把 0.2925 除以了 logT = 13.59。**换句话说：15.6% 不是「随 T 变化的误差」，是「一个固定 0.2925 被越来越长的 logT 稀释」—— 这正是它对不上表、又「渐近无害」两句话的统一解释。**

**编译与探针（`_probe_pdelta.lean`/`.txt`）**

| 条目 | axiom 集 |
|---|---|
| `physDeltaRvM` | `[propext, Classical.choice, Quot.sound]` |
| `physWindowRvM` | 同上 |
| `physDelta_sub_physDeltaRvM` | 同上（**真证，零业务 axiom**） |
| `s71_main` | `N_L_lower_bound, bgs3_pair_expansion, bgs4_offcrit_high, bgs4_offcrit_low` + 三条基础（**账本 7 条不变**） |

`lake build QRH` 3836 jobs 全绿。（注：本刀使 `QRH.S7_1_Main` 的 job 数由 3824 起算，全量仍 3836。）

**续做的对表探针（§2.1a″，同样纯新增）**

把「换成同源刻度后落不落带」做成了 Lean 里可检索的对象，**与 `s71_main` 并列、不互相依赖**：

| 件 | 形 | axiom |
|---|---|---|
| `pairConstantRvM T` | `pairConstant sincKer (physDeltaRvM T) (N_L T) (zerosLChi5UpTo T)` | `[propext, choice, Quot.sound]` |
| `PairBandRvM T` | `\|pairConstantRvM T − C_FLAT\| ≤ (1/√log(T/2π))/3`（Prop，未证明，不加 axiom） | 同上 |
| `physDeltaRvM_le_physDelta` | `0 < T → physDeltaRvM T ≤ physDelta T`（真证） | 同上 |
| `physDeltaRvM_pos` | `2π < T → 0 < physDeltaRvM T`（真证） | 同上 |

**主链未受污染**：`s71_main` 与 `s71_main_tail` 的 axiom 集与探针加入前逐条一致（7 条 / 6 条，账本不变）。

`PairBandRvM` 的适用域是 `T > 2π`：否则 `log(T/2π) ≤ 0`，`sqrt` 退化成 0、右侧为 `1/0 = 0`，式子失去意义——这一点写进了 docstring，不靠注释兜。

行号：`::1266`（`physDeltaRvM`）、`::1269`（`physWindowRvM`）、`::1274`（恒等式）、`::1295`（`pairConstantRvM`）、`::1304`（`PairBandRvM`）、`::1308`/`::1318`（两条真证引理）。探针 `_probe_pdelta.lean`/`.txt`。

**证据**：`_pd_delta.py`/`.txt`（四口径矩阵 + 5 个 T 梯度，1 s）、`_pd_window.py`/`.txt`（分段诊断 + 局部窗口，2 s）、`_pd_trunc.py`/`.txt`（W_u = 25…400 收敛，1 s）、`_pd_noise.py`/`.txt`（抽样量 8k…100k，SE 判决）、`_pd_full.py`/`.txt`（全表 + T 梯度，18 s）、`_pd_band.py`/`.txt`（误差带判读）。


