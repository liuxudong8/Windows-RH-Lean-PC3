import QRH.S7_1_Core
import QRH.S7_1_Main
import QRH.S7_1_Stage3

/-!
# 攻防 XLII — S7.1 形式化证明（QRH 库根模块）

`L(s, χ_5)` 单族 BGS 型配对公式的形式化项目入口（C:\\proj2\\QRH，随 C:\\proj2 库编译）。

模块结构：
  - `QRH.S7_1_Core` —— 核常数件（C_MT、Khat 解析式、ε 正则化偏差；真证明件 + 少量 sorry）。
  - `QRH.S7_1_Main` —— 主定理 S7.1 骨架（显式公式 / Siegel–Walfisz / 配对展开 / 主定理陈述）。
  - `QRH.S7_1_Stage3` —— Stage 3+ 超支撑断层闭合（N1/N2/N3 结构件 + 四条真证明件：
    缩放支撑保持、f_ε 支撑、K̂_a 偶性、Abel 求和）。

构建：`lake build QRH`（mathlib 依赖已完成增量构建）。
-/

namespace QRH

/-- 项目自检：主定理陈述存在（由 `s71_main` 直接给出；2026-11-23 随 `bgs3` 口径手术
    同步：归一化分母为真实零点计数 `N_L T`，求和域为有限截断集 `zerosLChi5UpTo T`；
    **第五刀后**离线项已是具体项 `offCriticalError T / N_L T`，故额外要求阈值条件
    `offcritThreshold ≤ T`——「T 足够大」这一步现在是显式前提，不是藏在 ∃ 里）。 -/
example (T : ℝ) (hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (hbig : offcritThreshold ≤ T) (ε : ℝ) (hε0 : 0 < ε) :
    ∃ (C₁ C₂ : ℝ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      pairConstant sincKer (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)
        ≤ C_FLAT + C₁ * ε + C₂ :=
  s71_main T hT hweak hbig ε hε0

/-- 尾部形状自检：`A ≤ C_MT + o(1)`（2026-11-24 第九刀）——条件于 BGS 一致常数 `(U)`；
    离线项那个绝对 1 已被 `offcrit_remainder_eventually_small` 真证消化，故结论无 `+C₂`。 -/
example (hU : BGSLocalUniform) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, WeakRealPart T zerosLChi5 →
      pairConstant sincKer (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)
        ≤ C_FLAT + ε :=
  s71_main_tail hU ε hε

end QRH
