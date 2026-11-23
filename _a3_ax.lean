import QRH

/-! 第七刀 A3 探针：三角核口径落刀后的闭包复核。

撤除对象：`fourierCos_Khat`（假命题）、`bgs5_khat_fourier_supp`（空话）。
替换物：`triKer`（`S7_1_Core` §4c）+ `triKer_admissible`；S7.6 全链 profile 换核。
本探针取六条关键件的公理集，重点看 `s71_main` 是否仍为 4 条用户 axiom。 -/

open QRH

#print axioms triKer_admissible
#print axioms primeSum_window_eq
#print axioms prime_sum_bound
#print axioms pair_sum_expansion
#print axioms bgs3_pair_expansion
#print axioms s71_main

/-- 支撑性：原 `bgs5_khat_fourier_supp` 的真替代（定义即得，非 axiom）。 -/
example (u : ℝ) (h : 1 < |u|) : triKer u = 0 := triKer_supp h

/-- 核可选性：`KernelAdmissible` 现在真的关于 K 有内容（不再硬编码 Khat）。 -/
example : KernelAdmissible triKer := triKer_admissible
