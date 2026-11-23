import OrderPreservingBijection.stage_4

-- 拆环后主链闭包核验：riemann_hypothesis 及其反证链
#print axioms RHSpectralDuality.riemann_hypothesis
#print axioms RHSpectralDuality.all_zeros_on_critical_line
#print axioms RHSpectralDuality.off_critical_line_contradiction
-- 拆环后的两个独立公理：计数上界 + 重数界（各挂一个 sorryAx，不互相牵连）
#print axioms RHSpectralDuality.zero_counting_estimate
#print axioms RHSpectralDuality.zero_multiplicity_log_growth
-- 真证层：farZero 加权和（P0.3，无 sorry）
#print axioms RHSpectralDuality.farZero_weighted_summable
-- 落点 A：GoldenInt 域迹分类（代数锚点，应零 sorry）
#print axioms GoldenInt.fieldTrace_mem_of_abs_lt_two
#print axioms GoldenInt.fieldTrace_eq_sum
-- ⑤ 拆环：continuousTerm_eq_zero 应零 sorry（挂账点在散射对数导数恒零）
#print axioms RHSpectralDuality.continuousTerm_eq_zero
#print axioms RHSpectralDuality.scatteringLogDerivative_eq_zero_of_compact
