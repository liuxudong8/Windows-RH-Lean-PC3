import BSD.GrHChain389

open BSD.GrHChain389

-- 环 4：由 axiom 降为定理，闭包应只剩两条区间锚点 + 算术（不含 omega_reg_min_bound_389 本身）
#print axioms omega_reg_min_bound_389

-- 分母正性
#print axioms omega_reg_pos_389

-- 锚点可满足性（排空链）
#print axioms anchor_consistent_389

-- 主链收口：GRH + 精细 BSD ⟹ #Ш ≤ 3
#print axioms sha_bound_three_from_chain

-- 主链收口：GRH + 精细 BSD ⟹ #Ш = 1
#print axioms sha11_one_of_grh_fine_bsd_389

-- 端到端：经 Main 的对外命题
#print axioms BSD.GrHChain389.sha11_one_of_grh_fine_bsd_389
