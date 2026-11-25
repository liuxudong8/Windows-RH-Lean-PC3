import QRH.S7_1_Main

open QRH

-- 第十三刀：口径备件
#print axioms physDeltaRvM
#print axioms physWindowRvM
#print axioms physDelta_sub_physDeltaRvM
-- 第十三刀续：对表探针（不接入主链）
#print axioms pairConstantRvM
#print axioms PairBandRvM
#print axioms physDeltaRvM_le_physDelta
#print axioms physDeltaRvM_pos
-- 主链未被污染
#print axioms s71_main
#print axioms s71_main_tail

#check @pairConstantRvM
#check @PairBandRvM
#check @physDelta_sub_physDeltaRvM
#check @physDeltaRvM_le_physDelta
#check @physDeltaRvM_pos
