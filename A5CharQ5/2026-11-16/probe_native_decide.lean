import A5CharQ5.A5Defs

-- 探针：native_decide 能否闭合陪集等式（pA/pB 为具体置换时）
lemma probe_coset_a_11_decide : ∃ k : Fin 5, pA * cosetRep 11 = cosetRep 11 * pA ^ k.val := by
  native_decide

lemma probe_coset_b_7_decide : ∃ k : Fin 5, pB * cosetRep 7 = cosetRep 10 * pA ^ k.val := by
  native_decide

lemma probe_coset_b_8_decide : ∃ k : Fin 5, pB * cosetRep 8 = cosetRep 6 * pA ^ k.val := by
  native_decide

lemma probe_coset_b_11_decide : ∃ k : Fin 5, pB * cosetRep 11 = cosetRep 7 * pA ^ k.val := by
  native_decide

-- 若以上通过，则 24 条引理证明体均可一行 native_decide 收掉
lemma probe_all_24 : (∀ i : Fin 12, ∃ k : Fin 5, pA * cosetRep i = cosetRep (aTarget i) * pA ^ k.val) ∧
                    (∀ i : Fin 12, ∃ k : Fin 5, pB * cosetRep i = cosetRep (bTarget i) * pA ^ k.val) := by
  native_decide
