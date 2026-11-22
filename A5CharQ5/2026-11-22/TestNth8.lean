import Mathlib.Algebra.Group.Basic

-- 第七轮：b_8 合并步 + b_7 全链验证

-- T1：b8 1141：pA^2*pB*pA^3*pB*pB = pA^2*pB*pA^3*pB^2（合并 pB*pB，simpa [mul_assoc] 拆 RHS pB^2）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB*pA^3*pB^2 := by
  simpa [mul_assoc]

-- T2：b8 1143：pA^2*pB*pB*pA^2 = pA^2*pB^2*pA^2（合并 pB*pB）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pB*pA^2 = pA^2*pB^2*pA^2 := by
  simpa [mul_assoc]

-- T3：b7 步 3 全链：S2→S3（A@1 + b³=1）
-- pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hB3 : pB^3 = 1) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  calc pB*pA^2*pB^2*pA^3*pB*pA^4*pB
      = pB*pA^2*(pB*pB)*pA^3*pB*pA^4*pB := by
          rw [show pB^2 = pB*pB by rw [pow_two]]
  _ = pB*pA^2*pB*pB*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pB*(pA^2*pB)*pB*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pB*(pB^2*pA^3)*pB*pA^3*pB*pA^4*pB := by
          rw [a2_b_comm]
  _ = pB*pB^2*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pB^3*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [← pow_succ']
  _ = 1*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [pB_pow_three]
  _ = pA^3*pB*pA^3*pB*pA^4*pB := by
          simp

-- T4：b7 步 4：S3→S4（A×4 候选：simpa [← mul_assoc, a2_b_comm]）
-- pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  simpa [← mul_assoc, a2_b_comm, ← pow_succ]

-- T5：b7 步 4 手工链（拆 a³ + A 分步）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  calc pA^3*pB*pA^3*pB*pA^4*pB
      = pA*pA^2*pB*pA^3*pB*pA^4*pB := by
          rw [show pA^3 = pA*pA^2 by rw [← pow_succ']]
  _ = pA*(pA^2*pB)*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pA*(pB^2*pA^3)*pA^3*pB*pA^4*pB := by
          rw [a2_b_comm]
  _ = pA*pB^2*pA^3*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pA*pB*pB*pA^3*pA^3*pB*pA^4*pB := by
          rw [show pB^2 = pB*pB by rw [pow_two]]
  _ = pA*pB*pB*pA*pA^2*pA^3*pB*pA^4*pB := by
          rw [show pA^3 = pA*pA^2 by rw [← pow_succ']]
  _ = pA*pB*pB*pA*pA^2*pA*pA^2*pB*pA^4*pB := by
          rw [show pA^3 = pA*pA^2 by rw [← pow_succ']]
  _ = pA*pB*pB*pA*pA^5*pB*pA^4*pB := by
          simpa [mul_assoc, ← pow_add]
  _ = pA*pB*pB*pA*pB*pA^4*pB := by
          -- pA^5 = 1：pA*pB*pB*pA*pA^5*pB*pA^4*pB → pA*pB*pB*pA*1*pB*pA^4*pB → simp
          simpa [mul_assoc, pA_pow_five]

-- T6：b7 步 5（修正）：S4→S5
-- pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
  calc pA*pB*pB*pA*pB*pA^4*pB
      = pA*pB*pB*pA*pB*pA^2*pA^2*pB := by
          rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
  _ = pA*pB*pB*pA*pB*pA^2*(pA^2*pB) := by
          rw [← mul_assoc]
  _ = pA*pB*pB*pA*pB*pA^2*(pB^2*pA^3) := by
          rw [show pA^2*pB = pB^2*pA^3 by rw [hA]]
  _ = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
          simpa [mul_assoc]

-- T7：b7 步 6：S5→S6（A@5）
-- pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 = pA*pB*pB*pA^4*pB*pA^3
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 = pA*pB*pB*pA^4*pB*pA^3 := by
  simpa [← mul_assoc, a2_b_comm, ← pow_succ, ← pow_add, pA_pow_five]

-- T8：b7 步 7：S6→S7（A@3）
-- pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^2*pB^2*pA
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^2*pB^2*pA := by
  simpa [← mul_assoc, a2_b_comm, ← pow_succ, pA_pow_five]

end
