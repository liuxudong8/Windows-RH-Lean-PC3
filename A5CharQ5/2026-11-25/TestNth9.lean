import Mathlib.Algebra.Group.Basic

-- 第八轮：最终候选验证（参数版，无主文件引理依赖）

-- T1：b8 1141：合并 pB*pB → pB^2（simpa 右结合化 + ← pow_two）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB*pA^3*pB^2 := by
  simpa [mul_assoc, ← pow_two]

-- T2：b8 1143：pA^2*pB*pB*pA^2 = pA^2*pB^2*pA^2
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pB*pA^2 = pA^2*pB^2*pA^2 := by
  rw [mul_assoc, ← pow_two]

-- T3：b7 步 3：S2→S3（手工链，参数版）
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
          rw [hA]
  _ = pB*pB^2*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
  _ = pB^3*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [← pow_succ']
  _ = 1*pA^3*pB*pA^3*pB*pA^4*pB := by
          rw [hB3]
  _ = pA^3*pB*pA^3*pB*pA^4*pB := by
          simp

-- T4：b7 步 4：S3→S4（simpa 候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hA5 : pA^5 = 1) (hB3 : pB^3 = 1) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  simpa [← mul_assoc, hA, ← pow_succ, hA5, hB3]

-- T5：b7 步 5（修正）：S4→S5（声明带括号）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
  calc pA*pB*pB*pA*pB*pA^4*pB
      = pA*pB*pB*pA*pB*(pA^2*pA^2)*pB := by
          rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
  _ = pA*pB*pB*pA*pB*pA^2*(pA^2*pB) := by
          rw [← mul_assoc]
  _ = pA*pB*pB*pA*pB*pA^2*(pB^2*pA^3) := by
          rw [show pA^2*pB = pB^2*pA^3 by rw [hA]]
  _ = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
          simpa [mul_assoc]

-- T6：b7 步 6：S5→S6（simpa 候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hA5 : pA^5 = 1) :
    pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 = pA*pB*pB*pA^4*pB*pA^3 := by
  simpa [← mul_assoc, hA, ← pow_succ, ← pow_add, hA5]

-- T7：b7 步 7：S6→S7（simpa 候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hA5 : pA^5 = 1) :
    pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^2*pB^2*pA := by
  simpa [← mul_assoc, hA, ← pow_succ, hA5]

-- T8：b7 步 8：S7→S8（simpa 候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA^2*pB^2*pA = pA*pB*pA^3*pB*pA := by
  simpa [← mul_assoc, hA]

-- T9：b7 步 9：S8→S9（simpa 候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pA^3*pB*pA = pA*pB*pA*pB^2*pA^4 := by
  simpa [← mul_assoc, hA]

-- T10：b7 步 2：S1→S2（全拆 + 重组，候选）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  calc pB*pA^4*pB^2*pA^4*pB
      = pB*(pA^2*pA^2)*pB^2*(pA^2*pA^2)*pB := by
          rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
  _ = pB*pA^2*(pA^2*pB^2)*(pA^2*pA^2)*pB := by
          -- 树 (((pB*(pA^2*pA^2))*pB^2)*(pA^2*pA^2))*pB
          -- 需要 (pB*pA^2)*(pA^2*pB^2)：先 ← mul_assoc 于 pB*(pA^2*pA^2) → (pB*pA^2)*pA^2*pB^2*(pA^2*pA^2)*pB
          rw [← mul_assoc]
          -- 再 mul_assoc 于 ((pB*pA^2)*pA^2)*pB^2 → (pB*pA^2)*(pA^2*pB^2)？不行（mul_assoc 给 pB*(pA^2*pA^2)）
          sorry
  _ = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by sorry

end
