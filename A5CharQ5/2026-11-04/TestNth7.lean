import Mathlib.Algebra.Group.Basic

-- 第六轮：b_8 / b_7 真实 calc 步测试（非自反目标，验证候选证明）

-- T1：b8 1140 步：pA^2*pB*pA^2*pA*pB*pB = pA^2*pB*pA^3*pB*pB（归并 a²·a → a³）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^2*pA*pB*pB = pA^2*pB*pA^3*pB*pB := by
  simpa [mul_assoc, ← pow_succ]

-- T2：b8 1140 候选 B：先 mul_assoc 再 ← pow_succ（分步）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^2*pA*pB*pB = pA^2*pB*pA^3*pB*pB := by
  calc pA^2*pB*pA^2*pA*pB*pB
      = pA^2*pB*pA^2*pA*pB*pB := by rfl
  _ = pA^2*pB*pA^3*pB*pB := by
      rw [show pA^2*pA = pA^3 by rw [← pow_succ]]

-- T3：b8 1142 步：a³·b² → b·a²（Bi 整段）
-- pA^2*pB*pA^3*pB*pB = pA^2*pB^2*pA^2
example (x : Type) [Monoid x] (pA pB : x) (hBi : pA^3*pB^2 = pB*pA^2) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB^2*pA^2 := by
  calc pA^2*pB*pA^3*pB*pB
      = pA^2*pB*pA^3*pB^2 := by simpa [mul_assoc, ← pow_succ]
  _ = pA^2*pB*(pB*pA^2) := by
      rw [show pA^3*pB^2 = pB*pA^2 by rw [hBi]]
  _ = pA^2*pB^2*pA^2 := by
      simpa [mul_assoc, ← pow_two]

-- T4：b7 1112 步：S0→S1（F：a·b·a → a⁴·b²·a⁴）
-- pB*pA*pB*pA*pB = pB*pA^4*pB^2*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hF : pA*pB*pA = pA^4*pB^2*pA^4) :
    pB*pA*pB*pA*pB = pB*pA^4*pB^2*pA^4*pB := by
  calc pB*pA*pB*pA*pB
      = pB*(pA*pB*pA)*pB := by rw [mul_assoc, ← mul_assoc]
  _ = pB*(pA^4*pB^2*pA^4)*pB := by
      rw [show pA*pB*pA = pA^4*pB^2*pA^4 by rw [hF]]
  _ = pB*pA^4*pB^2*pA^4*pB := by
      simpa [mul_assoc]

-- T5：b7 1115 步：S1→S2（A@3）
-- pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  calc pB*pA^4*pB^2*pA^4*pB
      = pB*pA^2*pA^2*pB^2*pA^4*pB := by
          -- 拆第一个 pA^4：rw [h4] 全拆问题 → 先拆一个（声明带括号）
          sorry
  _ = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by sorry

-- T6：b7 1117 步：S2→S3（A@1 + b³=1）
-- pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hB3 : pB^3 = 1) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  simpa [mul_assoc, ← pow_succ, hA]

-- T7：b7 1120 步：S3→S4
-- pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  calc pA^3*pB*pA^3*pB*pA^4*pB
      = pA*pA^2*pB*pA^3*pB*pA^4*pB := by
          rw [show pA^3 = pA*pA^2 by rw [← pow_succ']]
  _ = pA*pB^2*pA^3*pA^3*pB*pA^4*pB := by
          -- A@1：pA*pA^2*pB*pA^3... 中 pA^2*pB 节点 = (pA*pA^2)*pB 右子树？pA*(pA^2*pB)？rw [← mul_assoc] 于 L2=(pA*pA^2)*pB → pA*(pA^2*pB)——然后 hA？
          sorry
  _ = pA*pB*pB*pA*pB*pA^4*pB := by sorry

-- T8：b8 1139 步现状验证：pB^2*pA*pB*pB = pA^2*pB*pA^2*pA*pB*pB（Ci 整段）
example (x : Type) [Monoid x] (pA pB : x) (hCi : pB^2 = pA^2*pB*pA^2) :
    pB^2*pA*pB*pB = pA^2*pB*pA^2*pA*pB*pB := by
  rw [show pB^2 = pA^2*pB*pA^2 by rw [hCi]]
  rfl

end
