import Mathlib.Algebra.Group.Basic

-- 第二轮：验证修正后的 rw 模式（基于 TestNth2 失败教训）
-- 教训：
--  (a) rw [show pA^4 = pA^2*pA^2 ...] 全拆所有 pA^4 → 用 nth_rewrite 1 只拆第一个
--  (b) rw [← pow_succ] 匹配 a^n*a；a*a^n 形态用 ← pow_succ'
--  (c) rw [pow_two] 匹配所有 ?a^2，先命中第一个（pA^2 先于 pB^2）
--  (d) simpa [mul_assoc] 会展开 pA^2 → pA*pA，不可靠；避免

-- ===== 测试 A：nth_rewrite 1 只拆第一个 pA^4 =====
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pA^2*pB^2*pA^4*pB := by
  nth_rewrite 1 [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
  rfl

-- ===== 测试 B：rw [← pow_succ'] 匹配 a*a^n（pA*pA^3 作为直接子项） =====
example (x : Type) [Monoid x] (pA pB : x) :
    (pA*pB*pB)*(pA*pA^3) = (pA*pB*pB)*pA^4 := by
  rw [← pow_succ']

-- ===== 测试 C：pB*pB^2 → pB^3（← pow_succ'） =====
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pB^2*pA^3*pB*pA^3*pB*pA^4*pB = pB^3*pA^3*pB*pA^3*pB*pA^4*pB := by
  rw [← pow_succ']

-- ===== 测试 D：nth_rewrite 2 [pow_two] 只拆 pB^2（pA^2 是第一个平方） =====
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pB*pA^2*pB*pB*pA^3*pB*pA^4*pB := by
  nth_rewrite 2 [pow_two]
  rfl

-- ===== 测试 E：b7 步 2 完整子证明：pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB =====
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  calc pB*pA^4*pB^2*pA^4*pB
      = pB*pA^2*pA^2*pB^2*pA^4*pB := by
          nth_rewrite 1 [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
          rfl
  _ = pB*pA^2*(pA^2*pB^2)*pA^4*pB := by
          -- 树 ((((pB*pA^2)*pA^2)*pB^2)*pA^4)*pB？声明 pB*pA^2*(pA^2*pB^2)*pA^4*pB = ((pB*pA^2)*(pA^2*pB^2))*pA^4*pB
          rw [← mul_assoc]
          rfl
  _ = pB*pA^2*(pB^2*pA^3*pB)*pA^4*pB := by
          rw [show pA^2*pB^2 = pB^2*pA^3*pB by
              calc pA^2*pB^2
                  = pA^2*(pB*pB) := by rw [pow_two]
                  _ = (pA^2*pB)*pB := by rw [mul_assoc]
                  _ = (pB^2*pA^3)*pB := by rw [hA]
          ]
  _ = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
          simpa [mul_assoc]

-- ===== 测试 F：b7 步 4：pA^3*pB*pA^3*pB*pA^4*pB = pA*pB^2*pA^6*pB*pA^4*pB =====
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hB3 : pB^3 = 1) (hA5 : pA^5 = 1) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB^2*pA^6*pB*pA^4*pB := by
  calc pA^3*pB*pA^3*pB*pA^4*pB
      = pA*pA^2*pB*pA^3*pB*pA^4*pB := by
          rw [show pA^3 = pA*pA^2 by rw [← pow_succ']]
          rfl
  _ = pA*(pA^2*pB)*pA^3*pB*pA^4*pB := by
          rw [← mul_assoc]
          rfl
  _ = pA*(pB^2*pA^3)*pA^3*pB*pA^4*pB := by
          rw [show pA^2*pB = pB^2*pA^3 by rw [hA]]
  _ = pA*pB^2*pA^3*pA^3*pB*pA^4*pB := by
          simpa [mul_assoc]
  _ = pA*pB^2*(pA^3*pA^3)*pB*pA^4*pB := by
          rw [← mul_assoc]
          rfl
  _ = pA*pB^2*pA^6*pB*pA^4*pB := by
          rw [← pow_add]

-- ===== 测试 G：b7 步 5：pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 =====
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
  calc pA*pB*pB*pA*pB*pA^4*pB
      = pA*pB*pB*pA*pB*pA^2*pA^2*pB := by
          -- 拆第一个 pA^4：`(pA*pB*pB*pA*pB)*(pA^4*pB)` 中 pA^4 是唯一？不，只有 1 个 pA^4
          rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
          -- rw 全拆（只有 1 个 pA^4）→ pA*pB*pB*pA*pB*pA^2*pA^2*pB？树 ((pA*pB*pB*pA*pB)*(pA^2*pA^2))*pB
          rfl
  _ = pA*pB*pB*pA*pB*pA^2*(pA^2*pB) := by
          -- ((X*pA^2)*pA^2)*pB → (X*pA^2)*(pA^2*pB)：rw [← mul_assoc] 于 L6？树 ((((((pA*pB)*pB)*pA)*pB)*pA^2)*pA^2)*pB：
          -- L2=(pA*pB)*pB 最先命中 ✗！需换法
          sorry

-- ===== 测试 H：b7 步 7：pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^2*pB^2*pA =====
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hA5 : pA^5 = 1) :
    pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^2*pB^2*pA := by
  calc pA*pB*pB*pA^4*pB*pA^3
      = pA*pB*pB*pA^2*pA^2*pB*pA^3 := by
          nth_rewrite 1 [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
          rfl
  _ = pA*pB*pB*pA^2*(pA^2*pB)*pA^3 := by
          -- 树 ((((((pA*pB)*pB)*pA^2)*pA^2)*pB)*pA^3)：需要 (X*pA^2)*pA^2*pB → (X*pA^2)*(pA^2*pB)？还是 L2 问题
          sorry

-- ===== 测试 I：b7 步 8：pA*pB*pA^3*pB*pA = pA*pB*pA*pB^2*pA^4 =====
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pA^3*pB*pA = pA*pB*pA*pB^2*pA^4 := by
  calc pA*pB*pA^3*pB*pA
      = pA*pB*pA*pA^2*pB*pA := by
          nth_rewrite 2 [show pA^3 = pA*pA^2 by rw [← pow_succ']]
          rfl
  _ = pA*pB*pA*(pA^2*pB)*pA := by
          -- 树 (((((pA*pB)*pA)*pA^2)*pB)*pA)：L2=(pA*pB)*pA 最先命中 ✗
          sorry

-- ===== 测试 J：b8 完整链：pB*pB*pA*pB*pB = pA*pA*pB*pA*pA =====
-- L = b²ab² = (pB*pB)*(pA*pB*pB)？coset_b_8 的 change：pB*(pB*pA*pB*pB) = pA^2*pB^2*pA^2
-- S0 = pB*pB*pA*pB*pB，S1 = pA^2*pB*pA^3*pB^2，S2 = pA^2*pB^2*pA^2
example (x : Type) [Monoid x] (pA pB : x) (hCi : pB^2 = pA^2*pB*pA^2) (hBi : pA^3*pB^2 = pB*pA^2) :
    pB*pB*pA*pB*pB = pA^2*pB^2*pA^2 := by
  calc pB*pB*pA*pB*pB
      = pB*pB*pA*pB*pB := by rfl
  -- Ci@0：b² → a²·b·a²
  _ = (pA^2*pB*pA^2)*pA*pB*pB := by
      rw [show pB^2 = pA^2*pB*pA^2 by rw [hCi]]
      rfl
  _ = pA^2*pB*pA^2*pA*pB*pB := by
      simpa [mul_assoc]
  -- 归并 a²·a = a³
  _ = pA^2*pB*pA^3*pB*pB := by
      rw [← pow_succ]
  -- 拆 pB^2（nth_rewrite 2）
  _ = pA^2*pB*pA^3*pB*pB := by rfl
  -- Bi：a³·b² → b·a²（这里 a³·b·b = (a³·b)*b，Bi 匹配 a³·b² 需要先合并 b·b = b²）
  -- 先合并最后两个 b：pA^2*pB*pA^3*pB*pB → pA^2*pB*pA^3*pB^2
  _ = pA^2*pB*pA^3*pB^2 := by
      rw [← pow_two]
  _ = pA^2*pB*(pB*pA^2) := by
      rw [hBi]
  _ = pA^2*pB*pB*pA^2 := by
      simpa [mul_assoc]
  _ = pA^2*pB^2*pA^2 := by
      rw [← pow_two]

end
