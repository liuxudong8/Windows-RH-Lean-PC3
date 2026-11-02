import A5CharQ5.A5Defs

-- 技巧1：a²·a = a³
example : pA ^ 2 * pA = pA ^ 3 := by
  rw [← pow_succ']
  norm_num

-- 技巧2：a·a³ = a⁴（:796 风格）
example : pA * pA ^ 3 = pA ^ 4 := by
  rw [← pow_succ']
  norm_num

-- 技巧3：a⁶ = a（pA_pow_mod）
example : pA ^ 6 = pA := by
  rw [pA_pow_mod]
  norm_num

-- 技巧4：a⁴ = a²·a²
example : pA ^ 4 = pA ^ 2 * pA ^ 2 := by
  rw [← pow_add]
  norm_num

-- 技巧5：a⁴·a² = a⁶
example : pA ^ 4 * pA ^ 2 = pA ^ 6 := by
  rw [← pow_add]
  norm_num

-- 技巧6：a²·a³ = a⁵
example : pA ^ 2 * pA ^ 3 = pA ^ 5 := by
  rw [← pow_add]
  norm_num

-- 技巧7：mul_assoc 子式替换（hbab4 行2）
example : pB * (pA ^ 2 * pA ^ 2) * pB = pB * pA ^ 2 * pA ^ 2 * pB := by
  rw [← mul_assoc]

-- 新恒等式 hba：b²·a = a²·b·a³
lemma hba_probe : pB ^ 2 * pA = pA ^ 2 * pB * pA ^ 3 := by
  calc pB ^ 2 * pA
      = pA ^ 2 * pB * pA ^ 2 * pA := by rw [← a2_b_a2_eq_b2]
      _ = (pA ^ 2 * pB) * (pA ^ 2 * pA) := by rw [mul_assoc]
      _ = pA ^ 2 * pB * pA ^ 3 := by
        rw [← pow_succ']
        norm_num

-- 新恒等式 hbab4：b·a⁴·b = a³·b·a³
lemma hbab4_probe : pB * pA ^ 4 * pB = pA ^ 3 * pB * pA ^ 3 := by
  calc pB * pA ^ 4 * pB
      = pB * (pA ^ 2 * pA ^ 2) * pB := by
        rw [show pA ^ 4 = pA ^ 2 * pA ^ 2 by
          rw [← pow_add]
          norm_num]
      _ = pB * pA ^ 2 * pA ^ 2 * pB := by rw [← mul_assoc]
      _ = (pB * pA ^ 2) * (pA ^ 2 * pB) := by rw [mul_assoc]
      _ = (pA ^ 3 * pB ^ 2) * (pB ^ 2 * pA ^ 3) := by rw [b_a2_comm, a2_b_comm]
      _ = pA ^ 3 * (pB ^ 2 * (pB ^ 2 * pA ^ 3)) := by rw [mul_assoc]
      _ = pA ^ 3 * ((pB ^ 2 * pB ^ 2) * pA ^ 3) := by nth_rewrite 2 [← mul_assoc]
      _ = pA ^ 3 * (pB ^ 4 * pA ^ 3) := by rw [← pow_two]
      _ = pA ^ 3 * (pB * pA ^ 3) := by rw [pB_pow_four]
      _ = pA ^ 3 * pB * pA ^ 3 := by rw [← mul_assoc]

-- 新恒等式 p1sub：b²·a² = a²·b·a⁴
lemma p1sub_probe : pB ^ 2 * pA ^ 2 = pA ^ 2 * pB * pA ^ 4 := by
  calc pB ^ 2 * pA ^ 2
      = pA ^ 2 * pB * pA ^ 2 * pA ^ 2 := by rw [← a2_b_a2_eq_b2]
      _ = (pA ^ 2 * pB) * (pA ^ 2 * pA ^ 2) := by rw [mul_assoc]
      _ = (pA ^ 2 * pB) * pA ^ 4 := by
        rw [← pow_add]
        norm_num
      _ = pA ^ 2 * pB * pA ^ 4 := by rfl

-- 新恒等式 p1：a⁴·b²·a² = a·b·a⁴（a_11 尾段）
lemma p1_probe : pA ^ 4 * pB ^ 2 * pA ^ 2 = pA * pB * pA ^ 4 := by
  calc pA ^ 4 * pB ^ 2 * pA ^ 2
      = pA ^ 4 * (pB ^ 2 * pA ^ 2) := by rw [mul_assoc]
      _ = pA ^ 4 * (pA ^ 2 * pB * pA ^ 4) := by rw [show pB ^ 2 * pA ^ 2 = pA ^ 2 * pB * pA ^ 4 by
          calc pB ^ 2 * pA ^ 2
              = pA ^ 2 * pB * pA ^ 2 * pA ^ 2 := by rw [← a2_b_a2_eq_b2]
              _ = (pA ^ 2 * pB) * (pA ^ 2 * pA ^ 2) := by rw [mul_assoc]
              _ = (pA ^ 2 * pB) * pA ^ 4 := by
                rw [← pow_add]
                norm_num
              _ = pA ^ 2 * pB * pA ^ 4 := by rfl]
      _ = pA ^ 4 * pA ^ 2 * pB * pA ^ 4 := by rw [← mul_assoc, ← mul_assoc]
      _ = pA ^ 6 * pB * pA ^ 4 := by
        rw [show pA ^ 4 * pA ^ 2 = pA ^ 6 by
          rw [← pow_add]
          norm_num]
      _ = pA * pB * pA ^ 4 := by
        rw [show pA ^ 6 = pA by
          rw [pA_pow_mod]
          norm_num]
