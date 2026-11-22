import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic

set_option maxRecursionDepth 1000

namespace A5CharQ5

-- ===== 测试环境声明（模拟 A5Defs 中的引理，用 h 假设代替）=====
-- pA = a, pB = b
-- A: a²·b = b²·a³     (a2_b_comm)
-- B: b·a² = a³·b²     (b_a2_comm)
-- C: a²·b·a² = b²     (a2_b_a2_eq_b2)
-- D: b·a²·b = a³      (b_a2_b_eq_a3)
-- F: a·b·a = a⁴·b²·a⁴ (a_b_a_eq_a4_b2_a4)
-- G: b²·a²·b² = b·a³·b (b2_a2_b2_eq_b_a3_b)
-- pA_pow_five: pA^5 = 1
-- pB_pow_three: pB^3 = 1

-- ===== b7 全链测试：pB*pA*pB*pA*pB = pA*pB*pA*pB^2*pA^4 =====
-- 脚本路径（权威）：F@1 -> A@3 -> A@1 -> A@1 -> A@7 -> A@5 -> A@5 -> A@3 -> A@3
-- 脚本中间态：
--   S0 = babab
--   S1 = ba4b2a4b        (F@1)
--   S2 = ba2b2a3ba4b     (A@3)
--   S3 = a3ba3ba4b       (A@1)
--   S4 = ab2aba4b        (A@1)
--   S5 = ab2aba2b2a3     (A@7)
--   S6 = ab2a4ba3        (A@5)
--   S7 = ab2a2b2a        (A@5)
--   S8 = aba3ba          (A@3)
--   S9 = abab2a4         (A@3)
-- 目标 = c10*a⁴ = a·b·a·b²·a⁴

noncomputable section

open Group

section b7chain

variable {G : Type} [Group G] (pA pB : G)
variable (hF : pA*pB*pA = pA^4*pB^2*pA^4)
variable (hA : pA^2*pB = pB^2*pA^3)
variable (hB : pB*pA^2 = pA^3*pB^2)
variable (hC : pA^2*pB*pA^2 = pB^2)
variable (hD : pB*pA^2*pB = pA^3)
variable (hG : pB^2*pA^2*pB^2 = pB*pA^3*pB)
variable (hA5 : pA^5 = 1)
variable (hB3 : pB^3 = 1)

-- 步 1（F@1）：S0 -> S1
example (hF : pA*pB*pA = pA^4*pB^2*pA^4) :
    pB*pA*pB*pA*pB = pB*pA^4*pB^2*pA^4*pB := by
  calc
    pB*pA*pB*pA*pB = pB*(pA*pB*pA)*pB := by rw [← mul_assoc]
    _ = pB*pA^4*pB^2*pA^4*pB := by rw [hF, ← mul_assoc]

-- 步 2（A@3）：S1 -> S2
example (hA : pA^2*pB = pB^2*pA^3) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  calc
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pA^2*pB^2*pA^2*pA^2*pB := by
      rw [show pA^4 = pA^2*pA^2 by rw [← pow_add], ← mul_assoc]
    _ = pB*pA^2*(pA^2*pB^2)*pA^2*pA^2*pB := by rw [← mul_assoc]
    _ = pB*pA^2*(pA^2*pB)*pB*pA^2*pA^2*pB := by
      rw [show pB^2 = pB*pB by rw [pow_two], ← mul_assoc]
    _ = pB*pA^2*pB^2*pA^3*pB*pA^2*pA^2*pB := by rw [hA, ← mul_assoc]
    _ = pB*pA^2*pB^2*pA^3*pB*(pA^2*pA^2)*pB := by rw [← mul_assoc]
    _ = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by rw [← pow_add]

-- 步 3（A@1）：S2 -> S3（TestNth9 T3 已验证的链）
example (hA : pA^2*pB = pB^2*pA^3) (hB3 : pB^3 = 1) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  calc
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pB*pA^2*pB*pB*pA^3*pB*pA^4*pB := by
      rw [show pB^2 = pB*pB by rw [pow_two], ← mul_assoc]
    _ = pB*(pA^2*pB)*pB*pA^3*pB*pA^4*pB := by rw [← mul_assoc]
    _ = pB^3*pA^3*pB*pA^3*pB*pA^4*pB := by
      rw [hA, ← mul_assoc, ← pow_succ']
    _ = 1*pA^3*pB*pA^3*pB*pA^4*pB := by rw [hB3]
    _ = pA^3*pB*pA^3*pB*pA^4*pB := by simp

-- 步 4（A@1）：S3 -> S4（脚本形态 ab2aba4b = pA*pB^2*pA*pB*pA^4*pB）
-- 尝试 1：simpa 拆幂 + A
example (hA : pA^2*pB = pB^2*pA^3) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB^2*pA*pB*pA^4*pB := by
  simpa [← pow_succ', hA, mul_assoc]

-- 步 4 尝试 2：手工链（全拆 2 个 pA^3）
example (hA : pA^2*pB = pB^2*pA^3) (hA5 : pA^5 = 1) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pB^2*pA^4*pB^2*pA^2*pB := by
  calc
    pA^3*pB*pA^3*pB*pA^4*pB = pA*pA^2*pB*pA*pA^2*pB*pA^4*pB := by
      rw [show pA^3 = pA*pA^2 by rw [← pow_succ'], mul_assoc]
    _ = pA*pB^2*pA^3*pA*pB^2*pA^3*pA^4*pB := by
      rw [hA, ← mul_assoc, ← mul_assoc]
    _ = pA*pB^2*pA^4*pB^2*pA^7*pB := by rw [← pow_add]
    _ = pA*pB^2*pA^4*pB^2*pA^2*pB := by
      rw [show pA^7 = pA^5*pA^2 by rw [← pow_add], hA5, one_mul]

end b7chain

end A5CharQ5
