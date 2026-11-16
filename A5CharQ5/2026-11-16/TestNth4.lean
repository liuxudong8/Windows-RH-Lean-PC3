import Mathlib.Algebra.Group.Basic

-- 第三轮：整段 show 模式验证（b_7 / b_8 核心步）
-- 教训：nth_rewrite 不接受 show-by 参数 → 用 have 定义引理名

-- T1：have + nth_rewrite 1 拆第一个 pA^4，声明匹配 rw 结果树（带括号）
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^4*pB^2*pA^4*pB = pB*(pA^2*pA^2)*pB^2*pA^4*pB := by
  have h4 : pA^4 = pA^2*pA^2 := by rw [← pow_add]
  nth_rewrite 1 [h4]
  rfl

-- T2：b7 步 2 整段：S1→S2
-- pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB（A@3：a⁴·b² 的 a²·b → b²·a³）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  calc pB*pA^4*pB^2*pA^4*pB
      = pB*(pA^2*pA^2)*pB^2*pA^4*pB := by
          have h4 : pA^4 = pA^2*pA^2 := by rw [← pow_add]
          nth_rewrite 1 [h4]
          rfl
  _ = pB*pA^2*(pA^2*pB^2)*pA^4*pB := by
          -- 树 (((pB*(pA^2*pA^2))*pB^2)*pA^4)*pB
          -- 两次 rw [← mul_assoc]：先 L3 = (pB*(pA^2*pA^2))*pB^2 → pB*((pA^2*pA^2)*pB^2)；再内部 ((pA^2*pA^2)*pB^2) → pA^2*(pA^2*pB^2)
          rw [← mul_assoc, ← mul_assoc]
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

-- T3：b7 步 3：S2→S3（A@1：pB*pA^2*pB^2 的 a²·b → b²·a³，然后 b³ → 1）
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) (hB3 : pB^3 = 1) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  calc pB*pA^2*pB^2*pA^3*pB*pA^4*pB
      = pB*pA^2*pB*pB*pA^3*pB*pA^4*pB := by
          have h2 : pB^2 = pB*pB := by rw [pow_two]
          -- 拆 pB^2（第一个平方？pA^2 也是平方——nth_rewrite 2 拆 pB^2）
          -- 方案：pA^2 是第 1 个平方，pB^2 是第 2 个 → nth_rewrite 2 [h2]？序号不可靠 → 用 rw [pow_two] 全拆 pA^2 和 pB^2？
          -- 改为：先拆 pB^2（用 rw [pow_two] 会先拆 pA^2）→ 干脆声明全拆？太丑。
          -- 用整段 calc 更稳：
          sorry
  _ = pA^3*pB*pA^3*pB*pA^4*pB := by sorry

-- T4：b7 步 5（修正 1122）：S4→S5
-- pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3
example (x : Type) [Monoid x] (pA pB : x) (hA : pA^2*pB = pB^2*pA^3) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 := by
  calc pA*pB*pB*pA*pB*pA^4*pB
      = pA*pB*pB*pA*pB*(pA^2*pA^2)*pB := by
          have h4 : pA^4 = pA^2*pA^2 := by rw [← pow_add]
          rw [h4]  -- 唯一 pA^4 → (pA*pB*pB*pA*pB)*(pA^2*pA^2)*pB
          rfl
  _ = pA*pB*pB*pA*pB*pA^2*(pA^2*pB) := by
          -- 树 ((((X*(pA^2*pA^2))*pB)，X = pA*pB*pB*pA*pB。需要 (X*pA^2)*(pA^2*pB)？
          -- 用整段 calc 太复杂 → 试试 rw [← mul_assoc] 序列？
          sorry

-- T5：b8 步 2：S1→S2（Bi：a³·b² → b·a²）
-- pA^2*pB*pA^3*pB*pB = pA^2*pB^2*pA^2
example (x : Type) [Monoid x] (pA pB : x) (hBi : pA^3*pB^2 = pB*pA^2) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB^2*pA^2 := by
  calc pA^2*pB*pA^3*pB*pB
      = pA^2*pB*(pA^3*pB)*pB := by
          -- 树 (((((pA^2*pB)*pA^3)*pB)*pB)：重组 L3 = ((pA^2*pB)*pA^3) → (pA^2*pB)*(pA^3*pB)？rw [← mul_assoc] 命中？
          sorry
  _ = pA^2*pB^2*pA^2 := by sorry

end
