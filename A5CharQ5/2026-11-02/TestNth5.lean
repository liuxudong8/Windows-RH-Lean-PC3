import Mathlib.Algebra.Group.Basic

-- 第四轮：rw [← mul_assoc] 命中位置探测
-- 方法：rw [← mul_assoc] 于自反目标 T=T，报错显示替换后的树 → 得知命中位置

-- 探测 1：b8 S1：pA^2*pB*pA^3*pB*pB（5 因子）——期望命中 L2=(pA^2*pB)*pA^3
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB*pA^3*pB*pB := by
  rw [← mul_assoc]

-- 探测 2：b7 S2：pB*pA^2*pB^2*pA^3*pB*pA^4*pB（8 因子）——期望命中 L2=(pB*pA^2)*pB^2
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  rw [← mul_assoc]

-- 探测 3：拆 pA^4 后（带括号）pB*(pA^2*pA^2)*pB^2*pA^4*pB——命中 L2 还是深处？
example (x : Type) [Monoid x] (pA pB : x) :
    pB*(pA^2*pA^2)*pB^2*pA^4*pB = pB*(pA^2*pA^2)*pB^2*pA^4*pB := by
  rw [← mul_assoc]

-- 探测 4：b7 S4 拆 pA^4 后：pA*pB*pB*pA*pB*(pA^2*pA^2)*pB
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pB*(pA^2*pA^2)*pB = pA*pB*pB*pA*pB*(pA^2*pA^2)*pB := by
  rw [← mul_assoc]

-- 探测 5：b7 S3 拆 a³ 后：pA*pA^2*pB*pA^3*pB*pA^4*pB
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pA^2*pB*pA^3*pB*pA^4*pB = pA*pA^2*pB*pA^3*pB*pA^4*pB := by
  rw [← mul_assoc]

-- 探测 6：b8 目标：pA^2*pB*(pB*pA^2)
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*(pB*pA^2) = pA^2*pB*(pB*pA^2) := by
  rw [← mul_assoc]

-- 探测 7：b7 S4：pA*pB*pB*pA*pB*pA^4*pB（7 因子）——期望命中 L2
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  rw [← mul_assoc]

-- 探测 8：a11 外部步：pA*pB*pA^3*pB*pA*pB*pA^4（Bi 步源）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pA^3*pB*pA*pB*pA^4 = pA*pB*pA^3*pB*pA*pB*pA^4 := by
  rw [← mul_assoc]

-- 探测 9：a11 外部：pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4 = pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4 := by
  rw [← mul_assoc]

-- 探测 10：b7 步 2 中间：pB*pA^2*(pA^2*pB^2)*pA^4*pB（含括号）
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*(pA^2*pB^2)*pA^4*pB = pB*pA^2*(pA^2*pB^2)*pA^4*pB := by
  rw [← mul_assoc]
