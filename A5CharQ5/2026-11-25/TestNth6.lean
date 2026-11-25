import Mathlib.Algebra.Group.Basic

-- 第五轮：rw [mul_assoc]（匹配 (a*b)*c → a*(b*c)）命中位置探测
-- 方法：rw [mul_assoc] 于自反目标 T=T，报错显示替换后的树 → 得知命中位置

-- 探测 1：b7 S1：pB*pA^4*pB^2*pA^4*pB（5 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^4*pB^2*pA^4*pB := by
  rw [mul_assoc]

-- 探测 2：b8：pA^2*pB*pA^3*pB*pB（5 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^2*pB*pA^3*pB*pB = pA^2*pB*pA^3*pB*pB := by
  rw [mul_assoc]

-- 探测 3：b7 S2：pB*pA^2*pB^2*pA^3*pB*pA^4*pB（8 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pB*pA^2*pB^2*pA^3*pB*pA^4*pB := by
  rw [mul_assoc]

-- 探测 4：b7 S4：pA*pB*pB*pA*pB*pA^4*pB（7 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^4*pB := by
  rw [mul_assoc]

-- 探测 5：b7 S3：pA^3*pB*pA^3*pB*pA^4*pB（7 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA^3*pB*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  rw [mul_assoc]

-- 探测 6：a11：pA*pB*pA^3*pB*pA*pB*pA^4（7 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pA^3*pB*pA*pB*pA^4 = pA*pB*pA^3*pB*pA*pB*pA^4 := by
  rw [mul_assoc]

-- 探测 7：a11：pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4（8 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4 = pB*pA^2*pB^2*pA*pB*pA^3*pB*pA^4 := by
  rw [mul_assoc]

-- 探测 8：b7 S6：pA*pB*pB*pA^4*pB*pA^3（6 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA^4*pB*pA^3 = pA*pB*pB*pA^4*pB*pA^3 := by
  rw [mul_assoc]

-- 探测 9：b7 R：pA*pB*pA*pB*pB*pA^4（6 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pA*pB*pB*pA^4 = pA*pB*pA*pB*pB*pA^4 := by
  rw [mul_assoc]

-- 探测 10：a11 外部：pA*pB*pB*pA^2*pB^2*pA*pB*pA^4（8 因子）
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA^2*pB^2*pA*pB*pA^4 = pA*pB*pB*pA^2*pB^2*pA*pB*pA^4 := by
  rw [mul_assoc]
