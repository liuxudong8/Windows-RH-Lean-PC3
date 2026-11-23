# -*- coding: utf-8 -*-
"""校核 Lamzouri Lemma 3.2 / 式 (3.1) 的真泛函：
   C_eta = Q(0) + 2∫_0^1 α Q(α) dα,   Q = f*f,  f = η^2 ≥ 0, ∫f = 1, supp f ⊂ (-λ,λ)
锚点：f≡1 应给 4/3（经典 Montgomery 2/3）；f0 应给 C_MT = 1.3274992963。
自相关用 |FFT|^2，滞后量直接读下标，避免任何环形对齐问题。
"""
import numpy as np

M = 1 << 21
dx = 1.0 / 2**18            # 支撑 [-0.5,0.5] 用 2^18 格点，M dx = 8 ⟹ 滞后 [-1,1] 无回绕
x = -4.0 + np.arange(M) * dx

def C_eta(fun, a=0.5):
    f = np.where(np.abs(x) <= a, fun(x), 0.0)
    A = np.fft.fft(f)
    r = np.real(np.fft.ifft(A * np.conj(A))) * dx      # r[j] = Q(j dx)
    Q0 = r[0]
    n1 = int(round(1.0 / dx))
    j = np.arange(n1 + 1)
    J = 2.0 * np.sum((j * dx) * r[:n1 + 1]) * dx
    return Q0, J, Q0 + J

s2 = np.sqrt(2.0)
v1 = 0.8603335890193797625
f0 = lambda x: np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))
Astar = 0.881123527
fstar = lambda x: np.cos(2 * v1 * x) / Astar

for name, fun, ref in [("f ≡ 1  (经典 Montgomery)", lambda x: np.ones_like(x), 4.0 / 3.0),
                       ("f0     (Montgomery–Taylor)", f0, 1.3274992963),
                       ("cos(2v1x) 归一", fstar, None)]:
    Q0, J, C = C_eta(fun)
    tail = "" if ref is None else "  [理论 %.10f, 差 %+.2e]" % (ref, C - ref)
    print("%-26s Q(0)=%.7f  J=%.7f  C_eta=%.10f  2-C=%.10f%s" % (name, Q0, J, C, 2 - C, tail))
print("\nDONE")
