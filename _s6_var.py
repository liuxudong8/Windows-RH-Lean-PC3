# -*- coding: utf-8 -*-
"""S6 真泛函 A(f)=1+∫_0^U ρ2(u)|f̂(u)|²du（K=f̂, ∫f=1, supp f⊂[-a,a]）下的变分问题：
   min Q(f) s.t. ∫f=1  —— KKT 线性解（分片常数基，φ̂ 解析）。
"""
import numpy as np

UMAX = 40.0
def sinc(x):
    x = np.asarray(x, float)
    return np.where(np.abs(x) < 1e-13, 1.0, np.sin(x) / x)

# u 网格：u=UMAX*t^2 加密小 u（ρ2~u²，K 变化快）
nt = 60000
t = np.linspace(0, 1, nt + 1)[1:]
u = UMAX * t ** 2
du = np.diff(np.concatenate([[0.0], u]))
rho2 = 1.0 - sinc(np.pi * u) ** 2
w = rho2 * du

def basis_hat(x0, x1):
    """φ=1 on [x0,x1]，φ̂(u)=∫ cos(2πux)dx = [sin(2πu x1)-sin(2πu x0)]/(2πu)"""
    with np.errstate(divide='ignore', invalid='ignore'):
        val = (np.sin(2 * np.pi * u * x1) - np.sin(2 * np.pi * u * x0)) / (2 * np.pi * u)
    return val

def solve(a=0.5, n=200, signed=True):
    edges = np.linspace(-a, a, n + 1)
    h = edges[1] - edges[0]
    B = np.empty((n, u.size))
    for i in range(n):
        B[i] = basis_hat(edges[i], edges[i + 1])
    A = (B * w) @ B.T
    A = 0.5 * (A + A.T)
    c = np.full(n, h)
    M = np.zeros((n + 1, n + 1))
    M[:n, :n] = A
    M[:n, n] = c
    M[n, :n] = c
    rhs = np.zeros(n + 1); rhs[n] = 1.0
    sol, *_ = np.linalg.lstsq(M, rhs, rcond=None)
    f = sol[:n]
    Q = float(f @ A @ f)
    return Q, f, edges, h

def Q_of(fun, a=0.5, n=40000):
    x = np.linspace(-a, a, n)
    v = fun(x)
    K = np.array([np.trapezoid(v * np.cos(2 * np.pi * uu * x), x) for uu in np.linspace(0, UMAX, 4000)])
    ug = np.linspace(0, UMAX, 4000)
    return float(np.trapezoid((1.0 - sinc(np.pi * ug) ** 2) * K ** 2, ug))

# 校验：uniform 应给 1/6
Q_unif = Q_of(lambda x: np.ones_like(x))
print("Q(uniform)=%.6f   (1/6=%.6f)" % (Q_unif, 1.0/6.0))
s2 = np.sqrt(2.0)
f0 = lambda x: np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))
print("Q(f0 MT)=%.6f  -> A_MT_model=%.6f (S6 实测 1.1868)" % (Q_of(f0), 1.0 + Q_of(f0)))

for a in [0.5, 1.018, 2.036]:
    Q, f, edges, h = solve(a=a, n=200)
    print("\n[a=%.3f] Q_min=%.6f  A_min=1+Q=%.6f  => 2-A=%.6f" % (a, Q, 1 + Q, 2 - (1 + Q)))
    if a == 0.5:
        idx = np.argsort(-np.abs(f))[:12]
        print(" f 形状（主要单元）：", ", ".join("x=%.2f:%.3f" % (0.5 * (edges[i] + edges[i + 1]), f[i]) for i in sorted(idx)))
        xs = np.linspace(-0.5, 0.5, 41)
        fint = np.interp(xs, 0.5 * (edges[:-1] + edges[1:]), f)
        print(" 采样值：", np.array2string(fint / np.abs(fint).max(), precision=3, suppress_small=True))
