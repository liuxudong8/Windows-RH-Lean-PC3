# -*- coding: utf-8 -*-
"""可容许类（f>=0, ∫f=1, supp f⊂[-a,a]）下 Q(f)=∫_0^40 ρ2|f̂|²du 的极小，
二分 A=1+Q=1.125 (7/8) 的临界 a(=λ)。FISTA + 单纯形投影。
"""
import numpy as np, sys

UMAX, NT = 40.0, 40000
def sinc(x):
    x = np.asarray(x, float)
    return np.where(np.abs(x) < 1e-13, 1.0, np.sin(x) / x)
t = np.linspace(0, 1, NT + 1)[1:]
u = UMAX * t ** 2
du = np.diff(np.concatenate([[0.0], u]))
w = (1.0 - sinc(np.pi * u) ** 2) * du

def build(a, n):
    edges = np.linspace(-a, a, n + 1); h = edges[1] - edges[0]
    B = (np.sin(2*np.pi*np.outer(u, edges[1:])) - np.sin(2*np.pi*np.outer(u, edges[:-1]))) / (2*np.pi*u)[:, None]
    A = (B * w[:, None]).T @ B          # A_ij = ∫ ρ2 φ̂_i φ̂_j du
    A = 0.5 * (A + A.T)
    return A, h

def proj_simplex(v):
    s = np.sort(v)[::-1]
    css = np.cumsum(s)
    rho = np.nonzero(s * np.arange(1, len(v) + 1) > (css - 1))[0][-1]
    theta = (css[rho] - 1) / (rho + 1.0)
    return np.maximum(v - theta, 0.0)

def min_q(a, n=200, iters=4000, verbose=False):
    A, h = build(a, n)
    C = A / h ** 2
    L = 2.0 * float(np.linalg.eigvalsh(C)[-1])
    g = np.full(n, 1.0 / n)
    y = g.copy(); tk = 1.0
    best = (g @ C @ g) / 2.0
    for k in range(iters):
        grad = 2.0 * C @ y
        xn = proj_simplex(y - grad / L)
        tn = (1 + np.sqrt(1 + 4 * tk ** 2)) / 2.0
        y = xn + ((tk - 1) / tn) * (xn - g)
        if (xn @ C @ xn) / 2.0 < (y @ C @ y) / 2.0:
            y = xn.copy()
        g, tk = xn, tn
        val = (g @ C @ g) / 2.0
        if val < best - 1e-12:
            best = val
    Q = float(g * h @ A @ (g * h)) # 用密度 f=g/h 直接算
    f = g / h
    return Q, f, edges_of(a, n), best

def edges_of(a, n):
    return np.linspace(-a, a, n + 1)

print("check a=0.5 uniform: Q(unif)=%.6f  1/6=%.6f" % (None or 0, 1/6))
for a in [0.5, 0.55, 0.60, 0.65, 0.70, 0.80, 1.00]:
    Q, f, e, best = min_q(a)
    print("a=%.2f  Q_min=%.6f  A=%.6f  2-A=%.6f  (f: min=%.4f max=%.4f)" %
          (a, Q, 1 + Q, 2 - (1 + Q), f.min(), f.max()))
    if a in (0.5, 0.8, 1.0):
        xs = np.linspace(-a, a, 21)
        prof = np.interp(xs, 0.5 * (e[:-1] + e[1:]), f)
        print("   轮廓：", np.array2string(prof / prof.max(), precision=2, suppress_small=True))
