# -*- coding: utf-8 -*-
"""修正版：Q(f)=∫_0^40 ρ2|f̂|²du，f=g/h（g 为单元质量）。非负+∫f=1 约束下极小。
先做 uniform 锚点自检（a=0.5 应给 1/6=0.166667）。"""
import numpy as np

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
    A = (B * w[:, None]).T @ B
    A = 0.5 * (A + A.T)
    return A, h, edges

def Qval(g, A, h):
    f = g / h
    return float(f @ A @ f)

def proj_simplex(v):
    s = np.sort(v)[::-1]; css = np.cumsum(s)
    rho = np.nonzero(s * np.arange(1, len(v) + 1) > (css - 1))[0][-1]
    return np.maximum(v - (css[rho] - 1) / (rho + 1.0), 0.0)

def min_q(a, n=200, iters=6000):
    A, h, edges = build(a, n)
    C = A / h ** 2
    L = 2.0 * float(np.linalg.eigvalsh(C)[-1])
    g = np.full(n, 1.0 / n); y = g.copy(); tk = 1.0
    for k in range(iters):
        grad = 2.0 * C @ y
        xn = proj_simplex(y - grad / L)
        tn = (1 + np.sqrt(1 + 4 * tk ** 2)) / 2.0
        ynew = xn + ((tk - 1) / tn) * (xn - g)
        if (ynew @ C @ ynew) > (xn @ C @ xn):
            ynew = xn.copy(); tn = 1.0
        g, y, tk = xn, ynew, tn
    return Qval(g, A, h), g / h, edges, (g @ C @ g)

# 锚点：uniform
A, h, e = build(0.5, 200)
print("锚点 uniform a=0.5: Q=%.6f  (1/6=%.6f)" % (Qval(np.full(200, 1.0/200), A, h), 1/6))

for a in [0.50, 0.60, 0.70, 0.85, 1.00]:
    Q, f, edges, raw = min_q(a)
    print("\na=%.2f  Q_min=%.6f  A=%.6f  2-A=%.6f  f_max/f_mean=%.2f" %
          (a, Q, 1 + Q, 2 - (1 + Q), f.max() / (1 / (2 * a))))
    xs = np.linspace(-a, a, 25)
    prof = np.interp(xs, 0.5 * (edges[:-1] + edges[1:]), f)
    print("  轮廓(归一到峰1)：", np.array2string(prof / prof.max(), precision=2, suppress_small=True))
    print("  密度质量分布(前8大单元)：", np.array2string(np.sort(f)[::-1][:8], precision=3))
