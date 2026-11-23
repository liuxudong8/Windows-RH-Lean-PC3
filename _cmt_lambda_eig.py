# -*- coding: utf-8 -*-
"""密度形式泛函的最优核：算子 T f(x) = ∫_{[-a,a]} triKer(x-y) f(y) dy 的谱
用分片常数 Galerkin（单元上的双重积分用解析内积分 + Gauss，精确到机器精度）
"""
import numpy as np

def triKer(t):
    return np.maximum(0.0, 1.0 - np.abs(t))

GX, GW = np.polynomial.legendre.leggauss(6)

def G_of_y(y, a1, a2):
    """G(y) = ∫_{a1}^{a2} (1-|x-y|) dx, 返回数组"""
    y = np.atleast_1d(y).astype(float)
    G = np.empty_like(y)
    # y <= a1
    m = y <= a1
    G[m] = ((1+y[m])*a2 - a2**2/2) - ((1+y[m])*a1 - a1**2/2)
    # y >= a2
    m = y >= a2
    G[m] = ((1-y[m])*a2 + a2**2/2) - ((1-y[m])*a1 + a1**2/2)
    # a1 < y < a2 : 拆 x=y
    m = (y > a1) & (y < a2)
    yy = y[m]
    G[m] = ((yy-a1) - (yy*(yy-a1) - (yy**2-a1**2)/2)) + ((a2-yy) - ((a2**2-yy**2)/2 - yy*(a2-yy)))
    return G

def rect_int(a1, a2, b1, b2):
    """∫_{b1}^{b2}∫_{a1}^{a2} triKer(x-y) dx dy"""
    cuts = sorted({b1, b2, a1, a2} & set()) if False else None
    pts = [b1, b2]
    for c in (a1, a2):
        if b1 < c < b2:
            pts.append(c)
    pts = sorted(pts)
    tot = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        A = 0.5*(hi-lo); B = 0.5*(hi+lo)
        ys = A*GX + B
        tot += A*np.sum(GW * G_of_y(ys, a1, a2))
    return tot

def spectrum(a, N):
    h = 2*a/N
    edges = np.linspace(-a, a, N+1)
    B = np.empty((N, N))
    for i in range(N):
        a1, a2 = edges[i], edges[i+1]
        for j in range(N):
            b1, b2 = edges[j], edges[j+1]
            B[i, j] = rect_int(a1, a2, b1, b2)
    B = 0.5*(B + B.T)
    A = np.diag(np.full(N, h))
    # 广义对称问题 B v = mu A v ; A 是 h*I
    ev = np.linalg.eigvalsh(B / h)
    return ev[::-1], B

print("自检：整区双重积分 ∫∫ triKer 应 = 2/3")
for a in (0.5,):
    ev, B = spectrum(a, 4)
    print(f"  a={a} N=4: B.sum()={B.sum():.8f}  (应 0.66666667),  mu1={ev[0]:.8f}")

print("\n最大特征值 mu1（分片常数 Galerkin, 网格加密看收敛）")
for a in (0.5, 0.25):
    vals = []
    for N in (25, 50, 100, 200, 400):
        ev, _ = spectrum(a, N)
        vals.append((N, ev[0]))
        print(f"  a={a:<5} N={N:4d}  mu1={ev[0]:.10f}   C=2-mu1={2-ev[0]:.10f}")
    # Richardson：误差 O(h^2)
    N1, v1 = vals[-2]; N2, v2 = vals[-1]
    lim = v2 + (v2-v1)/3.0
    print(f"  → a={a} 外推 mu1 ≈ {lim:.8f}  (C ≈ {2-lim:.8f})")
    print(f"    a={a} 前 5 个特征值: " + ", ".join(f"{x:.6f}" for x in ev[:5]))
