# -*- coding: utf-8 -*-
"""任意 a（含 2a>1 的带限核情形）下 T = P·triKer·P 的最大特征值
T f(x) = ∫_[-a,a] max(0, 1-|x-y|) f(y) dy

关键简化：单元 [i,i+1]×[j,j+1] 上的双重积分只依赖偏移 k=|i-j|
  g(k) = ∫∫_{[0,h]^2} triKer(k h + u - v) du dv = ∫_{-h}^{h} (h-|t|) triKer(k h + t) dt
（因为 {(u,v)∈[0,h]^2 : u-v=t} 的测度 = h-|t|）。故 B 是 Toeplitz，构造 O(N)。
被积函数是分段多项式（在 t=0 与 kh+t=±1 处分段），逐段 Gauss 精确。
"""
import numpy as np

GX, GW = np.polynomial.legendre.leggauss(10)

def triKer(t):
    return np.maximum(0.0, 1.0 - np.abs(t))

def g_offset(k, h):
    """∫_{-h}^{h} (h-|t|) triKer(k h + t) dt，分段精确"""
    c = k*h
    brk = {-h, 0.0, h, -1.0-c, 1.0-c}
    pts = sorted(p for p in brk if -h <= p <= h)
    tot = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        if hi <= lo:
            continue
        A = 0.5*(hi-lo); B = 0.5*(hi+lo)
        t = A*GX + B
        tot += A*np.sum(GW * (h - np.abs(t)) * triKer(c + t))
    return tot

def mu1(a, N=None, want_full=False):
    if N is None:
        N = max(80, int(round(120*2*a)))
    h = 2*a/N
    kk = np.arange(N)
    g = np.array([g_offset(k, h) for k in kk])
    B = np.zeros((N, N))
    for i in range(N):
        d = np.abs(np.arange(N) - i)
        B[i, :] = g[d]
    ev = np.linalg.eigvalsh(B / h)[::-1]
    return (ev if want_full else ev[0]), N

print("=" * 80)
print("自检（与解析值对照）")
for a, ref in ((0.5, 0.675516943439), (0.25, 0.417522735401)):
    m, N = mu1(a, N=400)
    print(f"  a={a}  N=400  mu1={m:.10f}   解析={ref:.12f}   差={m-ref:+.1e}")

print("\n收敛性（a=0.5, 0.8, 1.5 三个 N）")
for a in (0.5, 0.8, 1.5):
    for N in (150, 300, 600):
        m, _ = mu1(a, N=N)
        print(f"  a={a:<5} N={N:4d}  mu1={m:.10f}")

print("=" * 80)
print("mu1(a) 随 a 的走向（2a 即 lambda_eff）")
for a in (0.50, 0.55, 0.60, 0.70, 0.80, 0.90, 1.00, 1.20, 1.50, 2.00, 3.00):
    m, N = mu1(a, N=max(300, int(round(150*2*a))))
    print(f"  a={a:<5} lambda={2*a:<5} N={N:4d}  mu1={m:.9f}   距0.875={m-0.875:+.6f}")

print("=" * 80)
print("求 mu1(a) = 0.875 的临界 a（即 7/8 所需的最小 lambda_eff）")
lo, hi = 0.5, 3.0
for _ in range(30):
    m = (lo+hi)/2
    v, _ = mu1(m, N=max(300, int(round(150*2*m))))
    if v < 0.875:
        lo = m
    else:
        hi = m
a_star = 0.5*(lo+hi)
v_star, N = mu1(a_star, N=max(300, int(round(150*2*a_star))))
print(f"  a* = {a_star:.6f}   lambda_eff* = {2*a_star:.6f}   mu1(a*) = {v_star:.9f}")
print(f"  对照：a=0.5 时 mu1=0.675517（差 {0.875-0.675517:.6f}）")
