# -*- coding: utf-8 -*-
"""口径 A 下的候选核族 C 值 + 该类的最优核（变分问题）
C_rho(K) = 1 + ∫ K(u)^2 (1 - sinc^2(pi u)) du        (代码口径: pairConstant triKer)
C_den(f) = 1 + ∫f^2 - <f*f, triKer> = 2 - <K, triKer>  (文档"密度形式")
约定: f 为密度, K = f*f 归一化使 K(0)=1 (即 ∫f^2=1), supp f ⊂ [-a,a], lambda_eff = 2a <= 1
"""
import numpy as np

def sinc(x):
    x = np.asarray(x, float)
    out = np.ones_like(x)
    nz = x != 0.0
    out[nz] = np.sin(np.pi * x[nz]) / (np.pi * x[nz])
    return out

def Lam(t):
    return np.maximum(0.0, 1.0 - np.abs(t))

NGRID = 1 << 14

def family_numbers(f, a, ngrid=NGRID):
    """给密度 f(支持 [-a,a]) 返回 (C_rho, C_den, int f^2, K(0))"""
    x = np.linspace(-a, a, ngrid)
    h = x[1] - x[0]
    fx = f(x)
    n2 = 2 * ngrid
    F = np.fft.rfft(fx, n2)
    ac = np.fft.irfft(F * np.conj(F), n2) * h      # 自相关, 指数 j -> 滞后 j*h
    norm = ac[0]                                    # = ∫ f^2
    K = ac / norm                                   # K(0)=1
    u = np.arange(n2) * h                           # 滞后 >= 0
    rho2 = 1.0 - sinc(u) ** 2
    I_rho = np.trapezoid(K ** 2 * rho2, u)          # ∫_0^{2a}
    I_lam = np.trapezoid(K * Lam(u), u)             # ∫_0^{2a} K Lam (Lam 支撑到 1)
    C_rho = 1.0 + 2.0 * I_rho
    C_den = 2.0 - 2.0 * I_lam
    return C_rho, C_den, norm, K[0], (2.0 * I_rho, 2.0 * I_lam)

def nystrom_top(a, P=200, q=12):
    """算子 T f(x) = ∫_{-a}^{a} Lam(x-y) f(y) dy 的最大特征值
    复合 Gauss-Legendre, 每行在 y=x 处切断以避免核折点"""
    n = P * q
    nodes = np.empty(n); wts = np.empty(n)
    edges = np.linspace(-a, a, P + 1)
    gx, gw = np.polynomial.legendre.leggauss(q)
    for p in range(P):
        lo, hi = edges[p], edges[p + 1]
        nodes[p*q:(p+1)*q] = 0.5*(hi-lo)*gx + 0.5*(hi+lo)
        wts[p*q:(p+1)*q] = 0.5*(hi-lo)*gw
    M = np.empty((n, n))
    for i in range(n):
        xi = nodes[i]
        kern = Lam(xi - nodes)
        # 把含 xi 的面板在对 y=xi 的折点处切断: 用分段再积一次的高精度重算该面板
        M[i, :] = kern * wts
        p = np.searchsorted(edges, xi, side='right') - 1
        p = min(max(p, 0), P - 1)
        lo, hi = edges[p], edges[p + 1]
        # 该面板拆成 [lo,xi] + [xi,hi]
        for (s0, s1) in ((lo, xi), (xi, hi)):
            if s1 <= s0:
                continue
            A = 0.5*(s1-s0); B = 0.5*(s1+s0)
            ys = A*gx + B
            M[i, p*q:(p+1)*q] = Lam(xi - ys) * (A*gw)
    S = np.sqrt(wts)
    Msym = (S[:, None] * M) / S[None, :]
    Msym = 0.5*(Msym + Msym.T)
    ev = np.linalg.eigvalsh(Msym)
    order = np.argsort(ev)[::-1]
    ev = ev[order]; Vsym = None
    w, V = np.linalg.eigh(Msym)
    idx = np.argsort(w)[::-1]
    mu = w[idx[0]]
    vec = V[:, idx[0]] / S
    vec = vec / np.sqrt(np.sum(vec**2 * wts))
    return mu, nodes, vec, wts

def ray_quotient(vec, nodes, wts):
    """对给定 f 直接算 <Tf,f>/<f,f>"""
    n = len(nodes)
    Tf = np.empty(n)
    for i in range(n):
        Tf[i] = np.sum(Lam(nodes[i] - nodes) * vec * wts)
    return float(np.sum(Tf * vec * wts) / np.sum(vec**2 * wts))

print("=" * 78)
print("锚点自检（常数密度 f=1 on [-1/2,1/2] 应给 K=triKer, C=1.1564940036）")
C_rho, C_den, norm, k0, extras = family_numbers(lambda x: np.ones_like(x), 0.5)
print(f"  C_rho={C_rho:.10f}   C_den={C_den:.10f}   ∫f^2={norm:.8f}  K(0)={k0:.6f}")
print(f"  ∫Γ^2(1-sinc^2)={extras[0]:.10f}   ∫Γ·Λ={extras[1]:.10f}  (=J1?)")

print("=" * 78)
print("候选核族（a=1/2, lambda_eff=1）")
fams = {}
fams["常数 → K=triKer(Γ)"] = lambda x: np.ones_like(x)
s = np.sqrt(2.0) * np.sin(1.0/np.sqrt(2.0))
fams["cos-window (S6 最优核)"] = lambda x: np.cos(np.sqrt(2.0)*x)/s
for p in (0.5, 1.0, 2.0):
    fams[f"(a^2-x^2)^{p}"] = (lambda p: (lambda x: np.maximum(0.0, 0.25-x**2)**p))(p)
for k in (1.0, 2.0, 4.0):
    fams[f"cos({k}πx)"] = (lambda k: (lambda x: np.cos(k*np.pi*x)))(k)
for c in (2.0, 4.0, 8.0, 16.0):
    fams[f"exp(-{c}x^2) 截断"] = (lambda c: (lambda x: np.exp(-c*x**2)))(c)
rows = []
for name, f in fams.items():
    C_rho, C_den, norm, k0, ex = family_numbers(f, 0.5)
    rows.append((name, C_rho, C_den))
for name, C_rho, C_den in sorted(rows, key=lambda r: r[1]):
    print(f"  {name:28s} C_rho={C_rho:.7f}   C_den={C_den:.7f}   差={C_rho-C_den:+.2e}  超1.125={C_rho-1.125:+.7f}")

print("=" * 78)
print("双参数族 f=1+beta*x^2 的最优 beta")
best = None
for beta in np.arange(-40.0, 10.01, 0.5):
    C_rho, C_den, *_ = family_numbers(lambda x, b=beta: 1.0 + b*x**2, 0.5)
    if best is None or C_rho < best[1]:
        best = (beta, C_rho, C_den)
print(f"  网格最优 beta={best[0]:.2f} → C_rho={best[1]:.7f} C_den={best[2]:.7f}")
lo, hi = best[0]-1, best[0]+1
for _ in range(60):
    m1 = lo + (hi-lo)/3; m2 = hi - (hi-lo)/3
    v1 = family_numbers(lambda x, b=m1: 1.0+b*x**2, 0.5)[0]
    v2 = family_numbers(lambda x, b=m2: 1.0+b*x**2, 0.5)[0]
    if v1 < v2: hi = m2
    else: lo = m1
bb = 0.5*(lo+hi)
C_rho, C_den, *_ = family_numbers(lambda x, b=bb: 1.0+b*x**2, 0.5)
print(f"  三分法 beta*={bb:.6f} → C_rho={C_rho:.9f}  C_den={C_den:.9f}")

print("=" * 78)
print("变分最优核：算子 T f(x)=∫ Lam(x-y) f(y) dy 于 L^2([-a,a]) 的最大特征值 mu1")
for a, tag in ((0.5, "lambda_eff=1  (a=1/2)"), (0.25, "lambda_eff=1/2 (a=1/4)")):
    for P in (100, 200, 400):
        mu, nodes, vec, wts = nystrom_top(a, P=P, q=12)
        print(f"  {tag}  P={P:4d}  mu1={mu:.10f}  → C=2-mu1={2-mu:.10f}  残差={ray_quotient(vec,nodes,wts)-mu:+.1e}")

mu, nodes, vec, wts = nystrom_top(0.5, P=400, q=12)
print(f"\n  最优核(a=1/2): mu1={mu:.10f}, C_min=2-mu1={2-mu:.10f}, 距 1.125 = {2-mu-1.125:+.10f}")
print("  特征函数 f*(x) 采样（even, 归一 ∫f^2=1）:")
sel = [i for i in range(len(nodes)) if nodes[i] >= 0][::20]
for i in sel:
    print(f"    x={nodes[i]:+.5f}   f={vec[i]:+.6f}")
print(f"    f*(0)={vec[np.argmin(np.abs(nodes))]:.6f}   f*(±1/2 附近)={vec[-1]:.6f}")
# 把特征函数当密度喂进 C_rho 泛函，看两种泛函是否一致
interp = lambda x: np.interp(x, nodes, vec, left=0.0, right=0.0)
C_rho, C_den, norm, k0, ex = family_numbers(interp, 0.5)
print(f"  用 f* 求 C_rho={C_rho:.9f} ; C_den={C_den:.9f}  (差 {C_rho-C_den:+.2e})")
