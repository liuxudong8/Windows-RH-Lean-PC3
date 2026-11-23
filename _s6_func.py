# -*- coding: utf-8 -*-
"""反推 S6 的 A 泛函：K=f̂（密度余弦变换，∫f=1，K(0)=1），A=1+∫_0^∞ ρ2 |f̂|² du。
与 S6 实测表（_dump_s6 段[23]/[25]）对表。
"""
import numpy as np

def sinc(x):
    x = np.asarray(x, float)
    return np.where(np.abs(x) < 1e-13, 1.0, np.sin(x) / x)

def rho2(u):
    return 1.0 - sinc(np.pi * u) ** 2

def K_of(f, a, us, nx=20001):
    """f 定义在 [-a,a] 上（callable），返回 f̂(u)=∫ f(x)cos(2πux)dx"""
    x = np.linspace(-a, a, nx)
    v = f(x)
    out = np.empty_like(us)
    for i, uu in enumerate(us):
        out[i] = np.trapezoid(v * np.cos(2 * np.pi * uu * x), x)
    return out

s2 = np.sqrt(2.0)
f0 = lambda x: np.cos(s2 * x) / (s2 * np.sin(1.0 / s2))

def f_lam(lam):
    return lambda x: f0(x / lam) / lam

us = np.linspace(1e-4, 40.0, 120000)
print("rho2 check: rho2(0.5)=%.6f (=1), rho2(0.25)=%.6f" % (rho2(0.5), rho2(0.25)))

rows = []
# f0 @ lam=0.5
for lam in [0.30, 0.35, 0.40, 0.45, 0.48, 0.50]:
    f = f_lam(lam)
    K = K_of(f, lam / 2.0, us)
    val = np.trapezoid(rho2(us) * K ** 2, us)
    rows.append((lam, K[0], 1.0 + val))

print("\n%-6s %-10s %-12s %-10s" % ("lam", "K(0)", "A_model", "A_meas(ζ)"))
meas = {0.30: 2.7535, 0.35: 2.3957, 0.40: 2.1325, 0.45: 1.9322, 0.48: 1.8353, 0.50: 1.1868}
for lam, k0, A in rows:
    print("%-6.2f %-10.4f %-12.6f %-10.4f" % (lam, k0, A, meas.get(lam, float('nan'))))

# 均匀核 Γ（∫f=1 于 [-1/2,1/2]）
f_unif = lambda x: np.full_like(x, 1.0)  # ∫_{-1/2}^{1/2} 1 dx = 1 ✓
K = K_of(f_unif, 0.5, us)
A_unif = 1.0 + np.trapezoid(rho2(us) * K ** 2, us)
print("\nuniform Γ (λ=0.5): K(0)=%.4f  A_model=%.6f  (=7/6? %.6f)" % (K[0], A_unif, 7/6))
# 解析口径：∫_0^∞(1-sinc²)sinc² = 1/2 - 1/3 = 1/6
print("analytic ∫_0^∞ ρ2 sinc²(πu) du = %.6f" % (0.5 - 1.0/3.0))
