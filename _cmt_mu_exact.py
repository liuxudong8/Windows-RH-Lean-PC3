# -*- coding: utf-8 -*-
"""算子 T f(x) = ∫_[-a,a] triKer(x-y) f(y) dy 的谱：解析特征方程 + 高精度根
推导：Tf 求导两次 ⟹ (Tf)'' = -2f ⟹ mu f'' = -2f ⟹ k^2 = 2/mu, f = A cos(kx)+B sin(kx)
边界：g := Tf - mu f 为线性，g' = 0 给出
   偶支 (B=0): tan(ka) = a / ((1-a) ka)
   奇支 (A=0): cos(ka) = 0  ⟹  ka = pi/2 + n pi
a = 1/2 时：偶支 tan v = 1/v (v=ka)；奇支 k=(2n+1)pi
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def Lam(t):
    return np.maximum(0.0, 1.0 - np.abs(t))

a = 0.5

def even_eq(v, a=0.5):
    return mp.tan(v) - a / ((1.0 - a) * v)

print("=" * 84)
print("偶支最小正根 v1 (tan v = 1/v, a=1/2)")
v1 = mp.findroot(lambda v: mp.tan(v) - 1.0/v, mp.mpf('0.86'))
print(f"  v1 = {mp.nstr(v1, 25)}")
mu1 = 1.0/(2.0*v1**2)
print(f"  mu1 = 1/(2 v1^2) = {mp.nstr(mu1, 25)}")
print(f"  C_min = 2 - mu1   = {mp.nstr(2-mu1, 25)}")
print(f"  距 7/8(0.875)     = {mp.nstr(mp.mpf('0.875')-mu1, 12)}")
print(f"  对 Galerkin 外推 0.67551694 的差 = {mp.nstr(mu1-mp.mpf('0.67551694'), 6)}")

print("\n偶支全部正根 v_n（v tan v = 1，即 v sin v - cos v = 0）与 mu = 1/(2v^2)")
def even_root(n):
    lo = mp.pi*n + mp.mpf('1e-10') if n == 0 else mp.pi*n + mp.mpf('1e-6')
    hi = mp.pi*n + mp.pi/2 - mp.mpf('1e-6')
    return mp.findroot(lambda v: v*mp.sin(v) - mp.cos(v), (lo, hi))
evens = [even_root(n) for n in range(6)]
print("  n   v_n                      mu = 1/(2v^2)")
for n, r in enumerate(evens):
    print(f"  {n}   {mp.nstr(r, 18):<24} {mp.nstr(1.0/(2.0*r**2), 15)}")

print("\n奇支 mu = 2/((2n+1)^2 pi^2)")
for n in range(3):
    print(f"  n={n}  mu = {mp.nstr(2.0/((2*n+1)**2*mp.pi**2), 15)}")

print("=" * 84)
print("与分片常数 Galerkin 数值谱对照（N=400 的前 5 个）")
num = [0.6755166621, 0.202641, 0.0426074, 0.022515, 0.012065]
allmu = [('even', 1.0/(2.0*r**2), f'v={mp.nstr(r,8)}') for r in evens]
allmu += [('odd', 2.0/((2*n+1)**2*mp.pi**2), f'ka={n}+1/2') for n in range(6)]
allmu.sort(key=lambda x: -x[1])
print("  解析谱前 6（含分支标签）：")
for tag, m, lab in allmu[:6]:
    print(f"    {tag:5s} {mp.nstr(m, 15):<20} {lab}")
print("  Galerkin 数值前 5：", num)

print("=" * 84)
print("点值校验：T f = mu f 于 cos(2 v1 x)")
xs = np.linspace(-a, a, 4001)
k = float(2*v1)
f = np.cos(k*xs)
# Tf 用精确式：∫(1-|x-y|)cos(ky)dy
def Tcos(x, k, a):
    # 解析：对每点用数值高精度代替（细分积分）
    val = np.zeros_like(x)
    for i, xi in enumerate(x):
        yy = np.linspace(-a, a, 20001)
        val[i] = np.trapezoid(Lam(xi - yy)*np.cos(k*yy), yy)
    return val
Tf = Tcos(xs, k, a)
mu_num = float(mu1)
res = Tf - mu_num*f
print(f"  max|Tf - mu f| = {np.max(np.abs(res)):.3e}   (f 的 max = 1)")
print(f"  数值 Rayleigh 商 = {float(np.trapezoid(Tf*f, xs)/np.trapezoid(f*f, xs)):.10f}")
print(f"  mu1(解析)        = {float(mu1):.10f}")
