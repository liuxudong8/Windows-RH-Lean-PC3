# -*- coding: utf-8 -*-
"""残余 6% 的来源判定：在 half 已饱和（H = 200）下，看 A 随 T 的变化。
若 A 随 T 单调升向 C_MT = 1.3274993，则残余是 O(1/√logT) 的有限 T 效应；若持平，则是口径内别的东西。
口径：有序对、不含对角、A = 1 + Σ K(δΔ)²/N_i，δ 取该带真实平均间距密度 log(Tref/2π)/(2π)。
"""
import numpy as np, os, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"

M = 1 << 21
W = 64.0
dx = 2 * W / M
x = -W + np.arange(M) * dx
s2 = np.sqrt(2.0)
f0 = np.where(np.abs(x) <= 0.5, np.cos(s2 * x) / (s2 * np.sin(1.0 / s2)), 0.0)
KK = np.real(np.fft.rfft(f0)) * dx * ((-1.0) ** np.arange(M // 2 + 1))
ug = np.arange(KK.size) / (2 * W)

def run(fn, H=200.0, ntarget=4000, off=0):
    d = np.load(os.path.join(S, fn))
    k = "zeta" if "zeta" in d.files else [f for f in d.files if np.asarray(d[f]).dtype.kind == "f"][0]
    z = np.sort(np.asarray(d[k], float))
    zmax = z[-1]
    band = (0.90 * zmax, 0.995 * zmax)
    idx = np.where((z >= band[0]) & (z <= band[1]))[0]
    step = max(1, idx.size // ntarget)
    ii = idx[off::step]
    delta = np.log(0.99 * zmax / (2 * np.pi)) / (2 * np.pi)
    UMAX = H * delta
    acc = 0.0
    for i in ii:
        zi = z[i]
        lo = np.searchsorted(z, zi - UMAX, "left")
        hi = np.searchsorted(z, zi + UMAX, "right")
        dd = np.abs(z[lo:hi] - zi)
        dd = dd[dd > 1e-9]
        u = delta * dd
        acc += (np.interp(u, ug, KK, right=0.0) ** 2)[u <= H].sum()
    return acc / ii.size + 1.0, ii.size, delta, z.size

CMT = 1.3274992963
print("H = 200（截断已饱和）   C_MT = %.10f" % CMT)
print(" %-18s %8s %7s %9s %9s %9s" % ("file", "N_ζ", "i 数", "δ_loc", "A", "亏"))
t0 = time.time()
for fn in ["zeta_T40000.npz", "zeta_T100000.npz", "zeta_T200000.npz", "zeta_T400000.npz",
           "zeros_T6e5.npz", "zeta_T800000.npz"]:
    A, ni, delta, n = run(fn)
    print(" %-18s %8d %7d %9.6f %9.6f %9.4f" % (fn, n, ni, delta, A, CMT - A))
A1, ni1, _, _ = run("zeta_T800000.npz", off=0)
A2, ni2, _, _ = run("zeta_T800000.npz", off=1)
print("\n噪声探针（同表、i 抽样错开 1 位）：%.6f vs %.6f   差 %.4f" % (A1, A2, abs(A1 - A2)))
print("\n耗时 %.1fs" % (time.time() - t0))
