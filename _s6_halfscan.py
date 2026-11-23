# -*- coding: utf-8 -*-
"""钉 12%：对 half 做扫描，并同时检验 δ 的口径。
口径（S6 原样，有序对、不含对角）：A = 1 + Σ_{i≠j, |δΔ|≤half} K(δΔ)² / N_i
K 为 f₀ 的余弦变换（与 make_K_mt 同式），此处用 FFT 精确取样（步长 1/128，覆盖 u≤8192）。
对照曲线：g≡1 与 GUE(g = 1 − sinc²) 的同一截断值。
"""
import numpy as np, os, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"

# ---- K(u) = ∫ f0(x) cos(2πux) dx,  f0 在 [-1/2,1/2] ----
M = 1 << 21
W = 64.0
dx = 2 * W / M
x = -W + np.arange(M) * dx
s2 = np.sqrt(2.0)
f0 = np.where(np.abs(x) <= 0.5, np.cos(s2 * x) / (s2 * np.sin(1.0 / s2)), 0.0)
KK = np.real(np.fft.rfft(f0)) * dx          # 频率步长 1/(M dx) = 1/(2W)
KK = KK * ((-1.0) ** np.arange(KK.size))    # f 居中在 M/2 ⟹ DFT 带 e^{-iπk} 相位，必须消掉
du = 1.0 / (2 * W)
ug = np.arange(KK.size) * du
print("K(0)=%.9f  ∫K²du=%.9f (应 = Q(0) ≈ 1.006130)" % (KK[0], np.trapezoid(KK**2, ug)))

def Kint(u):
    return np.interp(u, ug, KK, left=KK[0], right=0.0)

def references(H):
    """同一截断下的两条参考曲线（有序对 → 2∫₀^H）。"""
    m = ug <= H
    uu, kk = ug[m], KK[m]
    a_g1 = 1.0 + 2.0 * np.trapezoid(kk**2, uu)
    sinc2 = np.where(uu < 1e-12, 1.0, (np.sin(np.pi * uu) / (np.pi * uu))**2)
    a_gue = 1.0 + 2.0 * np.trapezoid((1.0 - sinc2) * kk**2, uu)
    return a_g1, a_gue

# ---- 零点：ζ 到 8e5 ----
z = np.sort(np.asarray(np.load(os.path.join(S, "zeta_T800000.npz"))["zeta"], float))
Tref = 7.95e5
deltaS6 = np.log(Tref) / (2 * np.pi)          # 2.163…（S6 原口径）
deltaLoc = np.log(Tref / (2 * np.pi)) / (2 * np.pi)   # 1.8709…（真实平均间距密度）
print("n=%d  γ∈[%.1f,%.1f]  δ_S6=%.6f  δ_loc=%.6f  比=%.4f"
      % (z.size, z[0], z[-1], deltaS6, deltaLoc, deltaS6 / deltaLoc))

BAND = (7.2e5, 7.95e5)
idx = np.where((z >= BAND[0]) & (z <= BAND[1]))[0]
step = max(1, idx.size // 8000)
ii = idx[::step]
print("i 样本数 = %d（带内共 %d 个零点）" % (ii.size, idx.size))

def scan(delta, Hs, Hmax):
    acc = np.zeros(len(Hs))
    UMAX = Hmax * delta
    for i in ii:
        zi = z[i]
        lo = np.searchsorted(z, zi - UMAX, "left")
        hi = np.searchsorted(z, zi + UMAX, "right")
        d = np.abs(z[lo:hi] - zi)
        d = d[d > 1e-9]
        u = delta * d
        kv2 = Kint(u) ** 2
        for k, H in enumerate(Hs):
            acc[k] += kv2[u <= H].sum()
    return acc / ii.size + 1.0

t0 = time.time()
Hs = [2.0, 5.0, 10.0, 20.0, 40.0, 80.0, 160.0, 400.0]
print("\n[A] half 扫描，δ = δ_loc（真实间距）")
A_loc = scan(deltaLoc, Hs, max(Hs))
print("  half    A_loc      g≡1 参考   GUE 参考")
for k, H in enumerate(Hs):
    g1, gue = references(H)
    print("  %6.1f  %.6f   %.6f    %.6f" % (H, A_loc[k], g1, gue))

print("\n[B] 同一 half 下两种 δ 的对表（复现 S6 的 1.1868 并给出修正值）")
A_s6 = scan(deltaS6, [40.0], 40.0)[0]
g1, gue = references(40.0)
print("  δ_S6 (2.1630)，half=40 ⟹ A = %.6f   （S6 实测 1.1868）" % A_s6)
print("  δ_loc(1.8709)，half=40 ⟹ A = %.6f" % A_loc[4])
print("  同 half 下 g≡1 参考 %.6f ／ GUE 参考 %.6f ；定理常数 C_MT = 1.3274993" % (g1, gue))
print("\n耗时 %.1fs" % (time.time() - t0))
