import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0
D1 = math.log(T) / (2 * math.pi)          # 2.16329  定理字面
D2 = math.log(T / (2 * math.pi)) / (2 * math.pi)

def A(centers, delta_fn, kernel="sq", wt=25.0):
    tot = 0.0; n = 0
    for g in centers:
        d = delta_fn(g)
        if d <= 0: continue
        W = wt / d
        lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
        dd = z[lo:hi] - g; dd = dd[dd != 0.0]
        if dd.size == 0: continue
        v = np.sinc(d*dd)**2 if kernel == "sq" else np.sinc(d*dd)*(4.0/(4.0+dd*dd))
        tot += float(np.sum(v))
        n += 1
    return 1.0 + tot / max(n, 1)

def pick(lo, hi, n):
    m = (z >= lo) & (z <= hi)
    zz = z[m]
    if zz.size <= n: return zz
    idx = np.linspace(0, zz.size - 1, n).astype(int)
    return zz[idx]

print("=" * 100)
print("PART C  分段诊断：δ 固定 = logT/2π = 2.1633，按 γ 段切中心，看残差集中在哪")
print("=" * 100)
print(f"{'段':>26} {'#centers':>9} {'gamma范围':>26} {'δ/局部密度':>12} {'A':>9} {'残差4/3':>9}")
segs = [(14, 300), (300, 3000), (3000, 30000), (30000, 300000), (300000, T)]
t0 = time.time()
for a, b in segs:
    cc = pick(a, b, 5000)
    if cc.size == 0:
        print(f"{f'[{a},{b}]':>26} {'0':>9}"); continue
    mid = math.sqrt(a*b) if a > 0 else b
    dens = math.log(mid/(2*math.pi))/(2*math.pi)
    aq = A(cc, lambda g: D1, "sq")
    print(f"{f'[{a},{b}]':>26} {cc.size:9d} {f'{cc[0]:.0f}..{cc[-1]:.0f}':>26} {D1/dens:12.3f} {aq:9.5f} {aq-4/3:+9.5f}")
print(f"[{time.time()-t0:.0f}s]")

print("\n" + "=" * 100)
print("PART D  局部窗口判决：若 δ=logT/2π 的对象是 T 的邻域，则把中心收到 [T/c, T] 应闭合")
print("=" * 100)
print(f"{'中心窗口':>20} {'δ口径':>26} {'#centers':>9} {'A':>9} {'残差4/3':>9} {'残差5/4(w)':>11}")
MODES = [("D1 logT/2pi", lambda g: D1), ("D2 log(T/2pi)/2pi", lambda g: D2),
         ("D3 pw log(g/2pi)/2pi", lambda g: math.log(g/(2*math.pi))/(2*math.pi))]
wins = [("all [0.02,0.98]", 0, T), ("[T/2, T]", T/2, T), ("[0.9T, T]", 0.9*T, T), ("[T/e, T]", T/math.e, T)]
t0 = time.time()
for wn, a, b in wins:
    cc = pick(a, b, 8000) if a > 0 else pick(1e3, b, 8000)
    for mn, fn in MODES:
        aq = A(cc, fn, "sq"); aw = A(cc, fn, "w")
        print(f"{wn:>20} {mn:>26} {cc.size:9d} {aq:9.5f} {aq-4/3:+9.5f} {aw-5/4:+11.5f}")
    print()
print(f"[{time.time()-t0:.0f}s]")
