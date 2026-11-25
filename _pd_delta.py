import numpy as np, math, time, os

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"

def load(T, key="zeta"):
    f = S + rf"\{key}_T{int(T)}.npz"
    return np.sort(np.load(f)[key].astype(float))

def stats(centers, z, delta_fn, kernel):
    """A = 1 + (1/#centers) * sum_{gamma' != gamma} K(delta*(gamma'-gamma))"""
    tot = 0.0
    for g in centers:
        d = delta_fn(g)
        if d <= 0:
            continue
        W = 25.0 / d
        lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
        dd = z[lo:hi] - g
        dd = dd[dd != 0.0]
        if dd.size == 0:
            continue
        arg = d * dd
        if kernel == "sq":
            tot += float(np.sum(np.sinc(arg) ** 2))
        else:
            tot += float(np.sum(np.sinc(arg) * (4.0 / (4.0 + dd * dd))))
    return tot / centers.size

def centers_of(z, n):
    lo_i = int(0.02 * z.size); hi_i = int(0.98 * z.size)
    idx = np.linspace(lo_i, hi_i, n).astype(int)
    return z[idx]

print("=" * 96)
print("PART A  归一化刻度判决（T=8e5, 20000 中心等距抽样, 全表 partner）")
print("  理论: 去权式 sinc^2 -> 4/3 = 1.3333 ; 加权式 sinc*w -> 5/4 = 1.2500")
print("=" * 96)
T = 800000.0
z = load(T)
n0 = z.size
D_THEO = math.log(T) / (2 * math.pi)
D_RVM  = math.log(T / (2 * math.pi)) / (2 * math.pi)
print(f"#zeros={n0}  gamma in [{z[0]:.1f}, {z[-1]:.1f}]")
print(f"D_theo = logT/2pi        = {D_THEO:.5f}")
print(f"D_rvm  = log(T/2pi)/2pi  = {D_RVM :.5f}    ratio D_theo/D_rvm = {D_THEO/D_RVM:.5f}")
print(f"1/avg spacing (RvM)      = log(T/2pi)/2pi = {D_RVM:.5f}  (本表实际平均间距 T/N = {T/n0:.5f})")

cent = centers_of(z, 20000)
MODES = {
    "D1 theo const  logT/2pi":        lambda g: D_THEO,
    "D2 rvm  const  log(T/2pi)/2pi":  lambda g: D_RVM,
    "D3 pointwise  log(g/2pi)/2pi":   lambda g: math.log(g / (2 * math.pi)) / (2 * math.pi),
    "D4 pointwise  log(g)/2pi":       lambda g: math.log(g) / (2 * math.pi),
}
print(f"\n{'delta 口径':>32} {'A(sinc^2)':>11} {'残差4/3':>9} {'A(sinc*w)':>11} {'残差5/4':>9}")
t0 = time.time()
res = {}
for name, fn in MODES.items():
    t1 = time.time()
    aq = 1.0 + stats(cent, z, fn, "sq")
    aw = 1.0 + stats(cent, z, fn, "w")
    res[name] = (aq, aw)
    print(f"{name:>32} {aq:11.5f} {aq-4/3:9.5f} {aw:11.5f} {aw-5/4:9.5f}   [{time.time()-t1:.0f}s]")
print(f"PART A 总耗时 {time.time()-t0:.0f}s")

print("\n" + "=" * 96)
print("PART B  有限高度判决：残差是否 ∝ log(2pi)/log(T/2pi)  (= logT/log(T/2pi) - 1)")
print("  若成立，P-delta 结案为『渐近无害的归一化偏差』，不是缺一层数学")
print("=" * 96)
Ts = [40000, 100000, 200000, 400000, 800000]
print(f"{'T':>9} {'#zeros':>9} {'D1 const':>9} {'A(D1)':>9} {'res(D1)':>9} {'A(D2)':>9} {'res(D2)':>9} {'pred':>9} {'res/pred':>9}")
t0 = time.time()
rows = []
for T in Ts:
    zz = load(T)
    n = zz.size
    cc = centers_of(zz, 15000)
    d1 = math.log(T) / (2 * math.pi)
    d2 = math.log(T / (2 * math.pi)) / (2 * math.pi)
    a1 = 1.0 + stats(cc, zz, lambda g: d1, "sq")
    a2 = 1.0 + stats(cc, zz, lambda g: d2, "sq")
    pred = math.log(2 * math.pi) / math.log(T / (2 * math.pi))   # = 1 - 1/(logT/log(T/2pi)) 的近似
    r1 = a1 - 4/3
    rows.append((T, n, d1, a1, r1, a2, a2 - 4/3, pred))
    print(f"{T:9d} {n:9d} {d1:9.5f} {a1:9.5f} {r1:+9.5f} {a2:9.5f} {a2-4/3:+9.5f} {pred:9.5f} {r1/pred:+9.5f}")
print(f"PART B 总耗时 {time.time()-t0:.0f}s")

print("\n【判读】")
print("  res(D2) ~ 1.5% 且与 T 无关  => 归一化用 log(T/2pi) 就闭合，P-delta 不是数学缺口")
print("  res(D1) ~ -pred 且 pred ∝ 1/logT => D1 的偏差是纯渐近项")
