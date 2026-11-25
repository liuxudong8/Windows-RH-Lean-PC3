import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"

def A_full(T, W_u=50.0, kernel="sq", step=None):
    z = np.sort(np.load(S + rf"\zeta_T{int(T)}.npz")["zeta"].astype(float))
    n = z.size
    st = step or max(1, n // 200000)
    tot = 0.0; cnt = 0
    for s in range(0, n, 40000):
        zi = z[s:s+40000:st]
        for g in zi:
            d = math.log(g / (2 * math.pi)) / (2 * math.pi)
            if d <= 0: continue
            W = W_u / d
            lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
            dd = z[lo:hi] - g; dd = dd[dd != 0.0]
            if dd.size == 0: continue
            v = np.sinc(d*dd)**2 if kernel == "sq" else np.sinc(d*dd)*(4.0/(4.0+dd*dd))
            tot += float(np.sum(v)); cnt += 1
    return 1.0 + tot / cnt, n, cnt

print("=" * 100)
print("PART H  全表（几乎全零点作中心）δ 逐点 log(g/2pi)/2pi, W_u=50")
print("   目标：去权式 -> 4/3 (+0.3333 非对角)，加权式 -> 5/4 (+0.25)")
print("=" * 100)
print(f"{'T':>9} {'#zeros':>9} {'#centers':>9} {'A(sinc^2)':>11} {'非对角':>9} {'离1/3':>9} {'相对%':>8} {'A(sinc*w)':>11} {'非对角':>9} {'离1/4':>9} {'耗时':>6}")
rows = []
for T in (40000, 100000, 200000, 400000, 800000):
    t0 = time.time()
    aq, n, c = A_full(T, 50.0, "sq")
    aw, _, _ = A_full(T, 50.0, "w")
    dt = time.time() - t0
    ndq = aq - 1.0; ndw = aw - 1.0
    rows.append((T, aq, aw))
    print(f"{T:9d} {n:9d} {c:9d} {aq:11.5f} {ndq:9.5f} {ndq-1/3:+9.5f} {100*(ndq-1/3)/(1/3):8.2f} "
          f"{aw:11.5f} {ndw:9.5f} {ndw-0.25:+9.5f} {dt:6.0f}s")

print("\n" + "=" * 100)
print("PART I  是否 O(1/logT)：非对角残差 vs 1/log(T/2pi)")
print("=" * 100)
print(f"{'T':>9} {'1/log(T/2pi)':>14} {'残差(去权)':>12} {'残差/1log':>11} {'残差(加权)':>12} {'残差/1log':>11}")
for T, aq, aw in rows:
    L = math.log(T / (2 * math.pi))
    rq = (aq - 1.0) - 1/3
    rw = (aw - 1.0) - 0.25
    print(f"{T:9d} {1/L:14.5f} {rq:+12.5f} {rq*L:+11.5f} {rw:+12.5f} {rw*L:+11.5f}")
