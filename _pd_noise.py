import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0
D3 = lambda g: math.log(g / (2 * math.pi)) / (2 * math.pi)
W_u = 400.0

def per_center(cc, delta_fn, kernel="sq"):
    out = []
    for g in cc:
        d = delta_fn(g)
        if d <= 0: out.append(0.0); continue
        W = W_u / d
        lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
        dd = z[lo:hi] - g; dd = dd[dd != 0.0]
        if dd.size == 0: out.append(0.0); continue
        v = np.sinc(d*dd)**2 if kernel == "sq" else np.sinc(d*dd)*(4.0/(4.0+dd*dd))
        out.append(float(np.sum(v)))
    return np.array(out)

print("=" * 96)
print("PART G  抽样噪声判决：δ 逐点 log(g/2pi)/2pi, W_u=400; 报 mean 与 SE = std/sqrt(n)")
print("   若残差 ~ 2*SE，则 −0.74% 是 Monte Carlo 噪声，口径本身已闭合")
print("=" * 96)
print(f"{'#centers':>9} {'A(sinc^2)':>11} {'SE':>9} {'残差4/3':>10} {'残差/SE':>9} {'A(sinc*w)':>11} {'残差5/4':>10} {'残差/SE':>9} {'耗时':>6}")
for n in (8000, 20000, 50000, 100000):
    lo_i = int(0.02 * z.size); hi_i = int(0.98 * z.size)
    idx = np.linspace(lo_i, hi_i, n).astype(int)
    cc = z[idx]
    t0 = time.time()
    q = per_center(cc, D3, "sq")
    wv = per_center(cc, D3, "w")
    aq = 1 + q.mean(); aw = 1 + wv.mean()
    se_q = q.std(ddof=1) / math.sqrt(q.size)
    se_w = wv.std(ddof=1) / math.sqrt(wv.size)
    print(f"{n:9d} {aq:11.5f} {se_q:9.5f} {(aq-4/3)/se_q:+10.2f} {aq-4/3:+10.5f} {(aq-4/3)/se_q:+9.2f} "
          f"{aw:11.5f} {aw-5/4:+10.5f} {(aw-5/4)/se_w:+9.2f} {time.time()-t0:6.0f}s")

print("\n【判读】残差/SE 若在 ±3 内 => D3 口径已在统计噪声内闭合到 4/3")
