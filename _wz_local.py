import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0

def dloc(g):
    return math.log(g/(2*math.pi))/(2*math.pi)

def run(centers, mode, um=25.0, kernel="sq"):
    tot = 0.0
    for g in centers:
        delta = dloc(g) if mode == "local" else dloc(T)
        if delta <= 0:
            continue
        W = um/delta
        lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
        d = z[lo:hi] - g
        d = d[d != 0.0]
        if d.size:
            if kernel == "sq":
                tot += float(np.sum(np.sinc(delta*d)**2))
            else:
                tot += float(np.sum(np.sinc(delta*d) * (4.0/(4.0 + d*d))))
    return tot/centers.size

# 均匀抽样中心（覆盖全表，避开两端 2%）
lo_i = int(0.02*z.size); hi_i = int(0.98*z.size)
idx = np.linspace(lo_i, hi_i, 6000).astype(int)
centers = z[idx]
print(f"#centers={centers.size}  gamma in [{centers[0]:.2f}, {centers[-1]:.2f}]  delta_loc range [{dloc(centers[0]):.4f}, {dloc(centers[-1]):.4f}]")
print(f"{'口径':>28} {'非对角/N':>10} {'A = 1+·':>9} {'理论':>8} {'差':>9}")
t0 = time.time()
for mode in ("global", "local"):
    t1 = time.time()
    r = run(centers, mode, kernel="sq")
    print(f"{'去权式 sinc^2, δ='+mode:>28} {r:10.5f} {1+r:9.5f} {4/3:8.4f} {1+r-4/3:9.5f}   [{time.time()-t1:.0f}s]")
print(f"总耗时 {time.time()-t0:.0f}s")
