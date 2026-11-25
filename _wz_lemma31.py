import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0
N = z.size
D_THEO = math.log(T)/(2*math.pi)          # Lemma 3.1 的自变量尺度: z = Delta * logT/(2pi)
D_LOC  = math.log(T/(2*math.pi))/(2*math.pi)
print(f"#zeros={N}  delta_theo=logT/2pi={D_THEO:.5f}   delta_loc=log(T/2pi)/2pi={D_LOC:.5f}")
print("理论：Lemma 3.1 加权式 (核 K=sinc, 权重 w)  →  对角+N 后 1 + 非对角/N = 5/4 = 1.25  ⟹ 非对角/N = 0.25")
print("      Lemma 3.2 去权式 (核 K^2=sinc^2, 无权重) → 1 + 非对角/N = 4/3 = 1.3333 ⟹ 非对角/N = 0.3333")

def run(delta, um=25.0):
    W = um/delta
    aw = 0.0   # weighted, kernel sinc, weight w = 4/(4+Delta^2)
    aq = 0.0   # unweighted, kernel sinc^2
    for s in range(0, N, 50000):
        zi = z[s:s+50000]
        lo = np.searchsorted(z, zi - W, "left"); hi = np.searchsorted(z, zi + W, "right")
        for k in range(zi.size):
            d = z[lo[k]:hi[k]] - zi[k]
            d = d[d != 0.0]
            if d.size:
                aw += float(np.sum(np.sinc(delta*d) * (4.0/(4.0 + d*d))))
                aq += float(np.sum(np.sinc(delta*d)**2))
    return aw/N, aq/N

print(f"\n{'delta':>8} {'加权式 非对角/N':>16} {'A_w':>8} {'(理论 0.25)':>11} {'去权式 非对角/N':>17} {'A_q':>8} {'(理论 0.3333)':>13}")
for name, delta in (("theo", D_THEO), ("loc", D_LOC)):
    t0 = time.time()
    rw, rq = run(delta)
    print(f"{delta:8.5f} {rw:16.5f} {1+rw:8.5f} {rw-0.25:+11.5f} {rq:17.5f} {1+rq:8.5f} {rq-1/3:+13.5f}   [{name}] {time.time()-t0:.0f}s")
