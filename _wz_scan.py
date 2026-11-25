import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0
NL = (T/(2*math.pi))*math.log(T/(2*math.pi)) - T/(2*math.pi)   # 解析主项
NT = (T/(2*math.pi))*math.log(T)                              # 定理口径分母
print(f"#zeros={z.size}  N_L={NL:.0f}  (T/2pi)logT={NT:.0f}  logT/2pi={math.log(T)/(2*math.pi):.5f}  log(T/2pi)/2pi={math.log(T/(2*math.pi))/(2*math.pi):.5f}")
print(f"{'delta':>7} {'1/delta':>8} {'sum':>11} {'A(N_L)':>9} {'A(T/2pi logT)':>14}")

def pairsum(delta, um=25.0):
    W = um/delta
    acc = 0.0
    for s in range(0, z.size, 60000):
        zi = z[s:s+60000]
        lo = np.searchsorted(z, zi - W, "left"); hi = np.searchsorted(z, zi + W, "right")
        for k in range(zi.size):
            d = z[lo[k]:hi[k]] - zi[k]
            d = d[d != 0.0]
            if d.size:
                acc += float(np.sum(np.sinc(delta*d)**2))
    return acc

t0 = time.time()
for delta in (1.40, 1.50, 1.60, 1.70, 1.80, 1.8708, 1.95, 2.05, 2.1623, 2.25):
    s = pairsum(delta)
    print(f"{delta:7.4f} {1/delta:8.4f} {s:11.0f} {1+s/NL:9.5f} {1+s/NT:14.5f}")
print(f"耗时 {time.time()-t0:.1f}s  C_eta(flat)=1.33333")
