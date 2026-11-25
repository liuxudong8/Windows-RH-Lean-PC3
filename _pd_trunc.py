import numpy as np, math, time

S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
z = np.sort(np.load(S + r"\zeta_T800000.npz")["zeta"].astype(float))
T = 800000.0
D3 = lambda g: math.log(g / (2 * math.pi)) / (2 * math.pi)

lo_i = int(0.02 * z.size); hi_i = int(0.98 * z.size)
idx = np.linspace(lo_i, hi_i, 8000).astype(int)
cc = z[idx]

def A(delta_fn, W_u, kernel="sq"):
    tot = 0.0; n = 0
    for g in cc:
        d = delta_fn(g)
        if d <= 0: continue
        W = W_u / d
        lo = np.searchsorted(z, g - W, "left"); hi = np.searchsorted(z, g + W, "right")
        dd = z[lo:hi] - g; dd = dd[dd != 0.0]
        if dd.size == 0: continue
        v = np.sinc(d*dd)**2 if kernel == "sq" else np.sinc(d*dd)*(4.0/(4.0+dd*dd))
        tot += float(np.sum(v)); n += 1
    return 1.0 + tot / max(n, 1)

print("=" * 92)
print("PART E  截断收敛判决：W_u 放宽到 25/50/100/200/400（u 尺度），δ = 逐点 log(g/2pi)/2pi")
print("   若残差随 W_u 单调收敛到 ~0，则 1.6% 中有一块是截断尾巴，不是数学缺口")
print("   sinc^2 的解析尾部 2*int_{W}^inf sinc^2 = 2/(pi^2 W) :  W=25 -> 0.81%%, W=100 -> 0.20%%, W=400 -> 0.05%%")
print("=" * 92)
print(f"{'W_u':>6} {'A(sinc^2)':>11} {'残差4/3':>9} {'相对%':>8} {'A(sinc*w)':>11} {'残差5/4':>9} {'相对%':>8} {'耗时':>6}")
for W_u in (25, 50, 100, 200, 400):
    t0 = time.time()
    aq = A(D3, W_u, "sq"); aw = A(D3, W_u, "w")
    dt = time.time() - t0
    print(f"{W_u:6d} {aq:11.5f} {aq-4/3:+9.5f} {100*(aq-4/3)/(4/3):8.2f} {aw:11.5f} {aw-5/4:+9.5f} {100*(aw-5/4)/1.25:8.2f} {dt:6.0f}s")

print("\n" + "=" * 92)
print("PART F  尾部补偿（解析）：把 W_u 截断掉的解析尾巴补回去，看是否恰好闭合")
print("   int_{|u|>W} sinc^2(u) du = 2*int_W^inf sinc^2 du，乘以 d/δ 的密度因子")
print("=" * 92)
W_u = 25
aq = A(D3, W_u, "sq")
# 非对角估计：A-1。尾巴相对损失 = 2*int_W^inf sinc^2 / int_0^inf sinc^2 = 2/(pi^2 W)
loss = 2.0 / (math.pi ** 2 * W_u)
nd = aq - 1.0
print(f"  A(25) = {aq:.6f}   非对角 = {nd:.6f}   尾损失比 = {loss:.5f}")
print(f"  补偿后非对角 = {nd/(1-loss):.6f}   A_comp = {1+nd/(1-loss):.6f}   残差 = {1+nd/(1-loss)-4/3:+.6f}")
print("  （尾部分布近似均匀时这个补偿才准；若补偿后仍偏离，说明不是尾巴问题）")
