# -*- coding: utf-8 -*-
"""口径 A：候选核族的 C 值（修正版：自相关零填充 8x，积分域严格截到 [0,2a]）

两个泛函（一起算，便于看它们是否同一个东西）：
  F1(rho2 form, 与代码 pairConstant 一致): C = 1 + ∫ K(u)^2 * (1 - sinc^2(pi u)) du
  F2(density form, 文档"密度形式"):        C = 2 - ∫ K(u) * triKer(u) du
约定：f 为密度，K = f*f 归一使 K(0)=1（即 ∫f^2 = 1），supp f = [-a,a]，lambda_eff = 2a。
"""
import numpy as np

def sinc(x):
    x = np.asarray(x, float)
    out = np.ones_like(x)
    nz = x != 0.0
    out[nz] = np.sin(np.pi * x[nz]) / (np.pi * x[nz])
    return out

def triKer(t):
    return np.maximum(0.0, 1.0 - np.abs(t))

def numbers(f, a, ngrid=1 << 13):
    x = np.linspace(-a, a, ngrid)
    h = x[1] - x[0]
    fx = f(x)
    n2 = 8 * ngrid                      # 8x 零填充，杜绝回绕
    F = np.fft.rfft(fx, n2)
    ac = np.fft.irfft(F * np.conj(F), n2) * h    # 滞后 j*h
    norm = ac[0]
    if norm <= 0:
        raise ValueError("degenerate f")
    K = ac / norm
    umax = 2.0 * a
    jmax = int(round(umax / h))
    u = np.arange(jmax + 1) * h
    Kt = K[:jmax + 1]
    w = np.ones(jmax + 1); w[0] = 0.5; w[-1] = 0.5; w *= h    # 对称延拓用的梯形权
    Ik2 = 2.0 * np.sum(w * Kt ** 2)
    Isinc = 2.0 * np.sum(w * Kt ** 2 * sinc(u) ** 2)
    Ilam = 2.0 * np.sum(w * Kt * triKer(u))
    F1 = 1.0 + (Ik2 - Isinc)
    F2 = 2.0 - Ilam
    return dict(F1=F1, F2=F2, Ik2=Ik2, Isinc=Isinc, Ilam=Ilam, norm=norm, K0=K[0])

print("=" * 84)
print("锚点：常数密度 f=1 on [-1/2,1/2]（K=triKer=Γ）")
d = numbers(lambda x: np.ones_like(x), 0.5)
print(f"  ∫Γ²={d['Ik2']:.10f} (应 2/3=0.6666666667)")
print(f"  ∫Γ²sinc²={d['Isinc']:.10f} (应 J1=0.5101726630)")
print(f"  ∫Γ·triKer={d['Ilam']:.10f} (应 2/3)")
print(f"  F1={d['F1']:.10f} (应 1.1564940036)   F2={d['F2']:.10f}")
GAMMA = d

print("=" * 84)
print("候选族（a=1/2；F1 = 代码口径，F2 = 文档密度形式）")
fams = [
    ("常数 → K=Γ", lambda x: np.ones_like(x)),
    ("cos-window f0(S6)", lambda x: np.cos(np.sqrt(2)*x) / (np.sqrt(2) * np.sin(1.0/np.sqrt(2)))),
    ("cos(πx)", lambda x: np.cos(np.pi*x)),
    ("(1/4-x²)^1", lambda x: np.maximum(0, 0.25-x**2)),
    ("(1/4-x²)^2", lambda x: np.maximum(0, 0.25-x**2)**2),
    ("exp(-4x²)", lambda x: np.exp(-4*x**2)),
    ("exp(-16x²)", lambda x: np.exp(-16*x**2)),
    ("exp(-64x²)", lambda x: np.exp(-64*x**2)),
    ("exp(-256x²)", lambda x: np.exp(-256*x**2)),
]
res = []
for name, f in fams:
    d = numbers(f, 0.5)
    res.append((name, d))
for name, d in res:
    print(f"  {name:20s} F1={d['F1']:.7f} (超1.125 {d['F1']-1.125:+.7f})   F2={d['F2']:.7f}   ∫K²={d['Ik2']:.5f} ∫K²sinc²={d['Isinc']:.5f}")

print("=" * 84)
print("双参数族 f=1+βx² 的 F1 最优点")
def scan():
    best = None
    for beta in np.arange(-30.0, 5.01, 0.25):
        d = numbers(lambda x, b=beta: 1.0 + b*x*x, 0.5)
        if best is None or d['F1'] < best[1]:
            best = (beta, d['F1'], d['F2'])
    return best
print("  粗扫:", scan())
print("=" * 84)
print("支撑收缩（同一族 exp(-c x²)，a 变小 = lambda_eff 变小）——看 F1 是否随支撑收缩单调下降")
for a in (0.5, 0.25, 0.125, 0.0625):
    b1 = None
    for c in (2, 8, 32, 128, 512, 2048):
        d = numbers(lambda x, c=c: np.exp(-c*x*x), a)
        if b1 is None or d['F1'] < b1[1]:
            b1 = (c, d['F1'], d['Ilam'])
    print(f"  a={a:<7} lambda={2*a:<6} 最优 c={b1[0]:<5} F1={b1[1]:.7f}  (F2 项 ∫K·Λ={b1[2]:.5f})")
