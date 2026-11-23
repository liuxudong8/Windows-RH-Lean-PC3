import numpy as np

a = 1/np.sqrt(2)
def f0(x):
    return np.where(np.abs(x) <= 0.5, np.cos(np.sqrt(2)*x)/(np.sqrt(2)*np.sin(a)), 0.0)

def tri(x):
    return np.maximum(0.0, 1.0 - np.abs(x))

def hfun(x):           # triKer：三角形，supp [-1,1]
    return np.maximum(0.0, 1.0 - np.abs(x))

def C_functional(f, lo, hi, n=2001):
    x = np.linspace(lo, hi, n)
    w = np.gradient(x)
    fx = f(x)
    Q = np.sum(fx*fx*w)
    # 卷积 (f*f)(t) = ∫ f(y) f(t-y) dy，t ∈ [2lo, 2hi]
    t = np.linspace(2*lo, 2*hi, 2*n-1)
    conv = np.zeros_like(t)
    # 直接二维求和，规模 2001^2 太大，改用 FFT 近似格点卷积
    Ny = n
    pad = 2*Ny
    F = np.fft.rfft(fx, pad)
    conv_circ = np.fft.irfft(F*F, pad)
    dt = (hi-lo)/(n-1)
    # t_k 对应 k*dt 位移，起点 2lo
    conv = conv_circ[:2*n-1]*dt
    hh = hfun(t)
    I = float(np.sum(conv*hh*np.gradient(t)))
    return Q, I, 1.0 + Q - I

Q0, I0, C0 = C_functional(f0, -0.5, 0.5, 4001)
Qt, It, Ct = C_functional(tri, -1.0, 1.0, 4001)
print(f"f0 : int f^2 = {Q0:.8f}   I = {I0:.8f}   C = {C0:.8f}   (目标 1.3274992963)")
print(f"tri: int f^2 = {Qt:.8f} = 2/3={2/3:.8f}   I = {It:.8f}   C = {Ct:.8f}")

# 均匀核对照
def uni(x):
    return np.where(np.abs(x) <= 0.5, 1.0, 0.0)
Qu, Iu, Cu = C_functional(uni, -0.5, 0.5, 4001)
print(f"uni: int f^2 = {Qu:.8f}   I = {Iu:.8f}   C = {Cu:.8f}")
