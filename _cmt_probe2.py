import numpy as np

def tri(x):
    return np.maximum(0.0, 1.0 - np.abs(x))

# 1) A(t) = (tri*tri)(t) 数值 vs 解析式 t^3/6 + (1-t) - (1-t)^3/3  (0<=t<=1)
n = 20001
y = np.linspace(-1, 1, n); dy = y[1]-y[0]
g = tri(y)
def A_num(t):
    return np.sum(g*tri(t-y))*dy
for t in [0.0, 0.25, 0.5, 0.75, 1.0]:
    if t <= 1:
        ana = t**3/6 + (1-t) - (1-t)**3/3
    print(f"t={t}: num={A_num(t):.8f}  ana={ana:.8f}")

# 2) I 的二维直算，与卷积式对照
N = 1201
xs = np.linspace(-1, 1, N); w = np.gradient(xs)
Fx = tri(xs)
X, Z = np.meshgrid(xs, xs, indexing="ij")
S = X + Z
integrand = np.outer(Fx, Fx)*np.maximum(0.0, 1.0-np.abs(S))
I2 = np.sum(integrand*np.outer(w, w))
print("I(2D direct) =", f"{I2:.8f}")
print("I(解析猜测 19/30 = 0.633333) / 11/20 = 0.55")
print("C_tri = 1 + 2/3 - I =", f"{1 + 2/3 - I2:.8f}")
