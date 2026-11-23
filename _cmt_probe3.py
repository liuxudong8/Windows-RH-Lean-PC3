import mpmath as mp
mp.mp.dps = 40

pi = mp.pi
def sinc2(u):
    if u == 0:
        return mp.mpf(1)
    return (mp.sin(pi*u)/(pi*u))**2

# 分裂积分，避免 |u| 折点
J1 = 2*mp.quad(lambda u: (1-u)**2*sinc2(u), [0, 1])
print("J1 (split quad) =", mp.nstr(J1, 20))
print("sympy 闭式 =", mp.nstr(2*((-mp.log(4*pi**2)/2 - mp.euler + mp.ci(2*pi) + mp.mpf(1)/2 + pi*mp.si(2*pi))/pi**2), 20))
CK = 1 + mp.mpf(2)/3 - J1
print("C_K =", mp.nstr(CK, 20), "  2-C_K =", mp.nstr(2-CK, 20))
print("67/60 =", mp.nstr(mp.mpf(67)/60, 20), "  53/60 =", mp.nstr(mp.mpf(53)/60, 20), "  1/120 =", mp.nstr(mp.mpf(1)/120, 10))
