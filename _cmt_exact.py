import mpmath as mp
mp.mp.dps = 30

pi = mp.pi
def sinc2(u):
    if u == 0:
        return mp.mpf(1)
    return (mp.sin(pi*u)/(pi*u))**2

# (A) 已锚定的泛函：C(f) = 1 + ∫f² - <f*f, triKer>
#     等价于 C(K=f̂) = 1 + ∫K²(1 - sinc²(πu)) du
def C_from_density(f, lo, hi):
    Q = mp.quad(lambda x: f(x)**2, [lo, hi])
    # <f*f, tri> = ∫∫ f(y)f(z) tri(y+z)
    I = mp.quad(lambda y: mp.quad(lambda z: f(y)*f(z)*max(mp.mpf(0), 1-mp.fabs(y+z)), [lo, hi]), [lo, hi])
    return 1 + Q - I, Q, I

a = 1/mp.sqrt(2)
f0 = lambda x: mp.cos(mp.sqrt(2)*x)/(mp.sqrt(2)*mp.sin(a)) if abs(x) <= mp.mpf(1)/2 else mp.mpf(0)
uni = lambda x: mp.mpf(1) if abs(x) <= mp.mpf(1)/2 else mp.mpf(0)
tri = lambda x: max(mp.mpf(0), 1-mp.fabs(x))

C0, Q0, I0 = C_from_density(f0, -mp.mpf(1)/2, mp.mpf(1)/2)
Cu, Qu, Iu = C_from_density(uni, -mp.mpf(1)/2, mp.mpf(1)/2)
Ct, Qt, It = C_from_density(tri, -1, 1)
print("f0    : C =", mp.nstr(C0, 12), " (锚点 1.3274992963)  ∫f²=", mp.nstr(Q0,10), " ⟨f*f,tri⟩=", mp.nstr(I0,10))
print("uniform: C =", mp.nstr(Cu, 12), " (锚点 4/3 = 1.3333333333)")
print("tri(密度口径): C =", mp.nstr(Ct, 12), " ∫f²=", mp.nstr(Qt,12), " ⟨f*f,tri⟩=", mp.nstr(It,12))
print("   67/60 =", mp.nstr(mp.mpf(67)/60, 12), "   11/20 =", mp.nstr(mp.mpf(11)/20, 12))
print("   2 - C =", mp.nstr(2-Ct, 12), "  53/60 =", mp.nstr(mp.mpf(53)/60,12), "  7/8 =", mp.nstr(mp.mpf(7)/8,12))

# (B) 现行 Lean 口径：K = triKer 直接作配对核
J1 = mp.quad(lambda u: (max(mp.mpf(0), 1-mp.fabs(u)))**2*sinc2(u), [-1, 1])
CK = 1 + mp.mpf(2)/3 - J1
print("K=tri 口径: ∫Γ²sinc² =", mp.nstr(J1, 12), "  C_K =", mp.nstr(CK, 12), "  2-C_K =", mp.nstr(2-CK, 12))

# (C) 对照：若配对核取 sinc²（f=Γ 读法），∫ sinc^6 = 11/20 应成立
s6 = mp.quad(lambda u: sinc2(u)**3, [-mp.inf, mp.inf])
print("∫ sinc^6(πu) du =", mp.nstr(s6, 12), "  (11/20 = 0.55)")
