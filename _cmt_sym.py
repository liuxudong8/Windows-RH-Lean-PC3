import sympy as sp

u = sp.symbols('u', real=True)
expr = (1 - u)**2 * (sp.sin(sp.pi*u)/(sp.pi*u))**2
val = sp.integrate(expr, (u, 0, 1))
print("sympy J1/2 =", sp.simplify(val))
print("numeric:", sp.N(2*val, 20))
print("C_K =", sp.N(1 + sp.Rational(2,3) - 2*val, 20))
