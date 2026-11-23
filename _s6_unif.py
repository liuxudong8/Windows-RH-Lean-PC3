import numpy as np
def sinc(x):
    x=np.asarray(x,float); return np.where(np.abs(x)<1e-13,1.0,np.sin(x)/x)
u=np.linspace(1e-6,40.0,200000)
du=np.diff(np.concatenate([[0.0],u]))
rho2=1.0-sinc(np.pi*u)**2
def Q_unif(a):
    K=sinc(2*np.pi*a*u)
    return float(np.sum(rho2*K*K*du))
def Q_cos(a):
    s2=np.sqrt(2.0); x=np.linspace(-a,a,40001)
    f=np.cos(s2*x/a*(a/0.5*0.5*2))  # placeholder
    return None
print("=== uniform 核族 Q_uniform(a) （最光滑端）===")
for a in [0.45,0.5,0.55,0.6,0.667,0.7,0.8,0.9,1.0,1.2,1.5]:
    Q=Q_unif(a); print("a=%.3f  Q=%.6f  A=%.6f  2-A=%.6f %s"%(a,Q,1+Q,2-(1+Q), "<=7/8 越过" if Q<=0.125 else ""))
