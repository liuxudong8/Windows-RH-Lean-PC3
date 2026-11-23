import numpy as np
def sinc(x):
    x=np.asarray(x,float); return np.where(np.abs(x)<1e-13,1.0,np.sin(x)/x)
u=np.linspace(1e-6,40.0,300000); du=np.diff(np.concatenate([[0.0],u]))
rho2=1.0-sinc(np.pi*u)**2
f=lambda a: float(np.sum(rho2*sinc(2*np.pi*a*u)**2*du))
lo,hi=0.50,0.70
for _ in range(40):
    mid=(lo+hi)/2
    if f(mid)>0.125: lo=mid
    else: hi=mid
print("uniform 端：a*=%.6f  (λ_eff*=%.6f)  Q=%.8f"%(hi,2*hi,f(hi)))
print("关键点： a=0.5 Q=%.6f | a=0.55 Q=%.6f | a=0.60 Q=%.6f"%(f(0.5),f(0.55),f(0.60)))
