import numpy as np
def sinc(x):
    x=np.asarray(x,float); return np.where(np.abs(x)<1e-13,1.0,np.sin(x)/x)
u=np.linspace(1e-6,40.0,250000); du=np.diff(np.concatenate([[0.0],u])); rho2=1.0-sinc(np.pi*u)**2
def Q(f,a,nx=40001):
    x=np.linspace(-a,a,nx); v=f(x)
    K=np.array([np.trapezoid(v*np.cos(2*np.pi*uu*x),x) for uu in u[::20]])
    return float(np.trapezoid(rho2[::20]*K*K,u[::20]))
par=lambda a:(lambda x: (3.0/(4*a))*(1-(x/a)**2))
cospi=lambda a:(lambda x: np.cos(np.pi*x/(2*a))*(np.pi/(2*a))/(2*np.sin(np.pi/2)))
c2=lambda a:(lambda x: np.cos(np.pi*x/a)*(np.pi/a)/(2*np.sin(np.pi)))
for a in [0.50,0.55,0.575,0.60,0.65]:
    print("a=%.3f  Q_par=%.6f  Q_cos(π/2a)=%.6f  Q_cos(π/a)=%.6f"%(a,Q(par(a),a),Q(cospi(a),a),Q(c2(a),a)))
