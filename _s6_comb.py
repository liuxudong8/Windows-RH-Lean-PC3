import numpy as np
src=open("_s6_qp2.py",encoding="utf-8").read().split("# 锚点")[0]
exec(src)
for a in [0.55,0.56,0.57,0.58]:
    Q,f,edges,raw=min_q(a,n=200,iters=6000)
    print("a=%.3f Q_min=%.6f  A=%.6f  2-A=%.6f"%(a,Q,1+Q,2-(1+Q)))
# 光滑档（Tikhonov）在 a=0.575 附近
def min_q_pen(a,n,beta,iters=6000):
    A,h,edges=build(a,n)
    D=np.zeros((n-1,n))
    for i in range(n-1): D[i,i]=-1.0; D[i,i+1]=1.0
    C=A/h**2 + (beta*8*a**3/h)*(D.T@D)
    L=2.0*float(np.linalg.eigvalsh(C)[-1])
    g=np.full(n,1.0/n); y=g.copy(); tk=1.0
    for k in range(iters):
        xn=proj_simplex(y-2.0*C@y/L)
        tn=(1+np.sqrt(1+4*tk**2))/2.0
        yn=xn+((tk-1)/tn)*(xn-g)
        if (yn@C@yn)>(xn@C@xn): yn=xn.copy(); tn=1.0
        g,y,tk=xn,yn,tn
    return Qval(g,A,h)
for beta in [1.0,10.0]:
    Q=min_q_pen(0.575,200,beta)
    print("a=0.575 beta=%.1f Q=%.6f A=%.6f"%(beta,Q,1+Q))
