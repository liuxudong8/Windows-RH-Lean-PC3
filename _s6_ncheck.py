import numpy as np
exec(open("_s6_qp2.py", encoding="utf-8").read().split("# 锚点")[0])
for a in [0.50, 0.60]:
    for n in [50, 100, 200, 400]:
        Q, f, edges, raw = min_q(a, n=n, iters=4000 if n <= 200 else 2000)
        print("a=%.2f n=%3d  Q_min=%.6f  A=%.6f  peak/mean=%.2f" % (a, n, Q, 1+Q, f.max()/(1/(2*a)),))
