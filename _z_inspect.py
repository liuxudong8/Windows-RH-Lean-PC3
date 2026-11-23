# -*- coding: utf-8 -*-
"""先看清零点表：键名、条数、范围、平均间距（决定 δ 与带状归一是否可用）。"""
import numpy as np, os
S = r"C:\Users\shtcl\AppData\Local\Doubao\User Data\Default\.doubao\agent_mode\workspace\.sessions\38447505362182914\agents\m_0cwRdl91bFs\tmp_word_scatter"
for fn in ["zeros_T6e5.npz", "zeta_T800000.npz", "L_D5_T800000.npz"]:
    p = os.path.join(S, fn)
    d = np.load(p)
    print("==", fn, "keys:", d.files)
    for k in d.files:
        a = np.asarray(d[k]).ravel()
        if a.size == 0:
            print("   %-8s empty" % k); continue
        if a.dtype.kind in "fiu":
            print("   %-8s n=%d  min=%.6g  max=%.6g  dtype=%s" % (k, a.size, a.min(), a.max(), a.dtype))
        else:
            print("   %-8s dtype=%s size=%d" % (k, a.dtype, a.size))
