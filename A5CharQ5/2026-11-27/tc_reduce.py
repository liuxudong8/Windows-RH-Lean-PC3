# 作用引理约化路径：BFS 搜索从 L 到 R 的重写序列（规则 A: a²b→b²a³, B: ba²→a³b²），为 Lean calc 提供 rw 依据
# 字表示：0=a, 1=b（逐字母），幂 a^n 用 n 个 0、b^n 用 n 个 1；a^5=1, b^3=1 归并
import sys
from collections import deque

def perm_mul(p, q):
    return tuple(p[q[i]] for i in range(5))

s = (1,2,3,4,0)
t = (1,2,0,3,4)
ident = tuple(range(5))

def ev(word):
    e = ident
    for g in word:
        e = perm_mul(e, s if g == 0 else t)
    return e

def reduce_rel(word):
    # 用 a^5=1, b^3=1 消去全幂（循环），并归并相邻同生成元
    w = list(word)
    changed = True
    while changed:
        changed = False
        # 找 a^5 或 b^3 连续段消去
        i = 0
        while i < len(w):
            j = i
            while j < len(w) and w[j] == w[i]: j += 1
            cnt = j - i
            if (w[i] == 0 and cnt >= 5) or (w[i] == 1 and cnt >= 3):
                # 保留 cnt % mod 个
                mod = 5 if w[i] == 0 else 3
                newcnt = cnt % mod
                w = w[:i] + [w[i]] * newcnt + w[j:]
                changed = True
                break
            i = j
        if changed: continue
        # 归并（其实消段已处理；这里补一个通用归并）
        merged = [w[0]] if w else []
        for x in w[1:]:
            if merged and merged[-1] == x:
                merged.append(x)  # 保留逐字母（不归并，保持字长不变）
            else:
                merged.append(x)
        w = merged
    return tuple(w)

def apply_A(w):
    # a^2 b -> b^2 a^3：找 0,0,1 子串
    for i in range(len(w) - 2):
        if w[i] == 0 and w[i+1] == 0 and w[i+2] == 1:
            return reduce_rel(w[:i] + (1,1,0,0,0) + w[i+3:]), ("A", i)
    return None, None

def apply_B(w):
    # b a^2 -> a^3 b^2：找 1,0,0 子串
    for i in range(len(w) - 2):
        if w[i] == 1 and w[i+1] == 0 and w[i+2] == 0:
            return reduce_rel(w[:i] + (0,0,0,1,1) + w[i+3:]), ("B", i)
    return None, None

def apply_C(w):
    # a^2 b a^2 -> b^2（自 (a²b)²=1：a²ba² = b⁻¹ = b²）
    for i in range(len(w) - 4):
        if w[i] == 0 and w[i+1] == 0 and w[i+2] == 1 and w[i+3] == 0 and w[i+4] == 0:
            return reduce_rel(w[:i] + (1,1) + w[i+5:]), ("C", i)
    return None, None

def apply_D(w):
    # b a^2 b -> a^3（共轭 (a²b)²：ba²ba² = 1 → ba²b = a³）
    for i in range(len(w) - 3):
        if w[i] == 1 and w[i+1] == 0 and w[i+2] == 0 and w[i+3] == 1:
            return reduce_rel(w[:i] + (0,0,0) + w[i+4:]), ("D", i)
    return None, None

def apply_E(w):
    # b^2 a^2 -> a^3 b（(a²b)²=1 的又一变形：b²a² = a³b？验证：b²a² vs a³b）
    # 数学：a²ba² = b² → 左乘 a³b² 右侧... 直接置换验证后再启用
    # b^2 a^2 = b·b·a·a。用 B 规则：baa → a³b² 不行（需要 baa 子串）。bbaa 无。
    return None, None

def apply_Di(w):
    # a^3 -> b a^2 b
    for i in range(len(w) - 2):
        if w[i] == 0 and w[i+1] == 0 and w[i+2] == 0:
            return reduce_rel(w[:i] + (1,0,0,1) + w[i+3:]), ("Di", i)
    return None, None

def apply_Ai(w):
    # b^2 a^3 -> a^2 b
    for i in range(len(w) - 4):
        if w[i] == 1 and w[i+1] == 1 and w[i+2] == 0 and w[i+3] == 0 and w[i+4] == 0:
            return reduce_rel(w[:i] + (0,0,1) + w[i+5:]), ("Ai", i)
    return None, None

def apply_Bi(w):
    # a^3 b^2 -> b a^2
    for i in range(len(w) - 4):
        if w[i] == 0 and w[i+1] == 0 and w[i+2] == 0 and w[i+3] == 1 and w[i+4] == 1:
            return reduce_rel(w[:i] + (1,0,0) + w[i+5:]), ("Bi", i)
    return None, None

def apply_Ci(w):
    # b^2 -> a^2 b a^2
    for i in range(len(w) - 1):
        if w[i] == 1 and w[i+1] == 1:
            return reduce_rel(w[:i] + (0,0,1,0,0) + w[i+2:]), ("Ci", i)
    return None, None

def apply_F(w):
    # a b a -> a^4 b^2 a^4（共轭 B：a·(ba²)·a⁻¹ 变形）
    for i in range(len(w) - 2):
        if w[i] == 0 and w[i+1] == 1 and w[i+2] == 0:
            return reduce_rel(w[:i] + (0,0,0,0,1,1,0,0,0,0) + w[i+3:]), ("F", i)
    return None, None

def apply_Fi(w):
    # a^4 b^2 a^4 -> a b a
    for i in range(len(w) - 9):
        if tuple(w[i:i+10]) == (0,0,0,0,1,1,0,0,0,0):
            return reduce_rel(w[:i] + (0,1,0) + w[i+10:]), ("Fi", i)
    return None, None

def apply_G(w):
    # b^2 a^2 b^2 -> b a^3 b
    for i in range(len(w) - 5):
        if tuple(w[i:i+6]) == (1,1,0,0,1,1):
            return reduce_rel(w[:i] + (1,0,0,0,1) + w[i+6:]), ("G", i)
    return None, None

def apply_Gi(w):
    # b a^3 b -> b^2 a^2 b^2
    for i in range(len(w) - 4):
        if tuple(w[i:i+5]) == (1,0,0,0,1):
            return reduce_rel(w[:i] + (1,1,0,0,1,1) + w[i+5:]), ("Gi", i)
    return None, None

def bfs(start, goal, max_depth=16):
    start = reduce_rel(start)
    goal = reduce_rel(goal)
    q = deque([(start, [])])
    seen = {start}
    while q:
        w, path = q.popleft()
        if len(path) > max_depth: continue
        if w == goal:
            return path
        for fn, name in [(apply_A, "A"), (apply_Ai, "Ai"), (apply_B, "B"), (apply_Bi, "Bi"),
                         (apply_C, "C"), (apply_Ci, "Ci"), (apply_D, "D"), (apply_Di, "Di"),
                         (apply_F, "F"), (apply_Fi, "Fi"), (apply_G, "G"), (apply_Gi, "Gi")]:
            nw, step = fn(w)
            if nw is not None and nw not in seen:
                seen.add(nw)
                q.append((nw, path + [step]))
    return None

cases = {
  # L, R 逐字母（0=a, 1=b）
  "a7":  ("a·c7 = c8·a", (0,0,1,0,1), (1,0,1,1,0)),
  "a9":  ("a·c9 = c5·a²", (0,1,1,0,1), (1,0,1,0,0)),
  "a10": ("a·c10 = c9·a²", (0,0,1,0,1,1), (1,1,0,1,0,0)),
  "a11": ("a·c11 = c11·a⁴", (0,1,0,1,0,1,1), (1,0,1,0,1,1,0,0,0,0)),
  "b6":  ("b·c6 = c4·a³", (1,0,0,1,1), (0,1,1,0,0,0)),
  "b7":  ("b·c7 = c10·a⁴", (1,0,1,0,1), (0,1,0,1,1,0,0,0,0)),
  "b8":  ("b·c8 = c6·a²", (1,1,0,1,1), (0,0,1,1,0,0)),
  "b11": ("b·c11 = c7·a", (1,1,0,1,0,1,1), (0,1,0,1,0)),
}

for name, (desc, L, R) in cases.items():
    ok = ev(L) == ev(R)
    print(f"{name}: {desc} 置换验证={'OK' if ok else 'FAIL'}")
    if not ok:
        print(f"  L={ev(L)} R={ev(R)}")
        continue
    path = bfs(L, R)
    if path is None:
        path = bfs(R, L)
        if path is not None:
            # 反转路径
            path = list(reversed(path))
            print(f"  反向路径: {' -> '.join(f'{s[0]}(@{s[1]})' for s in path)}")
            w = reduce_rel(L)
            for st in path:
                fn = {"A": apply_A, "Ai": apply_Ai, "B": apply_B, "Bi": apply_Bi,
                      "C": apply_C, "Ci": apply_Ci, "D": apply_D, "Di": apply_Di}[st[0]]
                nw, _ = fn(w)
                w = nw
                if w is None:
                    print("    → ?")
                    continue
                pairs = []
                for x in w:
                    if pairs and pairs[-1][0] == x:
                        pairs[-1] = (x, pairs[-1][1] + 1)
                    else:
                        pairs.append((x, 1))
                wstr = "".join(("a" if g == 0 else "b") + (str(e) if e > 1 else "") for g, e in pairs)
                print(f"    → {wstr}")
            continue
        print(f"  无重写路径（深度16内）")
        continue
    steps = " -> ".join(f"{s[0]}(@{s[1]})" for s in path)
    print(f"  路径: {steps}")
    # 显示中间字（幂对形式）
    w = reduce_rel(L)
    for st in path:
        fn = {"A": apply_A, "Ai": apply_Ai, "B": apply_B, "Bi": apply_Bi,
              "C": apply_C, "Ci": apply_Ci, "D": apply_D, "Di": apply_Di,
              "F": apply_F, "Fi": apply_Fi, "G": apply_G, "Gi": apply_Gi}[st[0]]
        nw, _ = fn(w)
        w = nw
        if w is None:
            print("    → ?")
            continue
        # 转幂对
        pairs = []
        for x in w:
            if pairs and pairs[-1][0] == x:
                pairs[-1] = (x, pairs[-1][1] + 1)
            else:
                pairs.append((x, 1))
        wstr = "".join(("a" if g == 0 else "b") + (str(e) if e > 1 else "") for g, e in pairs)
        print(f"    → {wstr}")
