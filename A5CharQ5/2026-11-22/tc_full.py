# tc_full.py — 模拟 Lean rw 全替换语义，BFS 找 calc 中间态
# 词条 = [(gen, exp), ...]。拆幂规则返回「未合并」序列；合并/消段为显式规则。
import sys
from collections import deque

def show(w):
    return "".join(g + (str(e) if e > 1 else "") for g, e in w)

RULES = []

def add(name, pat, rep):
    def fn(w):
        w = list(w)
        out = []
        i = 0
        changed = False
        while i < len(w):
            m = i + len(pat) <= len(w) and all(w[i+k] == pat[k] for k in range(len(pat)))
            if m:
                out.extend(rep)
                i += len(pat)
                changed = True
            else:
                out.append(w[i])
                i += 1
        return tuple(out), changed
    RULES.append((name, fn))

# 引理规则（pow 级，全替换）
add("A", (('a',2),('b',1)), (('b',2),('a',3)))
add("Ai", (('b',2),('a',3)), (('a',2),('b',1)))
add("B", (('b',1),('a',2)), (('a',3),('b',2)))
add("Bi", (('a',3),('b',2)), (('b',1),('a',2)))
add("C", (('a',2),('b',1),('a',2)), (('b',2),))
add("Ci", (('b',2),), (('a',2),('b',1),('a',2)))
add("D", (('b',1),('a',2),('b',1)), (('a',3),))
add("Di", (('a',3),), (('b',1),('a',2),('b',1)))
add("F", (('a',1),('b',1),('a',1)), (('a',4),('b',2),('a',4)))
add("Fi", (('a',4),('b',2),('a',4)), (('a',1),('b',1),('a',1)))
add("G", (('b',2),('a',2),('b',2)), (('b',1),('a',3),('b',1)))
add("Gi", (('b',1),('a',3),('b',1)), (('b',2),('a',2),('b',2)))

def mk_split(gen, k, name):
    # gen^n -> gen^k * gen^(n-k)，不合并
    def fn(w):
        w = list(w)
        out = []
        changed = False
        for g, e in w:
            if g == gen and e >= 2 and k <= e - 1 and k >= 1:
                out.append((gen, k)); out.append((gen, e - k))
                changed = True
            else:
                out.append((g, e))
        return tuple(out), changed
    RULES.append((name, fn))

mk_split('a', 1, "sa1")   # a^n -> a*a^(n-1)   (← pow_succ')
mk_split('a', 2, "sa2")   # a^n -> a^2*a^(n-2) (← pow_add 拆法)
mk_split('b', 1, "sb1")   # b^n -> b*b^(n-1)
mk_split('b', 2, "sb2")   # b^n -> b^2*b^(n-2)

# 合并相邻同底幂（← pow_add）
def merge(w):
    w = list(w)
    out = []
    changed = False
    for g, e in w:
        if out and out[-1][0] == g:
            out[-1] = (g, out[-1][1] + e)
            changed = True
        else:
            out.append((g, e))
    return tuple(out), changed
RULES.append(("merge", merge))

# 消段：每个幂原子 e % mod（pA_pow_five / pB_pow_three 直接应用）
def reduce(w):
    out = []
    changed = False
    for g, e in w:
        mod = 5 if g == 'a' else 3
        if e >= mod:
            e = e % mod
            changed = True
        if e > 0:
            out.append((g, e))
    return tuple(out), changed
RULES.append(("reduce", reduce))

def bfs(start, goal, max_depth=16):
    start = tuple(start); goal = tuple(goal)
    q = deque([(start, [])])
    seen = {start}
    total = 0
    while q:
        w, path = q.popleft()
        total += 1
        if len(path) > max_depth: continue
        if w == goal:
            return path, total
        for name, fn in RULES:
            nw, changed = fn(w)
            if changed and nw not in seen:
                seen.add(nw)
                q.append((nw, path + [name]))
    return None, total

def run_case(name, S0, G, max_depth):
    path, total = bfs(S0, G, max_depth)
    print(f"== {name}: depth={max_depth}, states={total}")
    if not path:
        print("   NONE")
        return
    print("   path:", " -> ".join(path))
    w = tuple(S0)
    print("   S0 =", show(w))
    for st in path:
        fn = dict(RULES)[st]
        nw, _ = fn(w)
        w = nw
        print(f"   {st} -> {show(w)}")
    print("   final =", show(w), "| goal =", show(G))

if __name__ == "__main__":
    # b7 用例：S0 = b·a·b·a·b, 目标 = a·b·a·b^2·a^4
    S0 = (('b',1),('a',1),('b',1),('a',1),('b',1))
    G  = (('a',1),('b',1),('a',1),('b',2),('a',4))
    run_case("b7", S0, G, 16)
