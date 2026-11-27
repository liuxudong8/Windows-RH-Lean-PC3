# 独立 BFS：b_7 尾段 R4 -> R9（词级），fwd 规则
# R4 = abbabaaaab, R9 = ababbaaaa
import sys
from collections import deque

RULES = [
    ("rule2_fwd", "aabaa", "bb"),
    ("rule3_fwd", "baab", "aaa"),
    ("rule4_fwd", "aba", "aaaabbaaaa"),
    ("rule7_fwd", "baaaab", "aaabaaa"),
    ("rule8_fwd", "bba", "aabaaa"),
    ("rule1_fwd", "aab", "bbaaa"),
    ("rule0_fwd", "baa", "aaabb"),
    ("rule6_fwd", "bbbb", "b"),
    ("rule5_fwd", "bbaabb", "baaab"),
]

START = "abbabaaaab"
GOAL = "ababbaaaa"

def neighbors(w):
    out = []
    for name, pat, rep in RULES:
        i = w.find(pat)
        while i != -1:
            nw = w[:i] + rep + w[i+len(pat):]
            out.append((nw, f"{name}@{i}:{w[i:i+len(pat)]}"))
            i = w.find(pat, i+1)
    return out

# BFS with depth limit
limit = 6
q = deque([(START, 0, [])])
seen = {START}
found = None
while q:
    w, d, path = q.popleft()
    if d >= limit:
        continue
    for nw, desc in neighbors(w):
        if nw == GOAL:
            found = (w, d+1, path + [desc])
            break
        if nw not in seen and d+1 < limit:
            seen.add(nw)
            q.append((nw, d+1, path + [desc]))
    if found:
        break

if found:
    w, d, path = found
    print("FOUND depth", d)
    cur = START
    for p in path:
        print("  ", cur, "->", p)
        name, rest = p.split("@", 1)
        pos_s, pat = rest.split(":", 1)
        pos = int(pos_s)
        rep = dict((r[0], r[2]) for r in RULES)[name]
        cur = cur[:pos] + rep + cur[pos+len(pat):]
    print("  final", cur, "== GOAL?", cur == GOAL)
else:
    print("NOT FOUND within depth", limit)
    # 报一下可达深度 3 内的全部词，供手工核对
    q = deque([(START, 0, [])])
    seen = {START}
    d3 = []
    while q:
        w, d, path = q.popleft()
        if d == 3:
            d3.append((w, path))
            continue
        if d > 3:
            continue
        for nw, desc in neighbors(w):
            if nw not in seen:
                seen.add(nw)
                q.append((nw, d+1, path + [desc]))
    print("words at depth<=3:")
    for w, path in sorted(d3)[:20]:
        print("  ", w, path)
