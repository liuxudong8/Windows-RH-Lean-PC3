# -*- coding: utf-8 -*-
"""字重写 BFS：用 7 条交换引理 + 幂关系，为 4 条坏 coset 引理搜 Lean calc 路径。
字 = 生成元序列（'a'/'b'），规则双向匹配子串。
输出：从 start 到 goal 的重写序列（每步：位置、规则、方向）。
"""
from collections import deque

# 规则：LHS 子串 -> RHS 子串（'a'^n 已展开为重复 a）
RULES = [
    ("baa", "aaabb"),      # b_a2_comm: b a^2 -> a^3 b^2
    ("aab", "bba aaa"),    # a2_b_comm: a^2 b -> b^2 a^3
    ("aabaa", "bb"),       # a2_b_a2_eq_b2: a^2 b a^2 -> b^2
    ("baab", "aaa"),       # b_a2_b_eq_a3: b a^2 b -> a^3
    ("aba", "aaaabbaaaa"), # a_b_a_eq_a4_b2_a4: a b a -> a^4 b^2 a^4
    ("bbaabb", "baaab"),   # b2_a2_b2_eq_b_a3_b: b^2 a^2 b^2 -> b a^3 b
    ("bbbb", "b"),         # pB_pow_four: b^4 -> b
]

def normalize(w):
    """约化：a^5 -> '', b^3 -> ''（幂吸收），无限次"""
    while True:
        nw = w.replace("aaaaa", "").replace("bbb", "")
        if nw == w:
            return nw
        w = nw

def rewrites(w):
    """w 的所有一步重写（双向应用规则，含位置）。返回 (pos, rule_idx, dir, neww)"""
    out = []
    for idx, (l, r) in enumerate(RULES):
        # 正向
        start = 0
        while True:
            p = w.find(l, start)
            if p < 0:
                break
            out.append((p, idx, 1, w[:p] + r + w[p+len(l):]))
            start = p + 1
        # 反向
        start = 0
        while True:
            p = w.find(r, start)
            if p < 0:
                break
            out.append((p, idx, -1, w[:p] + l + w[p+len(r):]))
            start = p + 1
    return out

def bfs(start, goal, max_depth=12):
    start, goal = normalize(start), normalize(goal)
    q = deque([(start, [])])
    seen = {start}
    while q:
        w, path = q.popleft()
        if len(path) >= max_depth:
            continue
        for pos, ridx, d, nw in rewrites(w):
            nw = normalize(nw)
            if nw in seen:
                continue
            seen.add(nw)
            np = path + [(w, pos, ridx, d, nw)]
            if nw == goal:
                return np
            q.append((nw, np))
    return None

def show_path(path, start, goal):
    w = normalize(start)
    print("start:", w)
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"  pos {pos}: {'fwd' if d == 1 else 'rev'} rule[{ridx}] {l} -> {r}  =>  {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}")
        w = nw
    print("goal:", w)

def main():
    cases = [
        ("coset_a_11", "abaababbb", "bababbbaaaa"),   # a·b·a·b·a·b·b = b·a·b·a·b·b·a⁴
        ("coset_b_7", "babab", "ababbbaaaa"),          # b·a·b·a·b = a·b·a·b·b·a⁴
        ("coset_b_8", "bbabb", "aabb aa"),             # b²·a·b·b = a²·b²·a²
        ("coset_b_11", "bbababb", "ababa"),            # b²·a·b·a·b·b = a·b·a·b·a
    ]
    for name, start, goal in cases:
        print(f"==== {name}: {start}  ->  {goal}")
        p = bfs(start, goal)
        if p is None:
            print("  NO PATH")
        else:
            show_path(p, start, goal)
            print()

if __name__ == "__main__":
    main()
