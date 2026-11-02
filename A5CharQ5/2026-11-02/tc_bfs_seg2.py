# -*- coding: utf-8 -*-
"""双向 BFS：为所有坏段找真实引理词路径（逐段状态上限防爆炸）。"""
import sys
from collections import deque

RULES = [
    ("baa", "aaabb"),          # 0 b_a2_comm
    ("aab", "bbaaa"),          # 1 a2_b_comm
    ("aabaa", "bb"),           # 2 a2_b_a2_eq_b2
    ("baab", "aaa"),           # 3 b_a2_b_eq_a3
    ("aba", "aaaabbaaaa"),     # 4 a_b_a_eq_a4_b2_a4
    ("bbaabb", "baaab"),       # 5 b2_a2_b2_eq_b_a3_b
    ("bbbb", "b"),             # 6 pB_pow_four
    ("baaaab", "aaabaaa"),     # 7 hbab4
    ("bba", "aabaaa"),         # 8 hba
]

def rewrites(w, cap):
    out = []
    for idx, (l, r) in enumerate(RULES):
        for d, (pat, rep) in ((1, (l, r)), (-1, (r, l))):
            start = 0
            while True:
                p = w.find(pat, start)
                if p < 0:
                    break
                nw = w[:p] + rep + w[p+len(pat):]
                if len(nw) <= cap:
                    out.append((p, idx, d, nw))
                start = p + 1
    return out

def bi_bfs(start, goal, max_depth=12, cap=48, seen_limit=400000):
    if start == goal:
        return []
    # 前向：start->word, path=[(pos,ridx,d)]；后向：goal->word, path 反向累积
    f_q = deque([(start, [])])
    b_q = deque([(goal, [])])
    f_seen = {start: []}
    b_seen = {goal: []}
    depth = 0
    while f_q and b_q and depth < max_depth:
        depth += 1
        # 扩展前向一层
        for _ in range(len(f_q)):
            w, path = f_q.popleft()
            for pos, ridx, d, nw in rewrites(w, cap):
                if nw in f_seen:
                    continue
                f_seen[nw] = path + [(pos, ridx, d)]
                if nw in b_seen:
                    return f_seen[nw] + list(reversed(b_seen[nw]))
                f_q.append((nw, f_seen[nw]))
                if len(f_seen) > seen_limit:
                    return None, len(f_seen) + len(b_seen)
        # 扩展后向一层
        for _ in range(len(b_q)):
            w, path = b_q.popleft()
            for pos, ridx, d, nw in rewrites(w, cap):
                if nw in b_seen:
                    continue
                b_seen[nw] = path + [(pos, ridx, d)]
                if nw in f_seen:
                    fwd = f_seen[nw]
                    bwd = list(reversed(b_seen[nw]))
                    return fwd + bwd
                b_q.append((nw, b_seen[nw]))
                if len(b_seen) > seen_limit:
                    return None, len(f_seen) + len(b_seen)
    return None, len(f_seen) + len(b_seen)

def fmt_path(start, goal, path):
    w = start
    lines = []
    for pos, ridx, d in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        w = w[:pos] + rep + w[pos+len(pat):]
        lines.append((pos, ridx, d, pat, w))
    return lines

SEGS = [
    ("b11-s1", "bbababb", "aabaaababbb"),
    ("b11-s2", "aabaaababbb", "aabaaabaaabaa"),
    ("b11-s3", "aabaaabaaabaa", "aabbaabbaaabaa"),
    ("b11-s4", "aabbaabbaaabaa", "aabbaaaabbaa"),
    ("b11-s5", "aabbaaaabbaa", "aaaababbaa"),
    ("b11-s6", "aaaababbaa", "aaaabaaabaaaa"),
    ("b11-s7", "aaaabaaabaaaa", "aaaabbaabbaaaa"),
    ("b11-s8", "aaaabbaabbaaaa", "aaaabbaaaabba"),
    ("b11-s9", "aaaabbaaaabba", "ababa"),
    ("b7-tail", "abbaabaaaab", "abaabbaaaa"),
    ("a11-B",  "abaaabaaaabbbbaa", "abaaababaaaa"),
    ("a11-C",  "abaaababaaaa", "abbaabbaabaaaa"),
    ("a11-D",  "abbaabbaabaaaa", "aaabaaaaaabbaabaaaa"),
    ("a11-D2", "aaabaaaaaabbaabaaaa", "aaabaaabaaabaaaa"),
    ("a11-B2", "aaabaaabaaabaaaa", "bbaabbaabaaaabaaaa"),
    ("a11-C2", "bbaabbaabaaaabaaaa", "baaaabaaabaaabaaaa"),
    ("a11-G",  "baaaabaaabaaabaaaa", "baaaabbbaaabbaaabaaaa"),
    ("a11-A",  "baaaabbbaaabbaaabaaaa", "baaaabbbaaaaabbaaaa"),
    ("a11-A2", "baaaabbbaaaaabbaaaa", "baabaabbaaaa"),
]

for name, start, goal in SEGS:
    print(f"==== {name}  {start} -> {goal}", flush=True)
    res = bi_bfs(start, goal)
    if isinstance(res, tuple):
        print(f"  NO PATH / limit ({res[1]} states)", flush=True)
        continue
    path = res
    steps = fmt_path(start, goal, path)
    for (pos, ridx, d, pat, w) in steps:
        print(f"    pos={pos} rule{ridx} {'fwd' if d==1 else 'rev'} {pat} -> {w}", flush=True)
    print(f"  steps={len(path)} goal_reached={w == goal}", flush=True)
