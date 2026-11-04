# -*- coding: utf-8 -*-
"""解析 A5Defs.lean 中 calc 链的每一行 LHS/RHS，元素验证（数学真/假判定）。
输入：行号范围 + 起始项（change 的 LHS 元素）。
对 calc 链 `_ = RHS := by ...` 每行：验证 LHS(前一行 RHS 或起始) 元素 == RHS 元素。
"""
import itertools, re, sys

def comp(p, q):
    return tuple(p[q[i] - 1] for i in range(len(p)))

def mulp(*ps):
    r = tuple(range(1, 7))
    for p in ps:
        r = comp(p, r)
    return r

def powp(p, k):
    r = tuple(range(1, 7))
    for _ in range(k % 60):
        r = comp(p, r)
    return r

A = (2, 3, 4, 5, 1, 6)
ONE = tuple(range(1, 7))
for cand in itertools.permutations(range(1, 7)):
    if cand != ONE and powp(cand, 3) == ONE and powp(mulp(powp(A, 2), cand), 2) == ONE:
        B = cand
        break

def _parse_expr(s, i):
    """递归下降：expr := factor (* factor)*（左结合）；返回 (elem, next_index)"""
    def factor(j):
        if s[j] == '(':
            e, k = _parse_expr(s, j + 1)
            return e, k + 1
        if s[j] == 'a':
            return A, j + 1
        if s[j] == 'b':
            return B, j + 1
        if s[j] == '1':
            return ONE, j + 1
        raise ValueError(f"bad factor at {j}: {s[j:j+10]}")
    e, i = factor(i)
    while i < len(s) and s[i] == '*':
        f, i = factor(i + 1)
        e = mulp(e, f)
    return e, i

def eval_term(s):
    """s: pA * pB * pA ^ 3 形式的项 → 群元素（保留括号语义）"""
    s = s.replace(" ", "")
    s = re.sub(r'pA\^(\d+)', lambda m: '*'.join(['pA'] * int(m.group(1))), s)
    s = re.sub(r'pB\^(\d+)', lambda m: '*'.join(['pB'] * int(m.group(1))), s)
    s = s.replace("pA", "a").replace("pB", "b")
    e, i = _parse_expr(s, 0)
    return e

def check_chain(lines, start_term):
    """lines: (lineno, term) 列表；验证第 i 行 RHS == 前一行 RHS（或 start）"""
    prev = eval_term(start_term)
    bad = []
    for lineno, term in lines:
        cur = eval_term(term)
        if cur != prev:
            bad.append((lineno, term))
        prev = cur
    return bad

def main():
    path = r"C:\proj2\A5CharQ5\A5Defs.lean"
    with open(path, encoding="utf-8") as f:
        src = f.readlines()
    # 目标：coset_a_11 (1001-1085), b_6 (1087-1103), b_7 (1105-1131), b_8 (1133-1144), b_11 (1146-1178)
    # 从 change 行拿起始 LHS；_ = TERM 行收集
    for name, start, end in [("a_11", 1001, 1085), ("b_6", 1087, 1103), ("b_7", 1105, 1131),
                             ("b_8", 1133, 1144), ("b_11", 1146, 1178)]:
        start_term = None
        lines = []
        for i in range(start - 1, min(end, len(src))):
            line = src[i]
            m = re.search(r'change\s+(.+?)\s*=', line)
            if m and start_term is None:
                # change 的 LHS（等号左侧，可能跨行）——简化：取第一个 = 前
                start_term = line.split('=')[0].replace('change', '').strip()
            m2 = re.search(r'_ = (.+?) :=', line)
            if m2:
                lines.append((i + 1, m2.group(1).strip()))
        print(f"==== {name}: start = {start_term[:60]}..., {len(lines)} lines")
        if start_term is None:
            print("  no change line found")
            continue
        bad = check_chain(lines, start_term)
        if not bad:
            print("  ALL LINES MATHEMATICALLY CORRECT")
        else:
            for ln, t in bad:
                print(f"  BAD line {ln}: {t[:90]}")
        print()

if __name__ == "__main__":
    main()
