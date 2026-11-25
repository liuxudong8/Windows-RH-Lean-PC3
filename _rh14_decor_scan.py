# -*- coding: utf-8 -*-
"""RH_14 归档静态骨架扫描：找出「装饰壳」（theorem 的 body 是单个常量，而那个常量的类型里
根本不含该定理的假设类型 -> 假设在该定理内不可能被消费）。
两遍读盘：pass1 收集参考常量名 + gate 消费记录；pass2 只为被引用的常量建类型索引。
纯排除用途，不采纳任何结论。
"""
import os, re, sys, time

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT  = r"C:\proj2\_rh14_decor_scan_report.md"
RAW  = r"C:\proj2\_rh14_decor_flagged.txt"

GATES = ["Row0b", "VWinAt", "VWin", "Green", "Hyps", "HypsAlt", "EveryCharacter",
         "ZeroFreeAll", "OpenLiteratureStatements", "RecTExists", "TLiftK", "GeoOne",
         "RiemannHypothesis", "RHofG", "Row0", "RowSrc", "Claim",
         "HolomorphicLefschetzFormula"]

DECL  = re.compile(r"^(theorem|lemma)\s+([^\s:{([]+)", re.M)
STOP  = re.compile(r"^(theorem|lemma|def|structure|class|end|namespace|section|instance)\b")
IDRE  = re.compile(r"([ \t\r\n]*)(@?[A-Za-z_\u0370-\u03ff][\w.'!?]*)")


def scan_decls(text):
    for m in DECL.finditer(text):
        start = m.start()
        line = text.count("\n", 0, start) + 1
        i, depth, sep = m.end(), 0, None
        limit = min(len(text), start + 14000)
        while i < limit:
            ch = text[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0:
                if text[i:i + 2] == ":=":
                    sep = i
                    break
                if text[i:i + 6] == " where":
                    break
                if ch == "\n":
                    nxt = text[i + 1:i + 1 + 12]
                    if STOP.match(nxt):
                        break
            i += 1
        if sep is None:
            continue
        stmt = text[start:sep]
        body = text[sep + 2:]
        m2 = IDRE.match(body)
        thin, ref = False, None
        if m2:
            ref = m2.group(2).lstrip("@")
            rest = body[m2.end():]
            s = rest.strip()
            if s == "":
                thin = True
            elif rest.startswith(("\n", "\r\n")):
                nxt = rest.lstrip("\r\n")
                first = nxt.split("\n", 1)[0]
                thin = not first.startswith((" ", "\t"))
            yield (m.group(1), m.group(2), line, stmt, thin, ref)
            continue
        yield (m.group(1), m.group(2), line, stmt, thin, ref)


def binders(stmt):
    """只取显式 (...) 与隐式 {...} binder（跳过 [...] 实例，避免类型类误判）"""
    out = []
    for pat in (r"\(([^()]*)\)", r"\{([^{}]*)\}"):
        for g in re.finditer(pat, stmt):
            s = g.group(1)
            if ":" not in s:
                continue
            typ = s.split(":", 1)[1].strip()
            hm = re.match(r"(@?\w[\w.'!?]*)", typ)
            head = hm.group(1).lstrip("@") if hm else ""
            out.append(head.split(".")[-1] if head else "")
    return out


def main():
    t0 = time.time()
    files = []
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
    n_files = len(files)

    refs, gate_rows = set(), []
    n_decl = n_thin = n_thin_binder = n_err = 0
    vacuous = []

    for p in files:
        try:
            text = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            n_err += 1
            continue
        try:
            for kind, name, line, stmt, thin, ref in scan_decls(text):
                n_decl += 1
                heads = binders(stmt)
                if thin:
                    n_thin += 1
                    if heads:
                        n_thin_binder += 1
                    if ref:
                        refs.add(ref.split(".")[-1])
                    for g in GATES:
                        if re.search(r"\b" + re.escape(g) + r"\b", stmt):
                            gate_rows.append([g, p, line, name, ref, heads])
                            break
        except Exception:
            n_err += 1
            continue
        if "structure" in text and ": Prop" in text:
            lines = text.split("\n")
            for idx, ln in enumerate(lines):
                if re.match(r"^structure\s+[^\s:{([]+.*:\s*Prop.*where\s*$", ln):
                    nf = 0
                    for j in range(idx + 1, min(idx + 40, len(lines))):
                        s = lines[j]
                        if not s.strip():
                            continue
                        if s.startswith((" ", "\t")):
                            nf += 1
                            continue
                        break
                    if nf == 0:
                        vacuous.append((p, idx + 1, ln.strip()[:120]))

    print("[pass1] files=%d decls=%d thin=%d thin_with_binder=%d refs=%d gaterows=%d vacuous=%d err=%d  %.1fs"
          % (n_files, n_decl, n_thin, n_thin_binder, len(refs), len(gate_rows), len(vacuous), n_err,
             time.time() - t0))

    idx = {}
    for p in files:
        try:
            text = open(p, encoding="utf-8", errors="ignore").read()
            for kind, name, line, stmt, thin, ref in scan_decls(text):
                last = name.split(".")[-1]
                if last in refs:
                    idx.setdefault(last, [])
                    if len(idx[last]) < 3:
                        idx[last].append(stmt[:600])
        except Exception:
            continue
    print("[pass2] indexed=%d  %.1fs" % (len(idx), time.time() - t0))

    def verdict(g, ref):
        if not ref:
            return "NO-REF"
        cands = idx.get(ref.split(".")[-1])
        if not cands:
            return "UNKNOWN"
        return "PASS" if any(g in c for c in cands) else "DECO"

    rows, deco, unk = [], 0, 0
    for g, p, line, name, ref, heads in gate_rows:
        if not ref:
            rows.append((g, p, line, name, "NO-REF", ref))
            continue
        v = verdict(g, ref)
        if v == "DECO":
            deco += 1
        elif v == "UNKNOWN":
            unk += 1
        rows.append((g, p, line, name, v, ref))

    per = {}
    for r in rows:
        d = per.setdefault(r[0], {"n": 0, "deco": 0, "pass": 0, "unk": 0, "noref": 0})
        d["n"] += 1
        d[{"DECO": "deco", "PASS": "pass", "UNKNOWN": "unk"}.get(r[4], "noref")] += 1

    with open(RAW, "w", encoding="utf-8") as f:
        for r in rows:
            f.write("%s\t%s\t%s\t%s\t%s\t%s\n"
                    % (r[4], r[0], os.path.relpath(r[1], ROOT), r[2], r[3], r[5]))

    L = ["# RH_14 归档 · 装饰壳静态扫描（第 1 步）\n",
         "扫描根：`%s`\n" % ROOT,
         "- `.lean` 文件：**%d**（读盘失败 %d）" % (n_files, n_err),
         "- `theorem` / `lemma`：**%d**" % n_decl,
         "- 薄壳（body 为单个常量）：**%d**，其中带显式 binder：**%d**" % (n_thin, n_thin_binder),
         "- 零字段 `structure … : Prop where`：**%d**\n" % len(vacuous),
         "判定口径：对每个「消费 gate 的薄壳定理」，查其**引用常量的类型**里是否出现该 gate。",
         "不出现 → `DECO`（该假设在此定理内结构上不可能被消费）；出现 → `PASS`；",
         "引用者在库外（Mathlib 侧）→ `UNKNOWN`；body 不是单常量 → `NO-REF`。\n",
         "## 汇总\n",
         "| gate | 消费处 | 装饰 DECO | 传递 PASS | 外部 UNKNOWN | 非薄壳 |",
         "|---|---|---|---|---|---|"]
    for g in GATES:
        d = per.get(g)
        if not d:
            continue
        L.append("| `%s` | %d | **%d** | %d | %d | %d |"
                 % (g, d["n"], d["deco"], d["pass"], d["unk"], d["noref"]))
    L.append("")
    L.append("总计：DECO **%d** / PASS **%d** / UNKNOWN **%d**\n" % (deco, sum(d["pass"] for d in per.values()), unk))
    L.append("## 装饰样例（前 60）\n")
    n = 0
    for r in rows:
        if r[4] != "DECO":
            continue
        L.append("- `%s` — `%s:%d` `%s := %s`"
                 % (r[0], os.path.relpath(r[1], ROOT), r[2], r[3], r[5]))
        n += 1
        if n >= 60:
            break
    L.append("")
    if vacuous:
        L.append("## 零字段 Prop 结构（前 40）\n")
        for p, line, ln in vacuous[:40]:
            L.append("- `%s:%d` — `%s`" % (os.path.relpath(p, ROOT), line, ln))
        L.append("")
    open(OUT, "w", encoding="utf-8").write("\n".join(L))
    print("[done] %.1fs report=%s" % (time.time() - t0, OUT))


if __name__ == "__main__":
    main()
