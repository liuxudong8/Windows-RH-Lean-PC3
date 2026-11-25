# -*- coding: utf-8 -*-
"""第 2 条：定位所有真空命题（: Prop := True / UnusedSlot* / NoCondition*），
并把它们的全部消费点列出来（定义 / 被证 / 当前件槽 / 作结构字段 / 其它引用）。纯静态。"""
import os, re, time, collections

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT  = r"C:\proj2\_rh14_vacuous_sites.md"

VACDEF = re.compile(r"(?:def|abbrev|theorem|lemma)\s+([^\s:{([]+)[^\n]{0,300}?:\s*Prop\s*:=\s*True")
NAMEHIT = re.compile(r"[^\s:{([]*UnusedSlot\w*|[^\s:{([]*NoCondition\w*")

def main():
    t0 = time.time()
    files = []
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))

    vacdefs = []          # (name, rel, line)
    names = set()
    for p in files:
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        rel = os.path.relpath(p, ROOT)
        for m in VACDEF.finditer(t):
            nm = m.group(1)
            if nm.endswith("_holds") and "UnusedSlot" in nm:
                pass
            vacdefs.append((nm, rel, t.count("\n", 0, m.start()) + 1))
            names.add(nm.split(".")[-1])
        for m in NAMEHIT.finditer(t):
            names.add(m.group(0).split(".")[-1])
    print("[pass1] vacdefs=%d names=%d  %.1fs" % (len(vacdefs), len(names), time.time() - t0))
    for nm in sorted(names):
        print("   name:", nm)

    sites = collections.defaultdict(list)   # name -> [(rel, line, label, text)]
    for p in files:
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        rel = os.path.relpath(p, ROOT)
        for i, ln in enumerate(t.split("\n"), 1):
            hit = None
            for nm in names:
                if nm in ln:
                    hit = nm
                    break
            if not hit:
                continue
            s = ln.strip()
            if s.startswith(("--", "/-", "*")):
                continue
            if re.search(r"\b(def|abbrev|structure)\b", s) and re.search(r"\s*:\s*Prop\s*:=\s*True", ln):
                lab = "DEF(=True)"
            elif re.search(r"\b(def|abbrev|structure)\b", s) and ("UnusedSlot" in s or "NoCondition" in s):
                lab = "DEF"
            elif re.search(r":=\s*trivial\s*$", s):
                lab = "PROVE-BY-TRIVIAL"
            elif re.search(r"\b(theorem|lemma)\b", s):
                lab = "SIGNATURE(槽)"
            elif re.search(r"\s:\s.*UnusedSlot|\s:\s.*NoCondition", s):
                lab = "FIELD(结构字段)"
            elif "→" in s and ("UnusedSlot" in s or "NoCondition" in s) and not s.startswith(("theorem", "lemma")):
                lab = "ARROW(前件链)"
            else:
                lab = "REF(引用)"
            sites[hit].append((rel, i, lab, s[:260]))

    L = ["# RH_14 · 真空命题及其全部消费点（第 2 条）\n", "根：`%s`\n" % ROOT,
         "## 一、定义为恒真的命题（`: Prop := True`）\n"]
    for nm, rel, line in vacdefs:
        L.append("- `%s` — `%s:%d`" % (nm, rel.replace(os.sep, "/"), line))
    L.append("\n## 二、逐命题的消费点\n")
    for nm in sorted(sites):
        L.append("### `%s`（%d 处）\n" % (nm, len(sites[nm])))
        cnt = collections.Counter(s[2] for s in sites[nm])
        L.append("分类：" + "，".join("%s %d" % (k, v) for k, v in cnt.most_common()) + "\n")
        for rel, line, lab, text in sites[nm][:40]:
            L.append("- `[%s]` %s:%d — `%s`" % (lab, rel.replace(os.sep, "/"), line, text))
        if len(sites[nm]) > 40:
            L.append("- …（余 %d 处，见脚本可重跑）" % (len(sites[nm]) - 40))
        L.append("")
    open(OUT, "w", encoding="utf-8").write("\n".join(L))
    print("[done] %.1fs -> %s" % (time.time() - t0, OUT))
    for nm in sorted(sites):
        c = collections.Counter(s[2] for s in sites[nm])
        print(nm, len(sites[nm]), dict(c))


if __name__ == "__main__":
    main()
