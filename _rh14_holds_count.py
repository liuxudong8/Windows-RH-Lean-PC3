# -*- coding: utf-8 -*-
"""纯静态计数：*_holds 节点规模 + 真空槽规模。不编译、不采纳任何结论。"""
import os, re, time, collections

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT  = r"C:\proj2\_rh14_holds_count.md"

DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:private |protected |noncomputable |nonrec |partial )*"
                  r"(theorem|lemma|def|abbrev|opaque)\s+([^\s:{([]+)", re.M)
VAC  = re.compile(r":\s*Prop\s*:=\s*True")
UNUSED = re.compile(r"def\s+(\w*UnusedSlot\w*|\w*NoCondition\w*)\s*[^\n]*:\s*Prop\s*:=")

def main():
    t0 = time.time()
    files, n_files = [], 0
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
    n_files = len(files)

    holds = []          # (kind, name, rel, line, is_prop_def)
    vac, unused = [], []
    for p in files:
        try:
            text = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        rel = os.path.relpath(p, ROOT)
        for m in DECL.finditer(text):
            name = m.group(2)
            if name.endswith("_holds") or name.endswith("_hold"):
                line = text.count("\n", 0, m.start()) + 1
                seg = text[m.start():m.start() + 400]
                is_prop = bool(re.search(r":\s*Prop\s*:=", seg))
                holds.append((m.group(1), name, rel, line, is_prop))
        for m in VAC.finditer(text):
            vac.append((rel, text.count("\n", 0, m.start()) + 1))
        for m in UNUSED.finditer(text):
            unused.append((rel, text.count("\n", 0, m.start()) + 1, m.group(0)[:110]))

    by_kind = collections.Counter(h[0] for h in holds)
    by_top = collections.Counter(h[2].split(os.sep)[0] for h in holds)
    n_prop = sum(1 for h in holds if h[4])
    distinct = len(set(h[1] for h in holds))

    L = ["# RH_14 · `*_holds` 节点与真空槽计数（纯静态）\n",
         "根：`%s`（%d 个 `.lean`）\n" % (ROOT, n_files),
         "## 一、`*_holds` 规模\n",
         "- 声明总数（含 `theorem/lemma/def/abbrev/opaque`）：**%d**" % len(holds),
         "- 去重后名字数：**%d**" % distinct,
         "- 其中 `def … : Prop :=` 形态：**%d**" % n_prop,
         "- 按声明种类：" + "，".join("`%s` %d" % (k, v) for k, v in by_kind.most_common()),
         "",
         "按顶层目录：",
         ""]
    for k, v in by_top.most_common(12):
        L.append("- `%s`：%d" % (k, v))
    L += ["", "## 二、真空槽规模\n",
          "- `: Prop := True` 命中：**%d**" % len(vac),
          "- `UnusedSlot* / NoCondition*` 定义：**%d**" % len(unused), ""]
    if unused:
        for rel, line, s in unused[:30]:
            L.append("- `%s:%d` — `%s`" % (rel.replace(os.sep, "/"), line, s))
        L.append("")
    L += ["## 三、`*_holds` 抽样（前 30）\n"]
    for kind, name, rel, line, is_prop in holds[:30]:
        L.append("- `%s` %s:%d — `%s`%s" % (kind, rel.replace(os.sep, "/"), line, name,
                                            "（`: Prop :=`）" if is_prop else ""))
    open(OUT, "w", encoding="utf-8").write("\n".join(L))

    print("files=%d  holds=%d  distinct=%d  prop_defs=%d  vacuous=%d  unused_defs=%d  %.1fs"
          % (n_files, len(holds), distinct, n_prop, len(vac), len(unused), time.time() - t0))
    print("by_kind:", dict(by_kind))
    print("top:", dict(by_top.most_common(8)))
    for rel, line, s in unused[:8]:
        print("UNUSED", rel.replace(os.sep, "/"), line, s)


if __name__ == "__main__":
    main()
