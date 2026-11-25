# -*- coding: utf-8 -*-
"""静态 import 闭包：从 src/Main.lean 出发，数出真正参与 RH 证明的文件与声明规模。不编译。"""
import os, re, time, collections, json

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT  = r"C:\proj2\_rh14_closure.md"

IMP  = re.compile(r"^import\s+([^\s]+)", re.M)
DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:private |protected |noncomputable |nonrec |partial )*"
                  r"(theorem|lemma|def)\s+([^\s:{([]+)", re.M)


def modname(rel):
    return rel[:-5].replace(os.sep, ".")


def main():
    t0 = time.time()
    files, mod2path = [], {}
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, ROOT)
            files.append(p)
            mod2path[modname(rel)] = p

    imports, n_decl, n_holds, text_cache = {}, {}, {}, {}
    for p in files:
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        rel = os.path.relpath(p, ROOT)
        imports[rel] = IMP.findall(t)
        n_decl[rel] = len(DECL.findall(t))
        n_holds[rel] = len([1 for k, nm in DECL.findall(t) if nm.endswith("_holds") or nm.endswith("_hold")])

    # BFS
    seen, queue, external = set(), ["Main"], collections.Counter()
    while queue:
        m = queue.pop()
        if m in seen:
            continue
        seen.add(m)
        p = mod2path.get(m)
        if not p:
            external[m.split(".")[0]] += 1
            continue
        rel = os.path.relpath(p, ROOT)
        for imp in imports.get(rel, []):
            if imp in mod2path:
                queue.append(imp)
            else:
                external[imp.split(".")[0]] += 1

    cl_files = []
    for m in seen:
        p = mod2path.get(m)
        if p:
            cl_files.append(os.path.relpath(p, ROOT))

    tot_files = len(cl_files)
    tot_decl = sum(n_decl.get(f, 0) for f in cl_files)
    tot_holds = sum(n_holds.get(f, 0) for f in cl_files)

    L = ["# RH_14 · `import` 闭包实测（纯静态）\n",
         "根：`%s`\n" % ROOT,
         "起点：`src/Main.lean`（lakefile 的 `Main` roots = `[\"Statements\",\"Main\"]`）\n",
         "## 结果\n",
         "| 项 | 数 |",
         "|---|---|",
         "| 归档内 `.lean` 文件总数 | %d |" % len(files),
         "| **`Main.lean` 可达文件数** | **%d** |" % tot_files,
         "| 不可达（与 RH 证明无关） | %d |" % (len(files) - tot_files),
         "| 闭包内 `theorem/lemma/def` | **%d** |" % tot_decl,
         "| 闭包内 `*_holds` 节点 | **%d** |" % tot_holds,
         "",
         "外部依赖（库外根包）：" + "，".join("`%s` %d" % (k, v) for k, v in external.most_common(8)),
         "",
         "## 说明\n",
         "- 该闭包只按 `import` 传递性计算，不含 `open`/`exact` 层面的引用，属**上界**。",
         "- 若数为小，G1 只需在这个集合上跑 `#print axioms`；若数为大，则须先按 gate 再筛一轮。",
         ""]
    open(OUT, "w", encoding="utf-8").write("\n".join(L))
    print("total_files=%d  reachable=%d  unreachable=%d  closure_decls=%d  closure_holds=%d  %.1fs"
          % (len(files), tot_files, len(files) - tot_files, tot_decl, tot_holds, time.time() - t0))
    print("external:", dict(external.most_common(6)))


if __name__ == "__main__":
    main()
