"""形状清单审计 v2：Band / RvM 族 + 全库 `def ... : Prop` 的「是否被消费」判决。

判据：把全库 .lean 拼成一个文本流，一次 alternation 正则统计每个 Prop 名字的出现次数。
出现 1 次 = 只有声明行本身 => **孤立形状**（无证明、无消费者）。
出现 >1 = 被某处引用（谓词 / 已被 theorem 用）。

以此把 153 条 `def : Prop` 分成「谓词（有消费者）」与「孤立形状（危险区）」。
"""
import os, re, time
from collections import Counter

ROOT = r"C:\proj2"
SKIP_DIRS = {".lake", ".git", "node_modules", ".idea", "archive"}
SKIP_FILE_PREFIX = ("_probe",)

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|private\s+|protected\s+|nonrec\s+|partial\s+)?"
    r"(def|theorem|lemma|axiom|opaque|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_\u00C0-\uFFFF][A-Za-z0-9_'!?\u00C0-\uFFFF.]*)"
)

files = []
for dp, dns, fns in os.walk(ROOT):
    dns[:] = [d for d in dns if d not in SKIP_DIRS]
    for f in fns:
        if f.endswith(".lean") and not f.startswith(SKIP_FILE_PREFIX):
            files.append(os.path.join(dp, f))

texts = []
rows = []
for path in sorted(files):
    try:
        src = open(path, encoding="utf-8").read()
    except Exception:
        continue
    rel = os.path.relpath(path, ROOT).replace("\\", "/")
    texts.append(src)
    lines = src.splitlines()
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        head = "\n".join(lines[i:i + 9])
        is_prop = bool(re.search(r":\s*Prop", head))
        rows.append(dict(rel=rel, line=i + 1, kind=kind, name=name, prop=is_prop))

print(f"扫描 .lean {len(files)} 个，声明 {len(rows)} 条")

props = [r for r in rows if r["prop"] and r["kind"] in ("def", "abbrev")]
names = sorted({r["name"] for r in props}, key=len, reverse=True)
pat = re.compile(r"(?<![A-Za-z0-9_'!.])(" + "|".join(re.escape(n) for n in names) + r")(?![A-Za-z0-9_'!])")
counts = Counter()
t0 = time.time()
for src in texts:
    for m in pat.finditer(src):
        counts[m.group(1)] += 1
print(f"引用统计 {time.time()-t0:.1f}s")

bands = [r for r in rows if ("Band" in r["name"] or "RvM" in r["name"])]

def status(r):
    if r["kind"] in ("theorem", "lemma"): return "已证"
    if r["kind"] in ("axiom", "opaque"): return "**假设/黑箱**"
    if r["kind"] in ("def", "abbrev") and r["prop"]: return "**未证形状**"
    if r["kind"] in ("def", "abbrev"): return "定义件"
    return r["kind"]

iso = [r for r in props if counts[r["name"]] <= 1]
cons = [r for r in props if counts[r["name"]] > 1]

out = []
out.append("# 形状清单 v2：Band / RvM 族 + 未证形状（带消费判决）")
out.append("")
out.append(f"- 生成 {time.strftime('%Y-%m-%d %H:%M')}　根 `C:\\proj2`（排除 `.lake`、`_probe*`）")
out.append(f"- 声明 **{len(rows)}**；`def : Prop` **{len(props)}**；其中**孤立形状 {len(iso)}**、有消费者 {len(cons)}")
out.append("")
out.append("## 表 A　Band / RvM 族（7 条）")
out.append("")
out.append("| 文件 | 行 | 类别 | 名字 | Prop | 引用 | 状态 |")
out.append("|---|---|---|---|---|---|---|")
for r in sorted(bands, key=lambda x: (x["rel"], x["line"])):
    c = counts.get(r["name"], 1) if r["prop"] else "—"
    out.append(f"| {r['rel']} | {r['line']} | {r['kind']} | `{r['name']}` | {'是' if r['prop'] else '否'} | {c} | {status(r)} |")

out.append("")
out.append(f"## 表 B1　孤立形状（{len(iso)} 条，**无证明、无消费者**）")
out.append("")
out.append("| 文件 | 行 | 名字 |")
out.append("|---|---|---|")
for r in sorted(iso, key=lambda x: (x["rel"], x["line"])):
    out.append(f"| {r['rel']} | {r['line']} | `{r['name']}` |")

out.append("")
out.append(f"## 表 B2　有消费者的 `def : Prop`（{len(cons)} 条，谓词/已被用）")
out.append("")
out.append("| 文件 | 行 | 名字 | 引用数 |")
out.append("|---|---|---|---|")
for r in sorted(cons, key=lambda x: (-counts[x["name"]], x["rel"], x["line"])):
    out.append(f"| {r['rel']} | {r['line']} | `{r['name']}` | {counts[r['name']]} |")

out.append("")
out.append("## 判读")
out.append("")
out.append("- **孤立形状** = 名字在整库只出现一次（即声明行本身）。它既没有证明，也没有任何定理引用它 ⟹ 对证明系统零贡献，只占一个名字。**这才是「未证形状」的危险区。**")
out.append("- 有消费者 = 至少被引用过一次，通常是合法谓词（`IsEllipticMatrix` 这类），是定理陈述的组成部分，不算问题。")
out.append("- 引用计数是静态文本匹配，不含动态解析；同名不同文件会合并计数（粗筛够用，精确需 Lean 侧 `#check`）。")
out.append("- **假设/黑箱**（`axiom` / `opaque`）不在本清单，它们进闭包、是账本条目。")

path = os.path.join(ROOT, "_shape_audit.md")
open(path, "w", encoding="utf-8").write("\n".join(out) + "\n")

print(f"\n写出 {path}")
print(f"\n孤立形状 {len(iso)} 条 —— 按文件：")
byf = Counter(r["rel"] for r in iso)
for f, c in byf.most_common():
    print(f"  {c:3d}  {f}")
print(f"\n有消费者 {len(cons)} 条 —— 引用数 top 12：")
for r in sorted(cons, key=lambda x: -counts[x["name"]])[:12]:
    print(f"  {counts[r['name']]:4d}  {r['name']:34s} {r['rel']}:{r['line']}")

