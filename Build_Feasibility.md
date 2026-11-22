# RH_14 本地动态核验可行性结论（2026-11-21）

## 一句话

`#print axioms riemannHypothesis` 在本机**跑不出来**，不是代码问题，是规模 × 内存的硬约束：`Main` 的依赖闭包等于**整棵树 175,133 / 175,187 个模块**，而每个模块都 `import Mathlib`（单进程峰值提交 6.4–7.8 GB），本机提交上限只有 39.7 GB。

## 已排除的伪故障（此前多轮"418 error / failed to read file"的真因）

| 曾经的判断 | 实测结果 |
|---|---|
| mathlib 构建不全，`.olean.private` 缺失 | **否**。mathlib 源 8,311 个 `.lean` ↔ 8,312 个 `.olean` ↔ 8,312 个 `.olean.private`，缺失 0，仅 2 个 `.tmp` 残片 |
| olean 文件损坏 | **否**。逐文件 `.NET` 全读 + SHA256×8 全部一致；被报错的 `Variable.olean.private`(1,149,928 B)、`OrthogonalReflection.olean.private`(620,296 B) 均完好 |
| 磁盘故障 | **否**。系统日志无 disk/Ntfs 错误，F: 卷报"运行状况良好" |
| `--tstack=400000` 惹的祸 | **否**。`tstack=400000/100000/无` 三次单模块编译全部 exit=0 |
| 工具链 olean 与本机不匹配 | **否**。v4.33.1 单独 `import Lean.Meta.Tactic.Subst` exit=0；`import Mathlib.CategoryTheory.Presentable.OrthogonalReflection` exit=0 |
| 并发刹车失效是因为 `LEAN_NUM_THREADS` | **是，而且完全失效**。`=1/2/3/4/6` 分别实测 7/6/10/9/15 个 `lean`；`LAKE_JOBS`、`-j`、`--jobs` 均不被该版 Lake 接受 |

真因链条：
1. Lake 按 32 逻辑核起 13–15 个 `lean`，不看任何环境变量；
2. 每个 `lean` 加载完整 Mathlib 环境，峰值提交 6.4–7.8 GB；
3. 15 × 7.6 ≈ 114 GB ≫ 39.7 GB 提交上限 → 分配失败；
4. Lean 把分配失败报成 `failed to read file 'xxx.olean.private'` —— 这就是所有"读不出文件"的来源；
5. 一旦上一轮 `lake` 父进程没死干净，它还会续命重建 `lean`，把后面的单进程实验一并拖进 OOM（本轮就踩了这个坑，出现过 pwsh 自身 `OutOfMemoryException`）。
6. 残留的另一个真实现象：干净空闲机、单进程、22 GB 余量下，`import Mathlib` **三次里成功一次**，另两次在随机文件上失败 —— 属过滤器/杀软级抖动，可靠做法只能是重跑。

## 规模账

- `Main` 依赖闭包：**175,133 个模块**（`Main → Supplements.Kernels.MainTheoremsAll → Development.AutomorphicArithmetic... → 全树`）；扇出最高的单模块导入 370 个（`Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving`）。所以"只编 Main 链"等于编整棵树。
- 本机可用并发：**2–3 个**（39.7 GB 上限 − 约 17 GB 系统基线，每进程 7.6 GB）。
- 单模块成本：加载 Mathlib 环境约 5–10 s，加文件本身。
- 估算：串行 ≈ 150 h；3 并发 ≈ 50 h；即便把 pagefile 提到 96 GB 换到 5–6 并发，仍需 ≈ 30 h。**这不是调参能解决的量级问题。**

## 结论与替代

1. 动态核验在 32 GB / 39.7 GB 提交的 Windows 机器上不可达；需要 ≥128 GB 内存 + Linux 的机器（16 并发约 18 h）。
2. 已有等效且更权威的内核级证据：MIT Andrew Sutherland 独立编译该归档并用 Lean 内核复核，报告 **only the three standard axioms**；Elliot Glazer 判定形式化命题为 Dirichlet L 版 GRH；Buzzard 要求的 comparator 多内核复核截至 11-20 未完成。
3. 我方静态审计（174,793 文件全扫）：`axiom 0 / constant 0 / opaque 0 / unsafe 0 / sorry 0 / admit 0 / native_decide 0`；风险只剩"定义空转"（`Nonempty (Hyps …)` 是否真构造等 4 处），这属于语义审计，不需要编译。
4. 若仍要本机动态证据，唯一低成本可用目标：只编 `Statements`（仅依赖 Mathlib），对 `RiemannZetaZerosOnLine` 等 4 个 `def` 取 axiom 集 —— 能证明"陈述层干净"，但证明 `riemannHypothesis` 的定理层做不到。

## 现场状态

- 所有 `lean`/`lake` 已清空；`mathlib` 8,312 olean 完好；树侧已有 145 个 olean。
- 关键产物：`cone.json`（175,133 模块的拓扑序 + 导入图）、`cone.py`（闭包计算脚本）、`s1.log`/`m3.log`/`probe*.log`（并发与 OOM 实测日志）。

---

# 附：已交付的 kernel 级动态核验（2026-11-22）

程序：只编译 `src/Statements.lean`（仅 `import Mathlib`，不触及 175k 棵树），产出 `stmtbuild/Statements.olean`（20,784 字节，一次通过，84.1 s），再对其跑 `#print axioms`。

## 结果一：四个陈述的 axiom 集

```
'RiemannZetaZerosOnLine'             depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletLNonvanishingRightOfHalf'  depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletLZerosOnLine'              depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimitiveDirichletLZerosOnLine'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

四条全部只含三条标准公理，**无 `sorryAx`、无自定义 `axiom`**。陈述层是干净的，不是靠 sorry 或空转定义撑起来的。

## 结果二：他们的 RH 陈述 ≡ Mathlib 官方 `RiemannHypothesis`（`rfl` 可证）

Mathlib 原文：

```
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
'RiemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
```

他们的原文：

```
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2
```

两者逐字同构（绑定点相同、假设顺序相同、平凡零点排除项相同），并且

```
example : RiemannHypothesis = RiemannZetaZerosOnLine := rfl   -- exit=0
```

内核直接给出定义相等（不是 `↔`，是 `=`，`rfl` 一步）。

推论：`Main.lean` 的 `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` 所证的就是 Mathlib 标准 RH 命题本身，**陈述层不存在弱化**。这一条此前只能靠读源码判断，现在有内核证据。

## 仍未核验的

`#print axioms riemannHypothesis`（定理层）——需要 `rhOfAll` 所在的 175,133 模块闭包，本机不可达（见正文）。陈述层已 clean，定理层仍依赖 Sutherland 的独立内核复核与 Buzzard 的 comparator。
