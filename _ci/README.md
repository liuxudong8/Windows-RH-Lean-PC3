# CI 改造草案 v1（不生效、未推送）

**位置说明**：本目录 `_ci/` **不是** `.github/workflows/`，GitHub 不会读取、不会触发，纯草案。
确认后再手工搬到对应位置。

**日期**：2026-11-25
**依据**：对 `run 45520925414`（sha 22533a7）的实测拆解。

---

## 一、现状：绿了，但绿的是别的项目

`run 45520925414` 结论 `success`，7.1 分钟。逐步耗时：

| 步 | 结论 | 时长 |
|---|---|---|
| Checkout source | success | 7 s |
| Cache .lake | success | 5 s |
| Fetch dependencies (`lake update`) | success | 60 s |
| Get mathlib cache (`lake exe cache get \|\| true`) | success | **5 s** |
| **Build project (`lake build`)** | success | **343 s** |

它编的是什么，由下列链条唯一确定：

1. `build.yml` 末步是裸 `lake build` ⟹ 走 `lakefile.toml` 的 `defaultTargets = ["orderpreservingbijection"]`
2. 该目标 `[[lean_exe]] root = "Main"`，`Main.lean` 全文 123 字节，只有 `import OrderPreservingBijection`
3. 顶层聚合 `OrderPreservingBijection.lean` 只 import **5 个**模块：
   `Basic`、`HyperbolicIdentity`、`QuadraticFieldFive`、`stage_3`、`stage_4`
4. ⟹ 343 秒编的是这 5 个模块的闭包
5. **QRH 从未进入构建**：`lakefile.toml` 里根本没有 `[[lean_lib]] name = "QRH"`

**结论：绿灯的语义是「11-23 那版 OrderPreservingBijection 的 5 个旧模块能编译」。
它与 `sincKer`、`C_FLAT = 4/3`、1941 行的 `S7_1_Main.lean`、十四刀成果——零关系。**

为什么它一直绿、而且很快：

- 仓库确实提交了 9,152 个 mathlib 源文件，`path = "./mathlib4-master"` 在 CI 上成立
- `actions/cache` 的 key 是 `hashFiles('lakefile.toml','lean-toolchain')`，这两个文件自 11-23 起未变 ⟹ **key 恒定命中**，mathlib 的 oleans 永远从缓存恢复
- 于是 `lake exe cache get` 只需 5 s，`|| true` 也从不触发降级

九次历史 run 全 `success`，说明这个"恒绿"已经持续了一段时间。

---

## 二、目标

让 CI 的绿灯**具备真实语义**：`QRH` 编不过就红。

---

## 三、三处改动 + 一处配套

### 改动 1 · QRH 目录布局（草案：`migrate_qrh_layout.ps1`）

现状有两层问题：

- 仓库 `QRH/` **根下**已有 7 个 `.lean`（库根模块 `QRH.lean` 在仓库根，不在 `QRH/` 内），但内容**新旧混杂**
- 新版躺在 `QRH/2026-11-25/` 里，目录名 `2026-11-25` **不是合法 Lean 标识符**（数字开头 + 连字符），模块名会解析成 `QRH.2026-11-25.S7_1_Main` ⟹ 永远不可 import

实测差距（DryRun 已跑，`C:\proj2\QRH` vs 仓库 `QRH/`）：

| 文件 | 仓库现状 | 源 |
|---|---|---|
| `Dbg_Khat.lean` | 629 行 | 629 行（同） |
| `Probe_f0.lean` | 26 | 26（同） |
| `Probe_norm.lean` | 25 | 25（同） |
| `S7_1_Core.lean` | 1215 | 1215（同） |
| **`S7_1_Main.lean`** | **1423** | **1941**（差 518 行） |
| `S7_1_Stage3.lean` | 2143 | 2144（差 1 行） |
| `Test_import.lean` | 37 | 37（同） |

⟹ **真正落后的只有 2 个文件**。迁移的实际风险远低于"整套搬迁"的直觉。

处置（`migrate_qrh_layout.ps1`，默认只打印计划，加 `-Execute` 才动手）：

1. 用 `C:\proj2\QRH\*.lean` 覆盖仓库 `QRH\*.lean`（8 个文件，1941 行版）
2. 把 `QRH\` 下 13 个子目录全部移到 `archive\snapshots\qrh\<名>\`
   （`2026-10-27`、`2026-10-29`、`2026-10-30`、`2026-11-01`、`2026-11-02`、
   `2026-11-04`、`2026-11-22`、`2026-11-23`、`2026-11-25`、`latest`、
   `document`、`Lean过程`、`_s77_tmp`）
3. `QRH\` 根下只留 8 个 `.lean`，无子目录

**备选（更保守，不动目录）**：不搬目录，改在 `lakefile.toml` 里用显式 `globs`
把 QRH 锁在 8 个顶层模块上。草案 `lakefile.toml` 里两段都给了，注释标明。

### 改动 2 · lakefile（草案：`lakefile.toml`）

镜像现有 `lakefile.toml` 只声明 `OrderPreservingBijection`、`BSD` 两个 lib。
`C:\proj2\lakefile.toml` 已经声明了 `QRH` 与 `A5CharQ5`，且本地 `lake build QRH`
是 4025 jobs 成功过的——所以草案直接**照抄已验证的本地配置**，只多两处：

- `defaultTargets` 保持 `["orderpreservingbijection"]`（不把 QRH 塞进默认，避免无谓耗时）
- `QRH` 项按方案选择附 `globs`

### 改动 3 · workflow（草案：`build_v1.yml`）

四处：

| 改 | 原 | 新 |
|---|---|---|
| ① 手动触发 | 无 | 加 `workflow_dispatch` |
| ② cache key | `lakefile.toml`, `lean-toolchain` | 补 `lake-manifest.json` |
| ③ cache 失败不静默 | `lake exe cache get \|\| true` | 去掉 `\|\| true` |
| ④ 构建目标 | 裸 `lake build` | 分两步：`lake build OrderPreservingBijection BSD` → `lake build QRH` |

分两步的意义：core 先给快反馈，QRH 失败时能一眼看出是哪一层。

### 配套 · push 脚本第 1 步（**必须一起改**，否则改动 1 会被下次推送覆盖回去）

`push_new.ps1` 现在把 `C:\proj2\QRH\*` 复制到 `QRH\<today>\`。改动 1 之后，
源码应直接落 `QRH\` 顶层，日期快照进 `archive\snapshots\qrh\<today>\`：

```powershell
# 旧
$qrhDst = Join-Path $repo "QRH\$today"
Copy-Item -Path "C:\proj2\QRH\*" -Destination $qrhDst -Recurse -Force

# 新
Copy-Item -Path "C:\proj2\QRH\*.lean" -Destination (Join-Path $repo "QRH") -Force
$snap = Join-Path $repo "archive\snapshots\qrh\$today"
New-Item -ItemType Directory -Force -Path $snap | Out-Null
Copy-Item -Path "C:\proj2\QRH\*" -Destination $snap -Recurse -Force
```

---

## 四、切换步骤（建议顺序）

| # | 动作 | 可回退 |
|---|---|---|
| 1 | `.\_ci\migrate_qrh_layout.ps1`（先不加 `-Execute`，看计划） | — |
| 2 | `.\_ci\migrate_qrh_layout.ps1 -Execute` | `git checkout -- . ; git clean -fd` |
| 3 | 用 `_ci\lakefile.toml` 覆盖仓库根 `lakefile.toml` | git |
| 4 | 用 `_ci\build_v1.yml` 覆盖 `.github\workflows\build.yml` | git |
| 5 | 改 `push_new.ps1` 第 1 步（见上） | git |
| 6 | `git add . && git commit && git push` → 观察 Actions | `git revert` |

**建议 2–5 全做完再一次性推**，避免中间态（QRH 有新源码但 lakefile 没声明）成红。

---

## 五、风险清单

1. **`QRH` 里 3 个探针文件是否编得过，未在 CI 验证过**
   `QRH\Dbg_Khat.lean`（32 KB）、`Test_import.lean`、`Probe_f0/norm.lean` 会随 lib 一起编。
   本地 `lake build QRH` 是成功的（4025 jobs），理论上应通过，但 CI 环境未实测。
   **若红了，第一步是看是不是它们**；必要时把它们移出 `QRH\`（放到 `_probe\`）。

2. **镜像 `OrderPreservingBijection` 有 199 个 `.lean`，本地只有 149 个**
   多出 50 个是历史遗留（robocopy 不删）。QRH 只依赖其中 `LSeriesConj`、
   `Exceptional\ExceptionalZeroInterface`，两者 MD5 已核对一致。风险低但不为零。

3. **首次 QRH 构建可能显著耗时**
   mathlib oleans 由 cache 覆盖，QRH 自身文件（`S7_1_Main` 123 KB、
   `S7_1_Stage3` 118 KB、`S7_1_Core` 62 KB）编译量不小，首次可能 10–25 分钟。
   `build_v1.yml` 已设 `timeout-minutes: 60`。

4. **目录搬迁会让本次 commit 的 diff 变大**：**968 个文件**从 `QRH/` 移入
   `archive/snapshots/qrh/`（逐目录实测：68 / 67 / 17 / 110×7 / 20 / 1 / 25）。
   git 能识别为 rename，历史不会膨胀，但首次 clone 体积略增。

5. **`mathlib` 仍是 `path` 依赖**，依赖"仓库里那 9,152 个 mathlib 源文件一直在"。
   这不是好设计，但改动它（换 git 依赖 + 找 v4.34.0-rc2 对应的上游 commit）
   属于档 3，工作量 1–2 天，且本地 mathlib 是 `init` 快照（非上游 rev），
   风险高于本次改动。**本草案不动它。**

---

## 六、本草案没做的事

- 没改 `.github/workflows/build.yml`（原文件保持 11-23 的样子）
- 没改 `lakefile.toml`（仓库根仍是旧的 4 行 lib 声明）
- 没动仓库里任何源码与快照
- 没 commit、没 push

GitHub 上仍是 `22533a7`，CI 语义仍是"只验证 5 个旧模块"。
