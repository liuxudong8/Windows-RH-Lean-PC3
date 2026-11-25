<#
Windows-RH-Lean-PC3 push script —— v2 草案 (2026-11-25)
================================================================
与 push.ps1 的差异（只列改动，其余逻辑完全沿用）：

  [新增 1c] OrderPreservingBijection\ → 仓库根（robocopy /E 增量）
            原脚本只复制 QRH\* 与 A5CharQ5\*，OrderPreservingBijection 靠历史遗留躺在
            仓库里，本地对 Chi5Real.lean / Exceptional\Statement.lean 的改动永远推不上去。

  [新增 1d] QRH\latest\ —— 除日期的快照外，再维护一份"当前版本"覆写目录。
            原脚本每次建 QRH\<today>\，某天不跑，GitHub 上那天就是空白（11-24/11-25 即空白）。

  [改写 2]  根产出从"19 个硬编码调试文件名"改为「明确清单 + 通配」：
            QRH_summary.md / QRH_summary_en.md / _grh_iface\ / _partner\ /
            _probe_*.lean|.txt / _pd_*.py|.txt / _wz_*.py|.txt / _rh14_*.* /
            _shape_audit.* / _md2docx_page.py / _audit_check.py
            原清单里全是 11-23 之前的 Dbg_Probe / build_*.txt，文档与探针一个都进不去。

  [新增 0]  预检：打印 S7_1_Main.lean 的行数与关键符号计数（sincKer / C_FLAT / triKer /
            physDeltaRvM / landau axiom），推送前人工一眼确认推的不是旧版。

  [新增]    -DryRun 开关：照常同步工作区，但在 git add 之前停下，只打印待提交清单摘要。
            用于先看"会推什么"，不做 commit / 不 push。

【保守约定】
  - 所有 robocopy 均用 /E（增量覆盖），**不用 /MIR**：仓库里已有、本地没有的历史文件不会被删。
  - 远端守卫沿用原脚本：origin 必须等于 PC3，否则中止（防误写 PC2）。
  - 不改动 push.ps1；本脚本独立存在，确认后再决定是否替换。

用法：
  & .\push_new.ps1              # 同步 + 提交 + 推送
  & .\push_new.ps1 -DryRun      # 同步 + 列出待提交清单，不提交不推送
#>

param([switch]$DryRun)

$repo = Split-Path -Parent $MyInvocation.MyCommand.Path
$today = Get-Date -Format "yyyy-MM-dd"

# git 可执行文件定位（本机 PATH 里通常没有 git）
$gitExe = "C:\Program Files\Git\cmd\git.exe"
if (-not (Test-Path -LiteralPath $gitExe)) {
    $cmd = Get-Command git -ErrorAction SilentlyContinue
    if ($cmd) { $gitExe = $cmd.Source }
    else { Write-Host "git not found, abort." -ForegroundColor Red; exit 1 }
}

# 远端守卫：只允许推 PC3，防止误写历史仓库 PC2
$expectedRemote = "git@github.com:liuxudong8/Windows-RH-Lean-PC3.git"
$originUrl = & $gitExe -C $repo remote get-url origin 2>$null
if ($originUrl -ne $expectedRemote) {
    Write-Host "origin = '$originUrl', 应为 '$expectedRemote'，已中止。" -ForegroundColor Red
    exit 1
}

Write-Host "===== 0/5 Preflight: 源文件关键符号 =====" -ForegroundColor Cyan
$main = "C:\proj2\QRH\S7_1_Main.lean"
 if (Test-Path -LiteralPath $main) {
    $lines = (Get-Content -LiteralPath $main).Count
    $sinc  = (Select-String -Path $main -Pattern "sincKer"     -AllMatches | Measure-Object).Count
    $flat  = (Select-String -Path $main -Pattern "C_FLAT"      -AllMatches | Measure-Object).Count
    $tri   = (Select-String -Path $main -Pattern "triKer"      -AllMatches | Measure-Object).Count
    $rvm   = (Select-String -Path $main -Pattern "physDeltaRvM" -AllMatches | Measure-Object).Count
    $land  = (Select-String -Path $main -Pattern "^\s*axiom\s+landau_explicit_L\s*:" -AllMatches | Measure-Object).Count
    Write-Host ("  S7_1_Main.lean  {0} 行 | sincKer={1} C_FLAT={2} triKer={3} physDeltaRvM={4} landau_axiom={5}" -f $lines,$sinc,$flat,$tri,$rvm,$land)
    if ($flat -eq 0 -and $tri -gt 0) {
        Write-Host "  ⚠ 源仍是 triKer/C_MT 旧口径，请确认 C:\proj2 指向正确工程。" -ForegroundColor Yellow
    }
} else {
    Write-Host "  ✗ 找不到 $main，已中止。" -ForegroundColor Red
    exit 1
}

Write-Host "`n===== 1/5 Sync external artifacts into repo =====" -ForegroundColor Cyan

# 1) QRH Lean 项目源 → 仓库 QRH\<today> 快照（同日更新；历史快照保留不覆盖）
$qrhLibFiles = @("S7_1_Core.lean","S7_1_Main.lean","S7_1_Stage3.lean")
foreach ($f in $qrhLibFiles) {
    $s = Join-Path "C:\proj2\QRH" $f
    if (Test-Path -LiteralPath $s) {
        Copy-Item -LiteralPath $s -Destination (Join-Path $repo "QRH") -Force
    } else {
        Write-Host "  ⚠ 缺 $f（跳过）" -ForegroundColor Yellow
    }
}
# 全量快照（含探针 / 文档）→ archive\snapshots\qrh\<today>
$qrhSnap = Join-Path $repo "archive\snapshots\qrh\$today"
New-Item -ItemType Directory -Force -Path $qrhSnap | Out-Null
Copy-Item -Path "C:\proj2\QRH\*" -Destination $qrhSnap -Recurse -Force

# 1d) 「当前版本」入口已取消：顶层 QRH/ 本身就是当前版本（可编译的 3 个库模块）

# 1b) A5CharQ5 Lean 项目源 → 仓库 A5CharQ5\<today> 快照
$a5Dst = Join-Path $repo "A5CharQ5\$today"
New-Item -ItemType Directory -Force -Path $a5Dst | Out-Null
Copy-Item -Path "C:\proj2\A5CharQ5\*" -Destination $a5Dst -Recurse -Force
if (Test-Path -LiteralPath "C:\proj2\A5CharQ5.lean") { Copy-Item -LiteralPath "C:\proj2\A5CharQ5.lean" -Destination $a5Dst -Force }

# 1c) OrderPreservingBijection\ → 仓库根（增量覆盖，不删历史）
$opbSrc = "C:\proj2\OrderPreservingBijection"
if (Test-Path -LiteralPath $opbSrc) {
    & "$env:SystemRoot\System32\robocopy.exe" $opbSrc (Join-Path $repo "OrderPreservingBijection") /E /NFL /NDL /NJH /NJS /NP | Out-Null
    if ($LASTEXITCODE -ge 8) { Write-Host "robocopy OrderPreservingBijection FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }
    if (Test-Path -LiteralPath "C:\proj2\OrderPreservingBijection.lean") {
        Copy-Item -LiteralPath "C:\proj2\OrderPreservingBijection.lean" -Destination $repo -Force
    }
    Write-Host ("  OrderPreservingBijection: 本地 {0} 个 .lean → 仓库" -f (Get-ChildItem $opbSrc -Filter *.lean -Recurse).Count)
} else {
    Write-Host "  ⚠ 源目录 OrderPreservingBijection 不存在，跳过" -ForegroundColor Yellow
}

# 2) C:\proj2 根产出（探针 / 数值脚本 / 审计件）→ 仓库根
#    注意：QRH_summary.md / QRH_summary_en.md 位于 C:\proj2\QRH\ 下，已随步骤 1 进入
#    QRH\<today>\ 与 QRH\latest\，此处不再单独复制。
$proj2Files = @(
  "QRH.lean",
  "_md2docx_page.py","_audit_check.py"
)
foreach ($f in $proj2Files) {
    $s = Join-Path "C:\proj2" $f
    if (Test-Path -LiteralPath $s) { Copy-Item -LiteralPath $s -Destination $repo -Force }
    else { Write-Host "  ⚠ 缺文件 $f（跳过）" -ForegroundColor Yellow }
}

$proj2Patterns = @(
  "_probe_*.lean","_probe_*.txt",
  "_pd_*.py","_pd_*.txt",
  "_wz_*.py","_wz_*.txt",
  "_rh14_*.py","_rh14_*.md",
  "_shape_audit.*"
)
foreach ($p in $proj2Patterns) {
    Get-ChildItem -Path (Join-Path "C:\proj2" $p) -ErrorAction SilentlyContinue |
      ForEach-Object { Copy-Item -LiteralPath $_.FullName -Destination $repo -Force }
}

# 2b) 审计目录与合伙人文书目录（目录增量，不删历史）
foreach ($d in @("_grh_iface","_partner")) {
    $src = Join-Path "C:\proj2" $d
    if (Test-Path -LiteralPath $src) {
        & "$env:SystemRoot\System32\robocopy.exe" $src (Join-Path $repo $d) /E /NFL /NDL /NJH /NJS /NP | Out-Null
        if ($LASTEXITCODE -ge 8) { Write-Host "robocopy $d FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }
    } else {
        Write-Host "  ⚠ 目录 $d 不存在，跳过" -ForegroundColor Yellow
    }
}

# 3) d1 文档最新全目录 → 仓库 document\（robocopy /E 增量，退出码 0-7 为成功）
& "$env:SystemRoot\System32\robocopy.exe" "C:\Users\shtcl\Doubao\chats\2026-10-16\document" (Join-Path $repo "document") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy document FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

# 4) 数值件全目录 → 仓库 new-chat\
& "$env:SystemRoot\System32\robocopy.exe" "C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat" (Join-Path $repo "new-chat") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy new-chat FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

# 5) C:\proj2\archive 过程快照 → 仓库 archive\
& "$env:SystemRoot\System32\robocopy.exe" "C:\proj2\archive" (Join-Path $repo "archive") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy archive FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

Write-Host "`n===== 2/5 Check local changes =====" -ForegroundColor Cyan
$changes = & $gitExe -C $repo status --porcelain
if ([string]::IsNullOrWhiteSpace($changes)) {
    Write-Host "No changes detected, exit." -ForegroundColor Yellow
    exit
}

$changeLines = @($changes -split "`n" | Where-Object { $_ -ne "" })
Write-Host ("  变更条目 {0} 个" -f $changeLines.Count)
$adds = @($changeLines | Where-Object { $_ -match '^\?\?' }).Count
$mods = @($changeLines | Where-Object { $_ -match '^ ?M' }).Count
$dels = @($changeLines | Where-Object { $_ -match '^ ?D' }).Count
Write-Host ("  新增 {0} / 修改 {1} / 删除 {2}" -f $adds,$mods,$dels)

Write-Host "  前 40 条："
$changeLines | Select-Object -First 40 | ForEach-Object { Write-Host ("    " + $_) }

if ($DryRun) {
    Write-Host "`n[DRY-RUN] 到此为止：工作区已同步，未执行 git add / commit / push。" -ForegroundColor Yellow
    Write-Host "如需回退本次同步，用： git -C `"$repo`" checkout -- . ; git -C `"$repo`" clean -fd" -ForegroundColor Yellow
    exit
}

$commitMsg = $env:PUSH_MSG
if ([string]::IsNullOrWhiteSpace($commitMsg)) {
    $commitMsg = "sync: lean source & docs & numerics $today"
}

Write-Host "`n=== 3/5 git add all ===" -ForegroundColor Cyan
& $gitExe -C $repo add .

Write-Host "`n=== 4/5 git commit ===" -ForegroundColor Cyan
& $gitExe -C $repo commit -m "$commitMsg"

Write-Host "`n=== 5/5 git push origin main ===" -ForegroundColor Cyan
& $gitExe -C $repo push origin main

Write-Host "`n✅ Push completed!" -ForegroundColor Green
$lastHash = & $gitExe -C $repo rev-parse --short HEAD
Write-Host "Commit hash: $lastHash"
Write-Host "Actions URL: https://github.com/liuxudong8/Windows-RH-Lean-PC3/actions`n"
