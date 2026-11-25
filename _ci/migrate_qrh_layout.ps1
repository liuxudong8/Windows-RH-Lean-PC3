# ============================================================
# _ci/migrate_qrh_layout.ps1 —— QRH 目录迁移草案（2026-11-25）
#
# 目的：让 QRH 成为一个「可被 lake 声明的库」：
#   - QRH/ 根下放最新源码（7 个 .lean，来自 C:\proj2\QRH；
#     库根模块 QRH.lean 在仓库根，不动）
#   - QRH/ 下不再有子目录（日期快照名含数字/连字符，不是合法 Lean 标识符）
#
# 用法：
#   .\_ci\migrate_qrh_layout.ps1            # 只打印计划，不动任何文件
#   .\_ci\migrate_qrh_layout.ps1 -Execute   # 真正执行
#
# 回退：
#   git -C <repo> checkout -- . ; git -C <repo> clean -fd
# ============================================================

param([switch]$Execute)

$ErrorActionPreference = "Stop"

$repo     = Split-Path -Parent $PSScriptRoot          # 仓库根
$srcProj  = "C:\proj2\QRH"                           # 本地源码
$qrhDir   = Join-Path $repo "QRH"
$snapRoot = Join-Path $repo "archive\snapshots\qrh"

# 需要迁出的子目录（日期快照 + 文档 + 临时）
$dirs = @(
  "2026-10-27","2026-10-29","2026-10-30",
  "2026-11-01","2026-11-02","2026-11-04",
  "2026-11-22","2026-11-23","2026-11-25",
  "latest","document","Lean过程","_s77_tmp"
)

Write-Host "==== 迁移计划 ====" -ForegroundColor Cyan
Write-Host "  仓库根      : $repo"
Write-Host "  源码来源    : $srcProj"
Write-Host "  快照去向    : $snapRoot"
Write-Host ""

Write-Host "  [1] 覆盖 QRH 根下 .lean" -ForegroundColor Yellow
Get-ChildItem -Path "$srcProj\*.lean" -File | ForEach-Object {
  $dst = Join-Path $qrhDir $_.Name
  $old = if (Test-Path -LiteralPath $dst) { "{0} 行" -f (Get-Content -LiteralPath $dst).Count } else { "缺" }
  Write-Host ("      {0,-20} 目标现状 {1,-8} ← 源 {2} 行" -f $_.Name, $old, (Get-Content -LiteralPath $_.FullName).Count)
}

Write-Host ""
Write-Host "  [2] 迁出子目录" -ForegroundColor Yellow
foreach ($d in $dirs) {
  $p = Join-Path $qrhDir $d
  if (Test-Path -LiteralPath $p) {
    $n = (Get-ChildItem -LiteralPath $p -Recurse -File | Measure-Object).Count
    Write-Host ("      {0,-14} {1,6} 个文件 → archive\snapshots\qrh\{0}\" -f $d, $n)
  } else {
    Write-Host ("      {0,-14} （不存在，跳过）" -f $d) -ForegroundColor DarkGray
  }
}

if (-not $Execute) {
  Write-Host ""
  Write-Host "  [DRY-RUN] 未执行。确认后加 -Execute 再跑。" -ForegroundColor Yellow
  exit
}

Write-Host ""
Write-Host "==== 执行 ====" -ForegroundColor Cyan

# 1) 覆盖 .lean
Write-Host "  [1] Copy-Item 覆盖 .lean ..." -ForegroundColor Green
Copy-Item -Path "$srcProj\*.lean" -Destination $qrhDir -Force

# 2) 迁出子目录
Write-Host "  [2] Move-Item 迁出子目录 ..." -ForegroundColor Green
New-Item -ItemType Directory -Force -Path $snapRoot | Out-Null
foreach ($d in $dirs) {
  $p = Join-Path $qrhDir $d
  if (Test-Path -LiteralPath $p) {
    $target = Join-Path $snapRoot $d
    if (Test-Path -LiteralPath $target) {
      Write-Host ("      {0} 目标已存在，改用合并覆盖" -f $d) -ForegroundColor Yellow
      & "$env:SystemRoot\System32\robocopy.exe" $p $target /E /NFL /NDL /NJH /NJS /NP | Out-Null
      Remove-Item -LiteralPath $p -Recurse -Force
    } else {
      Move-Item -LiteralPath $p -Destination $target
      Write-Host ("      {0} → archive\snapshots\qrh\{0}" -f $d)
    }
  }
}

# 3) 校验
Write-Host ""
Write-Host "==== 校验 ====" -ForegroundColor Cyan
$lean = Get-ChildItem -Path $qrhDir -Filter *.lean -File
Write-Host ("  QRH 根下 .lean 数 = {0}" -f $lean.Count)
$lean | ForEach-Object { Write-Host ("    {0,-20} {1,6} 行" -f $_.Name, (Get-Content -LiteralPath $_.FullName).Count) }
$sub = Get-ChildItem -Path $qrhDir -Directory
Write-Host ("  QRH 根下子目录数 = {0}（应为 0）" -f $sub.Count)
if ($sub.Count -gt 0) { $sub | ForEach-Object { Write-Host ("    ✗ 残留: " + $_.Name) -ForegroundColor Red } }

$main = Join-Path $qrhDir "S7_1_Main.lean"
if (Test-Path -LiteralPath $main) {
  $c = (Select-String -Path $main -Pattern "C_FLAT" -AllMatches | Measure-Object).Count
  Write-Host ("  S7_1_Main.lean 里 C_FLAT 命中 = {0}（应 > 0，确认是 1941 行新版）" -f $c)
}
Write-Host ""
Write-Host "下一步：用 _ci\lakefile.toml 覆盖仓库根 lakefile.toml，再覆盖 .github\workflows\build.yml" -ForegroundColor Yellow
