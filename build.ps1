# 重新编译中文 PDF（需要 Typst 0.15.x）
$ErrorActionPreference = "Stop"
Push-Location (Join-Path $PSScriptRoot "typst_src")
try {
    typst compile main.typ "../rh_lean_blueprint_v2_中文.pdf"
}
finally {
    Pop-Location
}
