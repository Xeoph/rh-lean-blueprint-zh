#!/usr/bin/env bash
# 重新编译中文 PDF（需要 Typst 0.15.x）
set -euo pipefail
cd "$(dirname "$0")/typst_src"
typst compile main.typ "../rh_lean_blueprint_v2_中文.pdf"
