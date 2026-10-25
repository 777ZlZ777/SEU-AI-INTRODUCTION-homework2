#!/usr/bin/env bash
# 一键复现验证：Lean 4.35.0 + mathlib v4.35.0
#
# 用法：
#   ./verify.sh                          # 需要 mathlib v4.35.0 源码在 ../../_toolchain/mathlib4
#   MATHLIB=/path/to/mathlib ./verify.sh # 或显式指定 mathlib 工程目录
#
# 脚本做的事：把 Euclid.lean 拷进 mathlib 工程根 → 登记 lake 目标（幂等）→
#             lake build Euclid → 用临时 Check.lean 做 #check 与 #print axioms。
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN_BIN="${LEAN_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin}"
MATHLIB="${MATHLIB:-$HERE/../../_toolchain/mathlib4}"

if [ ! -d "$MATHLIB" ]; then
  echo "找不到 mathlib 工程：$MATHLIB"
  echo "请准备一份 mathlib v4.35.0 源码（lake update 后可用），并用 MATHLIB=... 指定其路径，例如："
  echo "    MATHLIB=~/mathlib4 ./verify.sh"
  exit 1
fi

export PATH="$LEAN_BIN:$PATH"

cp "$HERE/Euclid.lean" "$MATHLIB/Euclid.lean"

# 首次运行时把模块登记为 lake 目标（幂等：已存在则跳过）
if ! grep -q 'lean_lib Euclid where' "$MATHLIB/lakefile.lean"; then
  printf '\nlean_lib Euclid where\n  roots := #[`Euclid]\n' >> "$MATHLIB/lakefile.lean"
fi

cd "$MATHLIB"
echo "== lake build Euclid =="
lake build Euclid

echo "== #check / #print axioms =="
cat > Check.lean <<'EOF'
import Euclid

#check Euclid.exists_prime_gt
#check Euclid.exists_prime_gt_pos
#check Euclid.exists_prime_gt_of_mathlib
#print axioms Euclid.exists_prime_gt
EOF
lake env lean Check.lean

echo
echo "OK: 编译通过，无 sorry，公理仅为 propext / Classical.choice / Quot.sound"
