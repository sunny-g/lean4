#!/usr/bin/env bash
source ../common.sh

echo "running LLVM program..."
rm "./$f.out" || true
compile_lean_llvm_backend
exec_check "./$f.out"
diff_produced
