#!/bin/bash
# Copyright 2026 The PrimeIR Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

# Run KZG Prime-IR tests using zkir toolchain.
#
# Usage:
#   ./run.sh kzg_evaluate    # Horner + synthetic division
#   ./run.sh kzg_commit      # MSM commitment
#   ./run.sh kzg_prove       # Full KZG prove

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZKIR_DIR="${ZKIR_DIR:-/home/soowon/works/fractalyze/zkir}"
DEFS_DIR="$SCRIPT_DIR/defs"

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <test_name>"
  echo "  test_name: kzg_evaluate | kzg_commit | kzg_prove"
  exit 1
fi

TEST_NAME="$1"
TEST_FILE="$SCRIPT_DIR/${TEST_NAME}.mlir"

if [[ ! -f "$TEST_FILE" ]]; then
  echo "Error: $TEST_FILE not found"
  exit 1
fi

ENTRY_POINT="test_${TEST_NAME}"

echo "=== Running $TEST_NAME (entry: $ENTRY_POINT) ==="

cd "$ZKIR_DIR"

cat "$DEFS_DIR/default_print_utils.mlir" \
    "$DEFS_DIR/bn254_field_defs.mlir" \
    "$DEFS_DIR/bn254_ec_mont_defs.mlir" \
    "$DEFS_DIR/bn254_ec_utils.mlir" \
    "$TEST_FILE" \
  | bazel run //tools:prime-ir-opt -- \
      -elliptic-curve-to-field -field-to-llvm \
  | mlir-runner -e "$ENTRY_POINT" -entry-point-result=void \
      -shared-libs="$(bazel info bazel-bin)/tests/libruntime_functions.so,$(bazel info output_base)/external/llvm-project/llvm/lib/libmlir_runner_utils.so"
