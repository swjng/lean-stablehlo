<!-- Copyright 2026 The PrimeIR Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. -->

# lean-prime-ir

Lean 4 → Prime-IR pipeline PoC for KZG commitment scheme.

## Structure

- **`mlir/`** — Hand-written Prime-IR tests validating KZG over BN254
- **`lean/`** — Lean 4 project for 𝔽ₚ/KZG math structure definitions

## M0: Prime-IR KZG Tests

Test vector: p(x) = 1 + 2x + 3x² + 4x³, SRS = [G, 2G, 3G, 4G]

| Test | Description | Expected |
|------|-------------|----------|
| `kzg_evaluate` | Horner evaluation + synthetic division | p(5) = 586, q = [117, 23, 4] |
| `kzg_commit` | MSM commitment (3-way comparison) | C = 30 · G |
| `kzg_prove` | Full KZG prove pipeline | C = 30 · G, π = 175 · G |

### Running

Requires `zkir` build with `prime-ir-opt`:

```bash
cd mlir
./run.sh kzg_evaluate
./run.sh kzg_commit
./run.sh kzg_prove
```

## M1: Lean 4 Project

Skeleton only. Implementation follows M0 validation.
