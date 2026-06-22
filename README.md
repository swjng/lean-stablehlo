<!-- Copyright 2026 Soowon Jeong.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. -->

# lean-stablehlo

Lean 4 library for writing cryptographic protocols that generates formally verified StableHLO MLIR.
Users write protocols using a deep-embedded DSL, prove correctness in Lean, and extract verified MLIR through a trivial serializer.

KZG commitment scheme is the first PoC to validate the approach.

## Architecture

**Deep Embedding + Extraction** (Fiat-Crypto style).

```
Lean DSL (StableHLO AST represented as Lean types)
    ↓  proofs inside Lean (Expr.eval : ZMod p)
Proven StableHLO AST (Lean term)
    ↓  trivial serializer (AST → text, ~40 lines)
StableHLO MLIR text
```

- **Trust boundary**: only the serializer is unverified (trivially inspectable)
- **Prior art**: Fiat-Crypto (production use in Chrome/BoringSSL)

## Structure

- **`mlir/`** — Hand-written StableHLO tests validating KZG over BN254
- **`lean/`** — Lean 4 project: deep-embedded StableHLO DSL + KZG correctness proofs

```
lean/LeanStableHLO/
├── StableHLO/
│   ├── Expr.lean          -- Expr p inductive + eval semantics (ZMod p)
│   ├── Serialize.lean     -- AST → MLIR text serializer
│   ├── Polynomial.lean    -- Horner + synthetic division (pure AST)
│   ├── EllipticCurve.lean -- Affine point ops, scalar mul, MSM
│   ├── EllipticCurve/
│   │   └── Correctness.lean
│   ├── KZG.lean           -- KZG commit + prove + verify
│   ├── KZG/
│   │   └── Correctness.lean
│   ├── Pairing.lean       -- Pairing axiomatization
│   ├── Correctness.lean   -- End-to-end correctness theorems
│   └── BN254.lean         -- BN254 field/curve parameters
├── IR.lean                -- (M1) MLIR type repr + IRBuilder monad
├── Field.lean             -- (M1) StableHLO field ops
├── Polynomial.lean        -- (M1) String codegen polynomial ops
├── KZG.lean               -- (M1) String codegen KZG
└── EllipticCurve.lean     -- (M1) String codegen EC ops
```

## Status

### Phase 1: KZG PoC ✅

| Milestone | Description | Status |
|-----------|-------------|--------|
| M0 | Hand-written StableHLO KZG tests | ✅ Done |
| M1 | Lean 4 string codegen (proof-free PoC) | ✅ Done |
| M2 | Deep embedding: StableHLO AST + ZMod semantics | ✅ Done |
| M3 | Correctness theorems (Horner, synthetic div, KZG evaluate) | ✅ Done |
| M4 | AST extension: EC point ops (add, double, scalar mul, MSM) | ✅ Done |
| M5 | Full KZG: commit + prove + verify (end-to-end proof, no sorry) | ✅ Done |

### Phase 2: Library Interface 🔜

| Milestone | Description | Status |
|-----------|-------------|--------|
| M6 | Reusable primitive library (PrimeField, Polynomial, EllipticCurve modules) | ⬜ Planned |
| M7 | DSL usability (macros, ergonomic syntax) | ⬜ Planned |
| M8 | Serializer hardening (round-trip tests, MLIR conformance) | ⬜ Planned |

### Phase 3: Production 🔜

| Milestone | Description | Status |
|-----------|-------------|--------|
| M9 | Production pipeline (CI, integration with prime-ir-opt, documentation) | ⬜ Planned |

## M0: StableHLO KZG Tests

Test vector: p(x) = 1 + 2x + 3x² + 4x³, SRS = [G, 2G, 3G, 4G]

| Test | Description | Expected |
|------|-------------|----------|
| `kzg_evaluate` | Horner evaluation + synthetic division | p(5) = 586, q = [117, 23, 4] |
| `kzg_commit` | MSM commitment (3-way comparison) | C = 30 · G |
| `kzg_prove` | Full KZG prove pipeline | C = 30 · G, π = 175 · G |

The `mlir/` files are reference test vectors in the StableHLO dialect, originally validated against an external MLIR toolchain.

## M5: KZG Correctness (no sorry)

End-to-end theorem: commit → prove → verify pipeline proven via polynomial identity + pairing bilinearity.

- `horner_correct`: Horner evaluation matches `polyEval` spec
- `syntheticDiv_correct`: synthetic division matches spec
- `syntheticDiv_polynomial_correct`: `q(x) · (x - z) + p(z) = p(x)`
- `evaluate_correct`: end-to-end KZG evaluate
- `kzg_correctness`: full commit → prove → verify correctness

Pairing is axiomatized (bilinearity + non-degeneracy). Axiom consistency verified via trivial model (G₁ = G₂ = G_T = ZMod p, e(a,b) = a·b).
