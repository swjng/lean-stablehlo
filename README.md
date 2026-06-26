<!-- Copyright (C) 2026 Soowon Jeong.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. -->

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

## Trust model and axiom base

`no sorry` is **not** the same as "axiom-free". The proofs rest on an explicit,
enumerable axiom set, machine-checkable with `#print axioms` (see
`lean/AxiomAudit.lean`, run via `lake env lean AxiomAudit.lean`).

- The **polynomial / evaluation layer** (`evaluate_correct`, `horner_correct`,
  `syntheticDiv_*`) depends on **no custom axioms** — only Lean's standard
  `propext`, `Classical.choice`, `Quot.sound`.

- **KZG correctness / security** additionally rest on a small named set:
  - primality of the BN254 base and scalar fields (`basePrime_prime`,
    `scalarPrime_prime`);
  - field-tower non-vanishing facts used by the concrete `F_{p^12}` arithmetic
    (`Fp2.norm_ne_zero_of_ne_zero`, `Fp6.delta_ne_zero`, `Fp12.norm_ne_zero`);
  - the elliptic-curve group laws / prime-order injectivity on `G1`, `G2`
    (`G1.smul_add`, `G1.smul_smul`, `G2.smul_add`, `G1.smul_injective`, ...);
  - the order-`r` power laws on `G_T` (`GT.pow_add`, `GT.pow_mul`);
  - **bilinearity and non-degeneracy of the pairing** (`e_smul_left`,
    `e_smul_right`, `e_add_left`, `e_nondeg`).

The pairing `e` is **defined as the concrete BN254 optimal Ate pairing**
(`ConcretePairing.ate` = Miller loop + final exponentiation) and `G_T` is the
concrete field `F_{p^12}`. Consequently:

- the `G_T` group laws (`mul_one/comm/assoc`, `pow_one/zero/mul_dist`) are
  **proved** from Mathlib's `Field (Fp12 _)` instance, not assumed;
- `#print axioms kzg_correctness` transitively references the concrete pairing
  implementation, so the verified theorem and the extracted artifact concern the
  same object.

The remaining `e_*` axioms assert that this *concrete* `ate` (with the concrete
`G1`/`G2` scalar multiplication) is bilinear and non-degenerate — the genuine
BN254 pairing content, not available in Mathlib. The concrete `ate` has been
**numerically validated** to satisfy these properties: the compiled harness
`lean/PairingTest.lean` (`lake exe pairing-test`) confirms, on the standard
generators, that `e(P,Q) ≠ 1`, `e(P,Q)^r = 1`, and bilinearity in *both*
arguments — `e([k]P,Q) = e(P,[k]Q) = e(P,Q)^k` for `k = 2,3,7`, plus the mixed
check `e([2]P,[3]Q) = e(P,Q)^6` (numerical spot-checks, not a proof); and the
Miller-loop count is
machine-checked (`native_decide` in `Pairing/Miller.lean`) to equal `6x + 2`.
So the `e_*` axioms are empirically consistent (no longer provably false),
though still **not formally proven in Lean**. Proving them — and discharging the
`G1`/`G2` group laws via Mathlib's `WeierstrassCurve` group law — is future work
(gap 1 options B/C).
