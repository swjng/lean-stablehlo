# lean-prime-ir Roadmap

## Goal

Provide a **library** for writing cryptographic protocols in Lean 4 that
generates **formally verified** StableHLO MLIR. Users write their protocols
using the deep-embedded DSL, prove correctness in Lean, and extract
verified MLIR through a trivial serializer.

KZG commitment scheme is the first PoC to validate the approach.

## Architecture Decision

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

## Milestones

### Phase 1: KZG PoC

Prove the deep embedding approach works end-to-end with KZG.

#### M0: Hand-written Prime-IR KZG Tests [DONE]

Validate KZG pipeline with hand-written MLIR.

- [x] `kzg_evaluate.mlir` — Horner + synthetic division
- [x] `kzg_commit.mlir` — MSM commitment (3-way comparison)
- [x] `kzg_prove.mlir` — Full KZG prove pipeline
- [x] BN254 field/EC definitions (`mlir/defs/`)

#### M1: String Codegen [DONE]

Lean 4 → StableHLO string codegen (proof-free PoC).

- [x] `IR.lean` — MLIR type representation + IRBuilder monad
- [x] `Field.lean` — StableHLO field ops (const, add, mul, sub, div, pow, neg)
- [x] `Polynomial.lean` — Horner evaluation + synthetic division
- [x] `KZG.lean` — Complete StableHLO module generation
- [x] `Main.lean` — Runnable demo
- [x] Generated `kzg_evaluate.stablehlo.mlir` validated

**Limitation**: String codegen has no formal connection between Lean proofs
and the output MLIR.

#### M2: Deep Embedding Foundation [DONE]

Deep embed StableHLO AST as Lean types + Mathlib ZMod semantics.

- [x] `StableHLO/Expr.lean` — `Expr p` inductive (const, add, mul, sub, neg)
- [x] `StableHLO/Expr.lean` — `Expr.eval` denotational semantics (ZMod p)
- [x] `StableHLO/Serialize.lean` — AST → MLIR text serializer
- [x] `StableHLO/Polynomial.lean` — Horner + synthetic div (pure AST)
- [x] `StableHLO/KZG.lean` — KZG evaluate pipeline
- [x] Mathlib v4.27.0 dependency
- [x] M1 vs M2 output comparison (Main.lean)

#### M3: Correctness Theorems [DONE]

Add correctness proofs over the deep-embedded AST.

- [x] Define `polyEval` spec: `List (ZMod p) → ZMod p → ZMod p`
- [x] Define `syntheticDivSpec` spec: `List (ZMod p) → ZMod p → List (ZMod p)`
- [x] `horner_correct`: `(hornerExpr coeffs z).eval = polyEval coeffs z`
- [x] `syntheticDiv_correct`:
      `(syntheticDivExpr coeffs z).map Expr.eval = syntheticDivSpec coeffs z`
- [x] `evaluate_correct`: end-to-end KZG evaluate theorem composing the above
- [x] Bridge between `polyEval` and Mathlib's `Polynomial` type
      (`polyEval_eq_polynomial_eval` via `listPoly` + `Polynomial.ofFn`)
- [x] `syntheticDivSpec` mathematical correctness:
      `q(x) · (x - z) + p(z) = p(x)` (`syntheticDiv_polynomial_correct`)

#### M4: AST Extension — EC Point Operations [DONE]

Add elliptic curve operations to Expr (StableHLO has no native EC ops,
so point arithmetic is expressed as field ops on coordinates).

- [x] `Fact (Nat.Prime p)` instance for BN254 (needed for field ops: div, inv)
- [x] Affine point type: `(Expr p, Expr p)`
- [x] Point addition (short Weierstrass): `addAffine`
- [x] Point doubling: `doubleAffine`
- [x] Scalar multiplication (double-and-add)
- [x] MSM (multi-scalar multiplication) — naive
- [x] EC ops correctness: prove `eval` results match Mathlib Weierstrass formulas
- [x] `Expr.div` zero-division semantics: `ZMod p` returns 0 for 0⁻¹,
      StableHLO lowering uses `stablehlo.divide`
- [ ] Tree AST blowup mitigation for scalar mul (double-and-add produces
      exponential tree without sharing; deferred to future `Expr.let` or CSE)

#### M5: Full KZG Commitment Scheme

Implement KZG commit + prove + verify via deep embedding.

- [ ] `kzg_commit`: MSM(SRS, coeffs) → commitment point
- [ ] `kzg_prove`: quotient poly → MSM → proof point
- [ ] `kzg_verify`: pairing check (pairing may be axiomatized)
- [ ] If pairing axiomatized: verify axiom consistency (no `False` derivable)
- [ ] End-to-end: commit → prove → verify pipeline
- [ ] Equivalence check against M0 hand-written MLIR output

### Phase 2: Library Interface

Package the primitives as a reusable library so users can write their
own cryptographic protocols without touching serialization internals.

#### M6: Reusable Primitive Library

Factor out protocol-agnostic building blocks from KZG-specific code.

- [ ] `PrimeField` module: field arithmetic DSL (add, mul, sub, neg, inv)
- [ ] `Polynomial` module: evaluation, interpolation, division
- [ ] `EllipticCurve` module: point ops, scalar mul, MSM
- [ ] Clean public API: users compose primitives to build protocols
- [ ] Proven lemma library for each primitive

#### M7: DSL Usability

Make the embedded DSL ergonomic for protocol authors.

- [ ] Lean macro/elaborator so users write near-normal Lean syntax
- [ ] Automatic `Expr` construction from Lean expressions where possible
- [ ] Error messages that guide users toward provable constructions
- [ ] Examples: KZG as a library-user example (dogfooding)

#### M8: Serializer Hardening

Strengthen trust in the serializer (the only unverified component).

- [ ] Verify `valStr` (ZMod p → String) correctness: `v.val` produces
      the decimal string that StableHLO `dense<>` expects
- [ ] Round-trip test: serialize → parse → compare AST
- [ ] MLIR syntax conformance (parseable by prime-ir-opt)
- [ ] Property-based testing for the serializer
- [ ] (Optional) Partial verification of the serializer

### Phase 3: Production

#### M9: Production Pipeline

- [ ] Remove M1 string codegen (fully replaced by deep embedding)
- [ ] M2 output execution validation: pipe generated StableHLO through
      stablehlo → prime-ir → llvm pipeline and compare against M0 results
- [ ] Integration tests with `prime-ir-opt` pipeline
- [ ] CI: `lake build` + correctness theorem verification
- [ ] Document trust assumptions:
      - StableHLO `field.pf` ops ↔ ZMod p arithmetic correspondence
      - `stablehlo.constant dense<v>` takes standard form value, lowering
        handles Montgomery conversion (SFm type)
- [ ] Documentation: trust model, library API guide, tutorial

## Dependencies

```
Mathlib (ZMod, Polynomial, ...)
    ↑
lean-prime-ir (this project — library)
    ↑ (used by)                ↓ (generates)
user protocols              StableHLO MLIR
                               ↓ (consumed by)
                            zkir/prime-ir-opt → LLVM → binary
```

## Key Design Decisions

1. **Mathlib ZMod** for semantics — full algebraic structure available
2. **autoImplicit = false** — all type variables explicitly bound
3. **Keep M1 code** — preserved as comparison baseline until deep embedding
   fully replaces it
4. **AST is tree-structured** — no SSA value sharing (MLIR optimizer handles CSE)
5. **`Expr p` with `p` at type level** — type-safe separation between fields
6. **Library-first design** — users should be able to write their own protocols
   using the provided primitives without modifying the framework
