-- Copyright (C) 2026 Soowon Jeong.
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see <https://www.gnu.org/licenses/>.

import LeanStableHLO.StableHLO.Pairing.Miller

/-!
# Final Exponentiation for BN254 Pairing

Computes f^((p¹² - 1) / r) which maps the Miller loop output to an
element of the r-th roots of unity (the target group G_T).

## Decomposition

The exponent (p¹² - 1) / r factors as:

  (p¹² - 1) / r = (p⁶ - 1) · (p² + 1) · (p⁴ - p² + 1) / r

- **Easy part**: f^(p⁶ - 1) · f^(p² + 1) — uses Frobenius and conjugation
- **Hard part**: f^((p⁴ - p² + 1) / r) — uses addition chain with Frobenius

## Implementation

For the initial implementation, we use a simplified approach:
compute the exponent directly via binary exponentiation.
The optimized Frobenius-based approach can be added later.
-/

namespace LeanStableHLO.StableHLO.ConcretePairing

open FieldExt BN254

-- ============================================================================
-- Frobenius Endomorphism (simplified)
-- ============================================================================

/-- Frobenius endomorphism on Fp2: (a₀, a₁) ↦ (a₀, -a₁) = conjugate.
    This is Frob_p since p ≡ 3 (mod 4), so u^p = -u. -/
def frobFp2 (a : Fp2 basePrime) : Fp2 basePrime := a.conj

/-- Conjugation on Fp12: a₀ + a₁w ↦ a₀ - a₁w.
    This is f^(p⁶) for elements in the cyclotomic subgroup. -/
def conjugateFp12 (f : Fp12 basePrime) : Fp12 basePrime := f.conj

-- ============================================================================
-- Easy Part: f^((p⁶ - 1)(p² + 1))
-- ============================================================================

/-- Easy part of the final exponentiation: `f^((p⁶ - 1)(p² + 1))`.
    1. `f₁ = f^(p⁶ - 1) = conj(f) · f⁻¹`
       (the p⁶-Frobenius on `F_{p¹²} = F_{p⁶}(w)`, `w² ∈ F_{p⁶}` a non-residue,
       acts as the `F_{p⁶}`-conjugation `a + bw ↦ a - bw`).
    2. `f₂ = f₁^(p² + 1) = f₁^(p²) · f₁`.

    `f₁^(p²)` is the `p²`-power Frobenius. Rather than the optimized
    coefficient formulas (which need precomputed Frobenius constants and are a
    common source of bugs), we compute it by direct exponentiation
    `powNat f₁ (p²)`. This is a spec-level definition used only inside the
    pairing axioms, so correctness — not speed — is what matters here. -/
def easyPart (f : Fp12 basePrime) : Fp12 basePrime :=
  -- f^(p⁶ - 1): conjugate then divide.
  let f1 := conjugateFp12 f * f⁻¹
  -- f^(p² + 1) = f₁^(p²) · f₁, with f₁^(p²) computed directly.
  Fp12.powNat f1 (basePrime ^ 2) * f1

-- ============================================================================
-- Hard Part: f^((p⁴ - p² + 1) / r)
--
-- For BN curves, this decomposes using the BN parameter x:
--   (p⁴ - p² + 1) / r = (x + 1)·p³ + (x² - x)·p² + ...
-- This requires an optimized addition chain with Frobenius maps.
--
-- For the initial implementation, we compute the exponent directly.
-- ============================================================================

/-- The hard part exponent: (p⁴ - p² + 1) / r.
    For BN254 this is a specific large number. We compute it symbolically. -/
private def hardPartExp : Nat :=
  let p := basePrime
  let r := scalarPrime
  (p ^ 4 - p ^ 2 + 1) / r

/-- Hard part of the final exponentiation: f^((p⁴ - p² + 1) / r).
    Uses binary exponentiation. -/
def hardPart (f : Fp12 basePrime) : Fp12 basePrime :=
  Fp12.powNat f hardPartExp

-- ============================================================================
-- Complete Final Exponentiation
-- ============================================================================

/-- Final exponentiation: f^((p¹² - 1) / r).
    = easyPart(f) then hardPart. -/
def finalExp (f : Fp12 basePrime) : Fp12 basePrime :=
  hardPart (easyPart f)

-- ============================================================================
-- Complete Pairing
-- ============================================================================

/-- BN254 optimal Ate pairing: e(P, Q) = finalExp(millerLoop(P, Q)). -/
def ate (P : Option (ZMod basePrime × ZMod basePrime))
    (Q : G2Point) : Fp12 basePrime :=
  finalExp (millerLoop P Q)

end LeanStableHLO.StableHLO.ConcretePairing
