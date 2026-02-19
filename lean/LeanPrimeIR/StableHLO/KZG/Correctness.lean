-- Copyright 2026 The PrimeIR Authors.
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import LeanPrimeIR.StableHLO.KZG
import LeanPrimeIR.StableHLO.Correctness

/-!
# KZG Correctness Theorem

Proves that an honest prover's output passes the verifier's check.

## Theorem Statement

If:
1. SRS is well-formed: srs[i] = [sⁱ] · G₁
2. C = [p(s)] · G₁  (commitment)
3. π = [q(s)] · G₁  (proof from quotient polynomial)
4. v = p(z)          (correct evaluation)

Then the verification equation holds:
  e(π, [s]G₂ - [z]G₂) = e(C - [v]G₁, G₂)

## Proof Strategy

1. **Polynomial identity** (M3): q(x) · (x - z) + p(z) = p(x)
   Evaluated at x = s: q(s) · (s - z) = p(s) - v
2. **Bilinearity**:
   LHS = e([q(s)]G₁, [s-z]G₂) = e(G₁, G₂)^(q(s) · (s-z))
   RHS = e([p(s)-v]G₁, G₂) = e(G₁, G₂)^(p(s) - v)
3. These are equal by the polynomial identity.
-/

namespace LeanPrimeIR.StableHLO.KZG

open Pairing BN254

-- ============================================================================
-- SRS Well-Formedness
-- ============================================================================

/-- SRS is well-formed with respect to secret s:
    each g1Points[i] represents [sⁱ] · G₁.gen at the spec level. -/
def SRS.WellFormed (srs : SRS) (s : ZMod scalarPrime) : Prop :=
  ∀ (i : Nat), i < srs.g1Points.length →
    ∃ (gi : Pairing.G1), gi = Pairing.G1.smul (s ^ i) Pairing.G1.gen

-- ============================================================================
-- Main Correctness Theorem
-- ============================================================================

/-- **KZG correctness**: an honest prover's output passes verification.

    Given well-formed SRS with secret s:
    - C = [p(s)]G₁  (commitment via MSM)
    - v = p(z)       (polynomial evaluation)
    - π = [q(s)]G₁   (proof via quotient MSM)

    The verification equation holds because:
    1. q(s) · (s - z) = p(s) - v  (polynomial identity at x = s)
    2. e(π, [s-z]G₂) = e(G₁,G₂)^(q(s)·(s-z))  (bilinearity)
    3. e(C - [v]G₁, G₂) = e(G₁,G₂)^(p(s)-v)    (bilinearity)
    4. These are equal by (1). -/
theorem kzg_correctness
    (coeffs : List (ZMod scalarPrime))
    (z s : ZMod scalarPrime)
    -- Spec-level group elements for C and π
    (C : Pairing.G1)
    (hC : C = Pairing.G1.smul (polyEval coeffs s) Pairing.G1.gen)
    (π : Pairing.G1)
    (hπ : π = Pairing.G1.smul (polyEval (syntheticDivSpec coeffs z) s)
                               Pairing.G1.gen)
    -- G₂ elements
    (sG2 : Pairing.G2)
    (hsG2 : sG2 = Pairing.G2.smul s Pairing.G2.gen) :
    verify C z (polyEval coeffs z) π sG2 Pairing.G2.gen := by
  unfold verify
  -- Substitute C and π definitions
  rw [hC, hπ, hsG2]
  -- LHS: e([q(s)]G₁, [s]G₂ + [-z]G₂)
  -- [s]G₂ + [-z]G₂ = [(s-z)]G₂ by G₂.smul_add
  rw [← Pairing.G2.smul_add s (-z) Pairing.G2.gen]
  -- e([q(s)]G₁, [s-z]G₂) = e(G₁,G₂)^(q(s)·(s-z)) by bilinearity
  rw [Pairing.e_smul_left, Pairing.e_smul_right]
  -- RHS: e([p(s)]G₁ + [-v]G₁, G₂)
  -- [p(s)]G₁ + [-v]G₁ = [p(s)-v]G₁ by G₁.smul_add
  rw [← Pairing.G1.smul_add (polyEval coeffs s) (-(polyEval coeffs z)) Pairing.G1.gen]
  rw [Pairing.e_smul_left]
  -- Now both sides are GT.pow (e G₁ G₂) (something)
  -- LHS exponent: q(s) · (s + (-z)) = q(s) · (s - z)
  -- RHS exponent: p(s) + (-v) = p(s) - v
  -- By polynomial identity: q(s) · (s - z) = p(s) - v
  rw [GT.pow_mul]
  congr 1
  -- Need: polyEval (syntheticDivSpec coeffs z) s * (s + -z) =
  --       polyEval coeffs s + -polyEval coeffs z
  -- This follows from syntheticDiv_polynomial_correct evaluated at s
  have hpoly := syntheticDiv_polynomial_correct coeffs z
  -- hpoly : listPoly(syndivSpec) * (X - C z) + C(polyEval coeffs z) = listPoly coeffs
  -- Evaluate both sides at s using Polynomial.eval
  have heval : (listPoly (syntheticDivSpec coeffs z) *
    (_root_.Polynomial.X - _root_.Polynomial.C z) +
    _root_.Polynomial.C (polyEval coeffs z)).eval s = (listPoly coeffs).eval s :=
    congrArg (·.eval s) hpoly
  simp only [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_sub, _root_.Polynomial.eval_X,
    _root_.Polynomial.eval_C] at heval
  -- heval : syndivSpec(s) * (s - z) + polyEval coeffs z = listPoly(coeffs)(s)
  -- Bridge polyEval ↔ Polynomial.eval via polyEval_eq_polynomial_eval
  -- heval has: (listPoly syndiv).eval s * (s-z) + polyEval coeffs z = (listPoly coeffs).eval s
  -- Bridge both Polynomial.eval to polyEval
  rw [← polyEval_eq_polynomial_eval (syntheticDivSpec coeffs z) s] at heval
  rw [← polyEval_eq_polynomial_eval coeffs s] at heval
  -- heval : polyEval(syndivSpec, s) * (s - z) + polyEval(coeffs, z) = polyEval(coeffs, s)
  -- Goal: (s + -z) * q(s) = p(s) + -v, which is q(s)*(s-z) = p(s)-v by ring
  linear_combination heval

end LeanPrimeIR.StableHLO.KZG
