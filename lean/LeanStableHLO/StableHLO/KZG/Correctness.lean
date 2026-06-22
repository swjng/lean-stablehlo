-- Copyright 2026 Soowon Jeong.
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

import LeanStableHLO.StableHLO.KZG
import LeanStableHLO.StableHLO.Correctness

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

## End-to-End Theorem

The end-to-end theorem (`kzg_end_to_end`) connects all pieces:
- SRS well-formedness → inner product computes [p(s)]G₁
- Synthetic division → quotient inner product computes [q(s)]G₁
- Verification equation holds by bilinearity + polynomial identity
-/

namespace LeanStableHLO.StableHLO.KZG

open Pairing BN254

-- ============================================================================
-- Spec-Level SRS
-- ============================================================================

/-- Spec-level SRS: list of G₁ elements representing [s⁰]G, [s¹]G, ... -/
abbrev SpecSRS := List Pairing.G1

/-- Well-formedness: each element equals [sⁱ]G₁. -/
def SpecSRS.WellFormed (srs : SpecSRS) (s : ZMod scalarPrime) : Prop :=
  ∀ (i : Nat) (hi : i < srs.length),
    srs[i] = Pairing.G1.smul (s ^ i) Pairing.G1.gen

-- ============================================================================
-- Spec-Level Inner Product (MSM)
-- ============================================================================

/-- Spec-level inner product: ∑ cᵢ · Pᵢ in G₁. -/
noncomputable def G1.innerProduct :
    List (ZMod scalarPrime) → List Pairing.G1 → Pairing.G1
  | [], _ => Pairing.G1.zero
  | _, [] => Pairing.G1.zero
  | c :: cs, p :: ps => Pairing.G1.add (Pairing.G1.smul c p) (G1.innerProduct cs ps)

/-- Scalar-level weighted sum: ∑ cᵢ · s^(i + off). -/
def scalarIP : List (ZMod scalarPrime) → ZMod scalarPrime → Nat → ZMod scalarPrime
  | [], _, _ => 0
  | c :: cs, s, off => c * s ^ off + scalarIP cs s (off + 1)

-- ============================================================================
-- scalarIP ↔ polyEval Bridge
-- ============================================================================

/-- Generalized lemma: scalarIP with offset factors out s^off. -/
theorem scalarIP_shift
    (cs : List (ZMod scalarPrime)) (s : ZMod scalarPrime) (off : Nat) :
    scalarIP cs s off = s ^ off * polyEval cs s := by
  induction cs generalizing off with
  | nil => simp [scalarIP, polyEval]
  | cons c cs ih =>
    simp only [scalarIP]
    rw [ih, polyEval_cons]
    ring

/-- scalarIP at offset 0 equals polyEval. -/
theorem scalarIP_eq_polyEval
    (cs : List (ZMod scalarPrime)) (s : ZMod scalarPrime) :
    scalarIP cs s 0 = polyEval cs s := by
  rw [scalarIP_shift]; simp

-- ============================================================================
-- G₁ Helper Lemma
-- ============================================================================

theorem G1.zero_add (P : Pairing.G1) : Pairing.G1.add Pairing.G1.zero P = P := by
  rw [Pairing.G1.add_comm]; exact Pairing.G1.add_zero P

-- ============================================================================
-- Inner Product Well-Formedness
-- ============================================================================

/-- Generalized inner product theorem with offset. Under SRS well-formedness
    (shifted by offset), inner product equals [scalarIP coeffs s off]G₁. -/
theorem innerProduct_wellformed_aux
    (coeffs : List (ZMod scalarPrime))
    (srs : List Pairing.G1) (s : ZMod scalarPrime) (off : Nat)
    (hwf : ∀ (i : Nat) (hi : i < srs.length),
      srs[i] = Pairing.G1.smul (s ^ (i + off)) Pairing.G1.gen)
    (hlen : coeffs.length ≤ srs.length) :
    G1.innerProduct coeffs srs =
    Pairing.G1.smul (scalarIP coeffs s off) Pairing.G1.gen := by
  induction coeffs generalizing srs off with
  | nil =>
    simp only [G1.innerProduct, scalarIP]
    exact (Pairing.G1.smul_zero Pairing.G1.gen).symm
  | cons c cs ih =>
    cases srs with
    | nil => simp at hlen
    | cons p ps =>
      simp only [G1.innerProduct, scalarIP]
      -- Normalize List.length for omega
      have hlen' : cs.length ≤ ps.length := by
        simp only [List.length_cons] at hlen; omega
      -- p = [s^off]G₁ from hwf at index 0
      have hp : p = Pairing.G1.smul (s ^ off) Pairing.G1.gen := by
        have := hwf 0 (by simp only [List.length_cons]; omega)
        simpa [Nat.zero_add] using this
      -- G₁.smul c p = G₁.smul (c * s^off) gen by smul_smul
      have hcp : Pairing.G1.smul c p =
          Pairing.G1.smul (c * s ^ off) Pairing.G1.gen := by
        rw [hp, Pairing.G1.smul_smul]
      -- IH for tail: hwf shifted by 1
      have hwf' : ∀ (i : Nat) (hi : i < ps.length),
          ps[i] = Pairing.G1.smul (s ^ (i + (off + 1))) Pairing.G1.gen := by
        intro i hi
        have h := hwf (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at h
        rwa [show i + 1 + off = i + (off + 1) from by omega] at h
      rw [hcp, ih ps (off + 1) hwf' hlen', ← Pairing.G1.smul_add]

/-- Under well-formed SRS, inner product equals [polyEval coeffs s]G₁. -/
theorem innerProduct_wellformed
    (coeffs : List (ZMod scalarPrime))
    (srs : SpecSRS) (s : ZMod scalarPrime)
    (hwf : SpecSRS.WellFormed srs s)
    (hlen : coeffs.length ≤ srs.length) :
    G1.innerProduct coeffs srs =
    Pairing.G1.smul (polyEval coeffs s) Pairing.G1.gen := by
  have hwf' : ∀ (i : Nat) (hi : i < srs.length),
      srs[i] = Pairing.G1.smul (s ^ (i + 0)) Pairing.G1.gen := by
    intro i hi; simp only [Nat.add_zero]; exact hwf i hi
  rw [innerProduct_wellformed_aux coeffs srs s 0 hwf' hlen, scalarIP_eq_polyEval]

-- ============================================================================
-- Core Correctness Theorem (assumes C and π as hypotheses)
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
  rw [← polyEval_eq_polynomial_eval (syntheticDivSpec coeffs z) s] at heval
  rw [← polyEval_eq_polynomial_eval coeffs s] at heval
  -- heval : polyEval(syndivSpec, s) * (s - z) + polyEval(coeffs, z) = polyEval(coeffs, s)
  -- Goal: (s + -z) * q(s) = p(s) + -v, which is q(s)*(s-z) = p(s)-v by ring
  linear_combination heval

-- ============================================================================
-- End-to-End Theorem
-- ============================================================================

/-- **KZG end-to-end correctness**: from well-formed SRS to verification equation.

    Given:
    - A well-formed SRS with secret s
    - Polynomial coefficients and evaluation point z
    - Commitment C = innerProduct(coeffs, SRS)
    - Proof π = innerProduct(syntheticDivSpec(coeffs, z), SRS)

    The verification equation holds without assuming C and π values directly.
    Instead, we derive C = [p(s)]G₁ and π = [q(s)]G₁ from SRS well-formedness
    via `innerProduct_wellformed`. -/
theorem kzg_end_to_end
    (coeffs : List (ZMod scalarPrime))
    (z s : ZMod scalarPrime)
    (srs : SpecSRS)
    (hwf : SpecSRS.WellFormed srs s)
    (hlen_p : coeffs.length ≤ srs.length)
    (hlen_q : (syntheticDivSpec coeffs z).length ≤ srs.length)
    (sG2 : Pairing.G2) (hsG2 : sG2 = Pairing.G2.smul s Pairing.G2.gen) :
    verify (G1.innerProduct coeffs srs) z (polyEval coeffs z)
           (G1.innerProduct (syntheticDivSpec coeffs z) srs) sG2 Pairing.G2.gen :=
  kzg_correctness coeffs z s
    (G1.innerProduct coeffs srs)
    (innerProduct_wellformed coeffs srs s hwf hlen_p)
    (G1.innerProduct (syntheticDivSpec coeffs z) srs)
    (innerProduct_wellformed (syntheticDivSpec coeffs z) srs s hwf hlen_q)
    sG2 hsG2

end LeanStableHLO.StableHLO.KZG
