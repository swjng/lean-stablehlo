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

import LeanPrimeIR.StableHLO.KZG.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# KZG Security Properties

Game-based security reductions for KZG polynomial commitments.

## Evaluation Binding

Given the same commitment C and evaluation point z, if two valid openings
(v, π) and (v', π') exist with v ≠ v', we can extract a witness W such that
e(W, [s-z]G₂) = e(G₁, G₂). This constitutes a t-SDH pair extraction,
breaking the t-SDH assumption.

## Polynomial Binding

Given the same commitment C for two different polynomials p ≠ p', the secret
s must be a root of (p - p'). Since deg(p - p') ≤ t, this means s is one of
at most t values, which is negligible over a large field.
-/

namespace LeanPrimeIR.StableHLO.KZG

open Pairing BN254

-- ============================================================================
-- G_T Helper Lemmas
-- ============================================================================

theorem GT.one_mul (a : GT) : GT.mul GT.one a = a := by
  rw [GT.mul_comm]; exact GT.mul_one a

theorem GT.pow_neg_one (a : GT) : GT.mul (GT.pow a (-1)) a = GT.one := by
  have h := GT.pow_add a (-1) 1
  rw [show (-1 : ZMod scalarPrime) + 1 = 0 from by ring, GT.pow_zero, GT.pow_one] at h
  exact h.symm

theorem GT.mul_inv (a : GT) : GT.mul a (GT.pow a (-1)) = GT.one := by
  rw [GT.mul_comm]; exact GT.pow_neg_one a

theorem GT.mul_left_cancel (a b c : GT) (h : GT.mul a b = GT.mul a c) : b = c := by
  have := congrArg (GT.mul (GT.pow a (-1))) h
  rw [← GT.mul_assoc, ← GT.mul_assoc, GT.pow_neg_one, GT.one_mul, GT.one_mul] at this
  exact this

private theorem gt_cancel_common
    (a b c : GT) (n : ZMod scalarPrime) :
    GT.pow (GT.mul (GT.mul a b) (GT.mul (GT.pow a (-1)) c)) n =
    GT.pow (GT.mul b c) n := by
  congr 1
  rw [GT.mul_assoc, ← GT.mul_assoc b (GT.pow a (-1)) c,
      GT.mul_comm b (GT.pow a (-1)), GT.mul_assoc (GT.pow a (-1)) b c,
      ← GT.mul_assoc a (GT.pow a (-1)) (GT.mul b c),
      GT.mul_inv, GT.one_mul]

private theorem gt_pow_combine (g : GT) (v v' : ZMod scalarPrime) :
    GT.mul (GT.pow g (-v)) (GT.pow g v') = GT.pow g (v' - v) := by
  rw [← GT.pow_add]; congr 1; ring

-- ============================================================================
-- Evaluation Binding
-- ============================================================================

/-- **Evaluation binding**: two valid openings for the same (C, z) with v ≠ v'
    yield a witness W such that e(W, [s-z]G₂) = e(G₁, G₂).

    This witnesses the q-DLOG relation: given [s-z]G₂ from the SRS,
    the adversary computes W = [(v'-v)⁻¹](π - π') satisfying
    e(W, [s-z]G₂) = e(G₁, G₂), implying W = [(s-z)⁻¹]G₁.
    Existence of such W contradicts the t-SDH assumption. -/
theorem evaluation_binding
    (C : Pairing.G1) (z v v' : ZMod scalarPrime)
    (π π' : Pairing.G1)
    (s : ZMod scalarPrime)
    (sG2 : Pairing.G2)
    (_hsG2 : sG2 = Pairing.G2.smul s Pairing.G2.gen)
    (hv1 : verify C z v π sG2 Pairing.G2.gen)
    (hv2 : verify C z v' π' sG2 Pairing.G2.gen)
    (hne : v ≠ v') :
    let W := G1.smul ((v' - v)⁻¹) (G1.add π (G1.neg π'))
    Pairing.e W (G2.add sG2 (G2.smul (-z) G2.gen)) =
    Pairing.e G1.gen G2.gen := by
  intro W
  have hd_ne : v' - v ≠ 0 := sub_ne_zero.mpr hne.symm
  unfold verify at hv1 hv2
  -- Expand W and apply bilinearity
  show Pairing.e (G1.smul ((v' - v)⁻¹) (G1.add π (G1.neg π')))
       (G2.add sG2 (G2.smul (-z) G2.gen)) = Pairing.e G1.gen G2.gen
  -- e([d⁻¹](π - π'), szG₂) = (e(π - π', szG₂))^(d⁻¹)
  rw [Pairing.e_smul_left, Pairing.e_add_left, G1.neg_eq_smul, Pairing.e_smul_left]
  -- Substitute verification equations
  rw [hv1, hv2]
  -- Expand e(C + [-v]G₁, G₂) and e(C + [-v']G₁, G₂)
  rw [Pairing.e_add_left C (G1.smul (-v) G1.gen) G2.gen,
      Pairing.e_smul_left (-v) G1.gen G2.gen,
      Pairing.e_add_left C (G1.smul (-v') G1.gen) G2.gen,
      Pairing.e_smul_left (-v') G1.gen G2.gen]
  -- Distribute (-1) power: (e(C,G₂) · g^(-v'))⁻¹ = e(C,G₂)⁻¹ · g^v'
  rw [GT.pow_mul_dist (Pairing.e C G2.gen)
        (GT.pow (Pairing.e G1.gen G2.gen) (-v')) (-1)]
  -- Simplify g^(-v') raised to (-1) = g^v'
  rw [GT.pow_mul (Pairing.e G1.gen G2.gen) (-v') (-1),
      show (-v' : ZMod scalarPrime) * (-1) = v' from by ring]
  -- Cancel e(C,G₂) · e(C,G₂)⁻¹
  rw [gt_cancel_common (Pairing.e C G2.gen)
        (GT.pow (Pairing.e G1.gen G2.gen) (-v))
        (GT.pow (Pairing.e G1.gen G2.gen) v')]
  -- g^(-v) · g^(v') = g^(v' - v) = g^d
  rw [gt_pow_combine (Pairing.e G1.gen G2.gen) v v']
  -- g^d raised to d⁻¹ = g^(d · d⁻¹) = g¹ = g
  rw [GT.pow_mul (Pairing.e G1.gen G2.gen) (v' - v) ((v' - v)⁻¹)]
  have hmul : (v' - v) * (v' - v)⁻¹ = (1 : ZMod scalarPrime) := by
    exact mul_inv_cancel₀ hd_ne
  rw [hmul, GT.pow_one]

-- ============================================================================
-- Polynomial Binding
-- ============================================================================

/-- **Polynomial binding (algebraic core)**: if two coefficient lists produce the
    same commitment under a well-formed SRS, they evaluate to the same value at
    the secret s. -/
theorem polynomial_binding_algebraic
    (coeffs coeffs' : List (ZMod scalarPrime))
    (s : ZMod scalarPrime)
    (srs : SpecSRS) (hwf : SpecSRS.WellFormed srs s)
    (hlen : coeffs.length ≤ srs.length)
    (hlen' : coeffs'.length ≤ srs.length)
    (hC : G1.innerProduct coeffs srs = G1.innerProduct coeffs' srs) :
    polyEval coeffs s = polyEval coeffs' s := by
  have h1 := innerProduct_wellformed coeffs srs s hwf hlen
  have h2 := innerProduct_wellformed coeffs' srs s hwf hlen'
  rw [h1, h2] at hC
  exact G1.smul_injective _ _ hC

/-- **Polynomial binding (root reduction)**: if two different polynomials produce
    the same commitment, the secret s is a root of their difference.

    Since deg(p - p') ≤ t (the SRS degree), s is one of at most t values. -/
theorem polynomial_binding_root
    (coeffs coeffs' : List (ZMod scalarPrime))
    (s : ZMod scalarPrime)
    (srs : SpecSRS) (hwf : SpecSRS.WellFormed srs s)
    (hlen : coeffs.length ≤ srs.length)
    (hlen' : coeffs'.length ≤ srs.length)
    (hC : G1.innerProduct coeffs srs = G1.innerProduct coeffs' srs)
    (_hdiff : listPoly coeffs ≠ listPoly coeffs') :
    (listPoly coeffs - listPoly coeffs').IsRoot s := by
  show (listPoly coeffs - listPoly coeffs').eval s = 0
  rw [_root_.Polynomial.eval_sub]
  have halg := polynomial_binding_algebraic coeffs coeffs' s srs hwf hlen hlen' hC
  rw [polyEval_eq_polynomial_eval, polyEval_eq_polynomial_eval] at halg
  exact sub_eq_zero.mpr halg

/-- **Polynomial binding (security)**: the secret s lies in the root set of (p - p'),
    connecting to the t-SDH hardness assumption. -/
theorem polynomial_binding_security
    (coeffs coeffs' : List (ZMod scalarPrime))
    (s : ZMod scalarPrime)
    (srs : SpecSRS) (hwf : SpecSRS.WellFormed srs s)
    (hlen : coeffs.length ≤ srs.length)
    (hlen' : coeffs'.length ≤ srs.length)
    (hC : G1.innerProduct coeffs srs = G1.innerProduct coeffs' srs)
    (hdiff : listPoly coeffs ≠ listPoly coeffs') :
    s ∈ (listPoly coeffs - listPoly coeffs').roots :=
  (_root_.Polynomial.mem_roots (sub_ne_zero.mpr hdiff)).mpr
    (polynomial_binding_root coeffs coeffs' s srs hwf hlen hlen' hC hdiff)

end LeanPrimeIR.StableHLO.KZG
