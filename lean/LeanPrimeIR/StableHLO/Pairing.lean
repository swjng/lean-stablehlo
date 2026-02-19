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

import LeanPrimeIR.StableHLO.BN254

/-!
# Pairing Axiomatization for BN254

Opaque types and axioms for the bilinear pairing over BN254.
These are specification-level constructs used in correctness theorems,
not AST-level constructs that generate MLIR.

## Consistency

The axioms assert a bilinear, non-degenerate map between groups of
prime order. BN254 is a pairing-friendly curve where such a map
(optimal Ate pairing) is known to exist. A trivial model
(G₁ = G₂ = G_T = ZMod scalarPrime, e(a,b) = a * b) satisfies all
bilinearity axioms, witnessing that these axioms cannot derive `False`.
-/

namespace LeanPrimeIR.StableHLO.Pairing

open BN254

-- ============================================================================
-- Opaque Group Types (spec-level, not in AST)
-- ============================================================================

/-- Abstract G₁ group element. -/
opaque G1 : Type

/-- Abstract G₂ group element. -/
opaque G2 : Type

/-- Abstract target group G_T element. -/
opaque GT : Type

-- ============================================================================
-- G₁ Operations
-- ============================================================================

/-- G₁ group addition. -/
axiom G1.add : G1 → G1 → G1

/-- G₁ identity element. -/
axiom G1.zero : G1

/-- G₁ negation. -/
axiom G1.neg : G1 → G1

/-- G₁ scalar multiplication: [k]P. -/
axiom G1.smul : ZMod scalarPrime → G1 → G1

/-- G₁ generator. -/
axiom G1.gen : G1

-- G₁ group axioms (needed for algebraic manipulations in proofs)

axiom G1.add_zero (P : G1) : G1.add P G1.zero = P
axiom G1.add_comm (P Q : G1) : G1.add P Q = G1.add Q P
axiom G1.add_assoc (P Q R : G1) : G1.add (G1.add P Q) R = G1.add P (G1.add Q R)
axiom G1.add_neg (P : G1) : G1.add P (G1.neg P) = G1.zero
axiom G1.smul_add (a b : ZMod scalarPrime) (P : G1) :
    G1.smul (a + b) P = G1.add (G1.smul a P) (G1.smul b P)
axiom G1.smul_smul (a b : ZMod scalarPrime) (P : G1) :
    G1.smul a (G1.smul b P) = G1.smul (a * b) P
axiom G1.smul_one (P : G1) : G1.smul 1 P = P
axiom G1.smul_zero (P : G1) : G1.smul 0 P = G1.zero
axiom G1.neg_eq_smul (P : G1) : G1.neg P = G1.smul (-1) P

-- ============================================================================
-- G₂ Operations
-- ============================================================================

/-- G₂ group addition. -/
axiom G2.add : G2 → G2 → G2

/-- G₂ identity element. -/
axiom G2.zero : G2

/-- G₂ negation. -/
axiom G2.neg : G2 → G2

/-- G₂ scalar multiplication: [k]Q. -/
axiom G2.smul : ZMod scalarPrime → G2 → G2

/-- G₂ generator. -/
axiom G2.gen : G2

axiom G2.add_zero (Q : G2) : G2.add Q G2.zero = Q
axiom G2.add_comm (P Q : G2) : G2.add P Q = G2.add Q P
axiom G2.add_neg (Q : G2) : G2.add Q (G2.neg Q) = G2.zero
axiom G2.smul_add (a b : ZMod scalarPrime) (Q : G2) :
    G2.smul (a + b) Q = G2.add (G2.smul a Q) (G2.smul b Q)
axiom G2.smul_one (Q : G2) : G2.smul 1 Q = Q
axiom G2.smul_zero (Q : G2) : G2.smul 0 Q = G2.zero
axiom G2.neg_eq_smul (Q : G2) : G2.neg Q = G2.smul (-1) Q

-- ============================================================================
-- G_T Operations
-- ============================================================================

/-- G_T group operation (written multiplicatively). -/
axiom GT.mul : GT → GT → GT

/-- G_T identity element. -/
axiom GT.one : GT

/-- G_T exponentiation: a^k. -/
axiom GT.pow : GT → ZMod scalarPrime → GT

axiom GT.mul_one (a : GT) : GT.mul a GT.one = a
axiom GT.mul_comm (a b : GT) : GT.mul a b = GT.mul b a
axiom GT.mul_assoc (a b c : GT) : GT.mul (GT.mul a b) c = GT.mul a (GT.mul b c)
axiom GT.pow_one (a : GT) : GT.pow a 1 = a
axiom GT.pow_zero (a : GT) : GT.pow a 0 = GT.one
axiom GT.pow_add (a : GT) (m n : ZMod scalarPrime) :
    GT.pow a (m + n) = GT.mul (GT.pow a m) (GT.pow a n)
axiom GT.pow_mul (a : GT) (m n : ZMod scalarPrime) :
    GT.pow (GT.pow a m) n = GT.pow a (m * n)

-- ============================================================================
-- Pairing Function + Axioms
-- ============================================================================

/-- The bilinear pairing e : G₁ × G₂ → G_T. -/
axiom e : G1 → G2 → GT

/-- Bilinearity in the first argument: e([a]P, Q) = e(P, Q)^a. -/
axiom e_smul_left (a : ZMod scalarPrime) (P : G1) (Q : G2) :
    e (G1.smul a P) Q = GT.pow (e P Q) a

/-- Bilinearity in the second argument: e(P, [b]Q) = e(P, Q)^b. -/
axiom e_smul_right (b : ZMod scalarPrime) (P : G1) (Q : G2) :
    e P (G2.smul b Q) = GT.pow (e P Q) b

/-- Additivity in the first argument: e(P + P', Q) = e(P, Q) · e(P', Q). -/
axiom e_add_left (P P' : G1) (Q : G2) :
    e (G1.add P P') Q = GT.mul (e P Q) (e P' Q)

/-- Additivity in the second argument: e(P, Q + Q') = e(P, Q) · e(P, Q'). -/
axiom e_add_right (P : G1) (Q Q' : G2) :
    e P (G2.add Q Q') = GT.mul (e P Q) (e P Q')

/-- Non-degeneracy: e(G₁, G₂) ≠ 1. -/
axiom e_nondeg : e G1.gen G2.gen ≠ GT.one

/-- Pairing of identity is identity: e(0, Q) = 1. -/
axiom e_zero_left (Q : G2) : e G1.zero Q = GT.one

/-- Pairing of identity is identity: e(P, 0) = 1. -/
axiom e_zero_right (P : G1) : e P G2.zero = GT.one

end LeanPrimeIR.StableHLO.Pairing
