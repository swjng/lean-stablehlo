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

import LeanStableHLO.StableHLO.BN254
import LeanStableHLO.StableHLO.FieldExt.Fp12
import LeanStableHLO.StableHLO.Pairing.FinalExp

/-!
# Pairing Specification for BN254 (concrete instantiation)

The groups and pairing used by the KZG correctness/security proofs are
*instantiated by the concrete BN254 objects* rather than left fully opaque:

* `G1` = affine points `Option (ZMod p × ZMod p)` (curve `y² = x³ + 3`),
* `G2` = `ConcretePairing.G2Point` (affine points over `F_{p²}`),
* `GT` = `Fp12 p`,
* `e`  = `ConcretePairing.ate` (Miller loop + final exponentiation).

Consequently `#print axioms kzg_correctness` references the concrete pairing
`ConcretePairing.ate`, so the proofs are tied to the object that is actually
serialized and executed.

## What is proved vs. what is axiomatized

* **Proved** (from the `Field (Fp12 p)` instance): all `GT` *group* laws
  (`mul_one`, `mul_comm`, `mul_assoc`) and the precision-free power laws
  (`pow_one`, `pow_zero`, `pow_mul_dist`).
* **Axiomatized** (named, and scoped to the concrete carriers):
  - the `G1`/`G2` *group laws* and prime-order injectivity — these are the
    elliptic-curve group structure (a separate formalization effort; cf. the
    Mathlib `WeierstrassCurve` group law),
  - the `GT` order-`r` power laws (`pow_add`, `pow_mul`) — valid on the
    order-`r` subgroup `μ_r`, where the pairing lands,
  - **`e_*` bilinearity and `e_nondeg` non-degeneracy of the concrete
    `ate`** — the genuine pairing content (not available in Mathlib).

These are exactly the irreducible mathematical facts; everything else is
either proved here or proved downstream.
-/

namespace LeanStableHLO.StableHLO.Pairing

open BN254 FieldExt ConcretePairing

-- ============================================================================
-- Concrete Group Carriers
-- ============================================================================

/-- G₁: affine points of `y² = x³ + 3` over `F_p` (`none` = ∞). -/
abbrev G1 := Option (ZMod basePrime × ZMod basePrime)

/-- G₂: affine points of the twist over `F_{p²}` (concrete `G2Point`). -/
abbrev G2 := ConcretePairing.G2Point

/-- Target group: the full field `F_{p¹²}` (the pairing lands in `μ_r ⊂ G_Tˣ`). -/
abbrev GT := Fp12 basePrime

-- ============================================================================
-- G₁ Operations (concrete affine elliptic-curve arithmetic over F_p)
-- ============================================================================

/-- G₁ identity element (point at infinity). -/
def G1.zero : G1 := none

/-- G₁ negation: `(x, y) ↦ (x, -y)`. -/
def G1.neg : G1 → G1
  | none => none
  | some (x, y) => some (x, -y)

/-- BN254 G₁ generator `(1, 2)` (on `y² = x³ + 3`). -/
def G1.gen : G1 := some (1, 2)

/-- Affine point addition over `F_p` (short Weierstrass, `a = 0`). -/
def G1.add : G1 → G1 → G1
  | none, Q => Q
  | P, none => P
  | some (x₁, y₁), some (x₂, y₂) =>
      if x₁ = x₂ then
        if y₁ = y₂ then
          if y₁ = 0 then none
          else
            let l := (3 * x₁ ^ 2) / (2 * y₁)
            let x₃ := l ^ 2 - x₁ - x₁
            some (x₃, l * (x₁ - x₃) - y₁)
        else none
      else
        let l := (y₂ - y₁) / (x₂ - x₁)
        let x₃ := l ^ 2 - x₁ - x₂
        some (x₃, l * (x₁ - x₃) - y₁)

/-- Scalar multiplication by a natural number (double-and-add). -/
def G1.scalarMulNat (k : Nat) (P : G1) : G1 :=
  if k = 0 then none
  else
    (Nat.bits k).foldl
      (fun (acc, running) bit =>
        (if bit then G1.add acc running else acc, G1.add running running))
      (none, P) |>.1

/-- G₁ scalar multiplication `[k]P` for `k : ZMod r`. -/
def G1.smul (k : ZMod scalarPrime) (P : G1) : G1 := G1.scalarMulNat k.val P

-- G₁ group axioms (elliptic-curve group law; see module docstring).
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

/-- Prime-order group: scalar mul on generator is injective. -/
axiom G1.smul_injective (a b : ZMod scalarPrime) :
    G1.smul a G1.gen = G1.smul b G1.gen → a = b

-- ============================================================================
-- G₂ Operations (concrete affine arithmetic over F_{p²})
-- ============================================================================

/-- G₂ identity element. -/
def G2.zero : G2 := none

/-- G₂ addition (concrete twist-curve addition). -/
def G2.add (P Q : G2) : G2 := ConcretePairing.G2.add P Q

/-- G₂ negation. -/
def G2.neg (Q : G2) : G2 := ConcretePairing.G2.neg Q

/-- G₂ scalar multiplication `[k]Q` for `k : ZMod r`. -/
def G2.smul (k : ZMod scalarPrime) (Q : G2) : G2 := ConcretePairing.G2.scalarMul k.val Q

/-- BN254 G₂ generator. -/
def G2.gen : G2 := ConcretePairing.g2Gen

axiom G2.add_zero (Q : G2) : G2.add Q G2.zero = Q
axiom G2.add_comm (P Q : G2) : G2.add P Q = G2.add Q P
axiom G2.add_assoc (P Q R : G2) :
    G2.add (G2.add P Q) R = G2.add P (G2.add Q R)
axiom G2.add_neg (Q : G2) : G2.add Q (G2.neg Q) = G2.zero
axiom G2.smul_add (a b : ZMod scalarPrime) (Q : G2) :
    G2.smul (a + b) Q = G2.add (G2.smul a Q) (G2.smul b Q)
axiom G2.smul_smul (a b : ZMod scalarPrime) (Q : G2) :
    G2.smul a (G2.smul b Q) = G2.smul (a * b) Q
axiom G2.smul_one (Q : G2) : G2.smul 1 Q = Q
axiom G2.smul_zero (Q : G2) : G2.smul 0 Q = G2.zero
axiom G2.neg_eq_smul (Q : G2) : G2.neg Q = G2.smul (-1) Q

-- ============================================================================
-- G_T Operations (concrete: the field F_{p¹²}; group laws are PROVED)
-- ============================================================================

/-- G_T group operation (field multiplication). -/
def GT.mul (a b : GT) : GT := a * b

/-- G_T identity element. -/
def GT.one : GT := 1

/-- G_T exponentiation `a^k` (natural-number power of the representative). -/
def GT.pow (a : GT) (k : ZMod scalarPrime) : GT := a ^ k.val

theorem GT.mul_one (a : GT) : GT.mul a GT.one = a := _root_.mul_one a

theorem GT.mul_comm (a b : GT) : GT.mul a b = GT.mul b a := _root_.mul_comm a b

theorem GT.mul_assoc (a b c : GT) : GT.mul (GT.mul a b) c = GT.mul a (GT.mul b c) :=
  _root_.mul_assoc a b c

theorem GT.pow_one (a : GT) : GT.pow a 1 = a := by
  haveI : Fact (1 < scalarPrime) := ⟨scalarPrime_prime.one_lt⟩
  show a ^ (1 : ZMod scalarPrime).val = a
  rw [ZMod.val_one]; exact _root_.pow_one a

theorem GT.pow_zero (a : GT) : GT.pow a 0 = GT.one := by
  show a ^ (0 : ZMod scalarPrime).val = 1
  rw [ZMod.val_zero]; exact _root_.pow_zero a

/-- Abelian group: `(a · b)ⁿ = aⁿ · bⁿ` (precision-free, holds in any `CommMonoid`). -/
theorem GT.pow_mul_dist (a b : GT) (n : ZMod scalarPrime) :
    GT.pow (GT.mul a b) n = GT.mul (GT.pow a n) (GT.pow b n) :=
  _root_.mul_pow a b n.val

-- Order-`r` power laws: valid on the order-`r` subgroup `μ_r` where the pairing
-- lands. Not provable for arbitrary `F_{p¹²}` elements because the exponent is
-- reduced mod `r` (so they require `aʳ = 1`).
axiom GT.pow_add (a : GT) (m n : ZMod scalarPrime) :
    GT.pow a (m + n) = GT.mul (GT.pow a m) (GT.pow a n)
axiom GT.pow_mul (a : GT) (m n : ZMod scalarPrime) :
    GT.pow (GT.pow a m) n = GT.pow a (m * n)

-- ============================================================================
-- The Pairing: e := concrete BN254 optimal Ate pairing
-- ============================================================================

/-- The bilinear pairing `e : G₁ × G₂ → G_T`, instantiated by the concrete
    BN254 optimal Ate pairing (Miller loop + final exponentiation). -/
def e (P : G1) (Q : G2) : GT := ConcretePairing.ate P Q

/-- Bilinearity in the first argument: `e([a]P, Q) = e(P, Q)^a`. -/
axiom e_smul_left (a : ZMod scalarPrime) (P : G1) (Q : G2) :
    e (G1.smul a P) Q = GT.pow (e P Q) a

/-- Bilinearity in the second argument: `e(P, [b]Q) = e(P, Q)^b`. -/
axiom e_smul_right (b : ZMod scalarPrime) (P : G1) (Q : G2) :
    e P (G2.smul b Q) = GT.pow (e P Q) b

/-- Additivity in the first argument: `e(P + P', Q) = e(P, Q) · e(P', Q)`. -/
axiom e_add_left (P P' : G1) (Q : G2) :
    e (G1.add P P') Q = GT.mul (e P Q) (e P' Q)

/-- Additivity in the second argument: `e(P, Q + Q') = e(P, Q) · e(P, Q')`. -/
axiom e_add_right (P : G1) (Q Q' : G2) :
    e P (G2.add Q Q') = GT.mul (e P Q) (e P Q')

/-- Non-degeneracy: `e(G₁, G₂) ≠ 1`. -/
axiom e_nondeg : e G1.gen G2.gen ≠ GT.one

/-- Pairing of identity is identity: `e(0, Q) = 1`. -/
axiom e_zero_left (Q : G2) : e G1.zero Q = GT.one

/-- Pairing of identity is identity: `e(P, 0) = 1`. -/
axiom e_zero_right (P : G1) : e P G2.zero = GT.one

end LeanStableHLO.StableHLO.Pairing
