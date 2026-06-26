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

import LeanStableHLO.StableHLO.FieldExt.Fp2

/-!
# G₂: BN254 Twist Curve over Fp2

The sextic twist E': y² = x³ + b' where b' = 3/ξ = 3 · ξ⁻¹.
Points on E' over F_p² map to points on E over F_p¹² via the twist
isomorphism.

## Point Representation

Affine coordinates: `none` = point at infinity, `some (x, y)` = finite point.
All operations use F_p² arithmetic.
-/

namespace LeanStableHLO.StableHLO.ConcretePairing

open FieldExt BN254

/-- G₂ affine point: `none` = ∞, `some (x, y)` = finite point over F_p². -/
abbrev G2Point := Option (Fp2 basePrime × Fp2 basePrime)

-- ============================================================================
-- Twist Curve Coefficient
-- ============================================================================

/-- b' = 3 / ξ where ξ = 9 + u. Twist curve is y² = x³ + b'. -/
noncomputable def twistB : Fp2 basePrime := 3 * Fp2.xi⁻¹

-- ============================================================================
-- Point Operations (affine, over Fp2)
-- ============================================================================

/-- Negate a G₂ point: (x, y) ↦ (x, -y). -/
def G2.neg : G2Point → G2Point
  | none => none
  | some (x, y) => some (x, -y)

/-- Double a G₂ point. Uses tangent slope: λ = 3x² / 2y (a = 0). -/
def G2.double : G2Point → G2Point
  | none => none
  | some (x, y) =>
    let lambda := 3 * x * x / (2 * y)
    let x3 := lambda * lambda - 2 * x
    let y3 := lambda * (x - x3) - y
    some (x3, y3)

/-- Add two distinct G₂ points. Assumes x₁ ≠ x₂ for finite points. -/
def G2.addDistinct : G2Point → G2Point → G2Point
  | none, q => q
  | p, none => p
  | some (x1, y1), some (x2, y2) =>
    let lambda := (y2 - y1) / (x2 - x1)
    let x3 := lambda * lambda - x1 - x2
    let y3 := lambda * (x1 - x3) - y1
    some (x3, y3)

/-- Add two G₂ points (handles all cases). -/
def G2.add (p q : G2Point) : G2Point :=
  match p, q with
  | none, _ => q
  | _, none => p
  | some (x1, y1), some (x2, y2) =>
    if x1 == x2 then
      if y1 == y2 then G2.double (some (x1, y1))
      else none  -- point + negation = ∞
    else G2.addDistinct (some (x1, y1)) (some (x2, y2))

/-- Scalar multiplication: [k]P via double-and-add. -/
def G2.scalarMul (k : Nat) (pt : G2Point) : G2Point :=
  if k = 0 then none
  else
    let bits := k.bits
    bits.foldl
      (fun (acc, running) bit =>
        let acc' := if bit then G2.add acc running else acc
        let running' := G2.double running
        (acc', running'))
      (none, pt) |>.1

-- ============================================================================
-- BN254 G₂ Generator Point
--
-- Standard generator coordinates from the BN254 specification.
-- These are well-known public constants.
-- ============================================================================

/-- G₂ generator x-coordinate (c0 component). -/
private def g2GenX0 : ZMod basePrime :=
  10857046999023057135944570762232829481370756359578518086990519993285655852781

/-- G₂ generator x-coordinate (c1 component). -/
private def g2GenX1 : ZMod basePrime :=
  11559732032986387107991004021392285783925812861821192530917403151452391805634

/-- G₂ generator y-coordinate (c0 component). -/
private def g2GenY0 : ZMod basePrime :=
  8495653923123431417604973247489272438418190587263600148770280649306958101930

/-- G₂ generator y-coordinate (c1 component). -/
private def g2GenY1 : ZMod basePrime :=
  4082367875863433681332203403145435568316851327593401208105741076214120093531

/-- BN254 G₂ generator point. -/
def g2Gen : G2Point :=
  some (⟨g2GenX0, g2GenX1⟩, ⟨g2GenY0, g2GenY1⟩)

end LeanStableHLO.StableHLO.ConcretePairing
