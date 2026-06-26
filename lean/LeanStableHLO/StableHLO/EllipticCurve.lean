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

import LeanStableHLO.StableHLO.Expr

/-!
# Elliptic Curve Point Operations (Deep-Embedded AST)

EC point arithmetic expressed as field operations on coordinates via `Expr p`.
StableHLO has no native EC ops, so point operations are decomposed into
coordinate-level field ops (add, mul, sub, div).

All formulas are for **short Weierstrass** curves with a=0: y² = x³ + b.
This covers BN254 (b=3).

## Point Representation

- `AffinePoint p` = `Option (Expr p × Expr p)` where `none` = point at infinity (∞)

## Limitations

- `addAffine` assumes distinct x-coordinates for finite points (AST-level
  equality testing is not possible). Caller must ensure this precondition.
- `scalarMul` uses double-and-add (right-to-left via `Nat.bits`), producing
  tree-structured AST. For large scalars, tree blowup is a concern (deferred
  to future `Expr.let` or serialization-level memoization).
-/

namespace LeanStableHLO.StableHLO

open Expr

-- ============================================================================
-- Slope Computations (short Weierstrass, a=0)
-- ============================================================================

/-- Slope of the line through two distinct points: (y₁ - y₂) / (x₁ - x₂). -/
def slopeAdd {p : Nat} (x₁ y₁ x₂ y₂ : Expr p) : Expr p :=
  .div (.sub y₁ y₂) (.sub x₁ x₂)

/-- Slope of the tangent at a point (a=0): 3x₁² / (2y₁). -/
def slopeDouble {p : Nat} (x₁ y₁ : Expr p) : Expr p :=
  .div (.mul (.const 3) (.mul x₁ x₁)) (.add y₁ y₁)

-- ============================================================================
-- Coordinate Formulas
-- ============================================================================

/-- x-coordinate of the sum: ℓ² - x₁ - x₂. -/
def addX {p : Nat} (x₁ x₂ ℓ : Expr p) : Expr p :=
  .sub (.sub (.mul ℓ ℓ) x₁) x₂

/-- y-coordinate of the sum: ℓ(x₁ - x₃) - y₁. -/
def addY {p : Nat} (x₁ y₁ x₃ ℓ : Expr p) : Expr p :=
  .sub (.mul ℓ (.sub x₁ x₃)) y₁

-- ============================================================================
-- Composite Point Operations
-- ============================================================================

/-- Add two distinct finite points (assumes x₁ ≠ x₂). -/
def addDistinct {p : Nat} (x₁ y₁ x₂ y₂ : Expr p) : Expr p × Expr p :=
  let ℓ := slopeAdd x₁ y₁ x₂ y₂
  let x₃ := addX x₁ x₂ ℓ
  let y₃ := addY x₁ y₁ x₃ ℓ
  (x₃, y₃)

/-- Double a finite point. -/
def double {p : Nat} (x₁ y₁ : Expr p) : Expr p × Expr p :=
  let ℓ := slopeDouble x₁ y₁
  let x₃ := addX x₁ x₁ ℓ
  let y₃ := addY x₁ y₁ x₃ ℓ
  (x₃, y₃)

-- ============================================================================
-- Affine Point Type + Operations with Infinity
-- ============================================================================

/-- Affine EC point: `none` = point at infinity, `some (x, y)` = finite point. -/
abbrev AffinePoint (p : Nat) := Option (Expr p × Expr p)

/-- Negate an affine point: (x, y) ↦ (x, -y), ∞ ↦ ∞. -/
def negPoint {p : Nat} : AffinePoint p → AffinePoint p
  | none => none
  | some (x, y) => some (x, .neg y)

/-- Add two affine points.
    Assumes distinct x-coordinates for two finite points. -/
def addAffine {p : Nat} : AffinePoint p → AffinePoint p → AffinePoint p
  | none, q => q
  | p, none => p
  | some (x₁, y₁), some (x₂, y₂) =>
    let (x₃, y₃) := addDistinct x₁ y₁ x₂ y₂
    some (x₃, y₃)

/-- Double an affine point. -/
def doubleAffine {p : Nat} : AffinePoint p → AffinePoint p
  | none => none
  | some (x₁, y₁) =>
    let (x₃, y₃) := double x₁ y₁
    some (x₃, y₃)

-- ============================================================================
-- Scalar Multiplication (double-and-add, right-to-left)
-- ============================================================================

/-- Scalar multiplication via double-and-add on `Nat.bits` (right-to-left).
    `scalarMul k P` computes `[k]P`. -/
def scalarMul {p : Nat} (k : Nat) (pt : AffinePoint p) : AffinePoint p :=
  if k = 0 then none
  else
    let bits := k.bits
    bits.foldl
      (fun (acc, running) bit =>
        let acc' := if bit then addAffine acc running else acc
        let running' := doubleAffine running
        (acc', running'))
      (none, pt) |>.1

/-- Multi-scalar multiplication (naive): Σ kᵢ · Pᵢ. -/
def msm {p : Nat} (scalars : List Nat) (points : List (AffinePoint p)) : AffinePoint p :=
  (scalars.zip points).foldl
    (fun acc (k, pt) => addAffine acc (scalarMul k pt))
    none

end LeanStableHLO.StableHLO
