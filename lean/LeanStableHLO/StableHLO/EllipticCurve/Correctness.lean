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

import LeanStableHLO.StableHLO.EllipticCurve
import LeanStableHLO.StableHLO.BN254
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# EC Operations Correctness

Three-level proof structure:
1. **eval lemmas**: `Expr.div` evaluator is definitionally correct (`rfl`)
2. **AST eval = spec**: composite operation evaluators unfold correctly (`rfl`)
3. **Spec = Mathlib**: our coordinate formulas match Mathlib's
   `WeierstrassCurve.Affine` formulas for short Weierstrass (a₁=a₂=a₃=a₄=0)
-/

namespace LeanStableHLO.StableHLO

-- ============================================================================
-- Level 1: Expr.div eval lemma
-- ============================================================================

@[simp]
theorem eval_div {p : Nat} [NeZero p] (a b : Expr p) :
    (Expr.div a b).eval = a.eval * b.eval⁻¹ := rfl

-- ============================================================================
-- Level 2: Component eval lemmas (definitional)
-- ============================================================================

@[simp]
theorem slopeAdd_eval {p : Nat} [NeZero p] (x₁ y₁ x₂ y₂ : Expr p) :
    (slopeAdd x₁ y₁ x₂ y₂).eval =
    (y₁.eval - y₂.eval) * (x₁.eval - x₂.eval)⁻¹ := rfl

@[simp]
theorem slopeDouble_eval {p : Nat} [NeZero p] (x₁ y₁ : Expr p) :
    (slopeDouble x₁ y₁).eval =
    (3 : ZMod p) * (x₁.eval * x₁.eval) * (y₁.eval + y₁.eval)⁻¹ := rfl

@[simp]
theorem addX_eval {p : Nat} [NeZero p] (x₁ x₂ ℓ : Expr p) :
    (LeanStableHLO.StableHLO.addX x₁ x₂ ℓ).eval =
    ℓ.eval * ℓ.eval - x₁.eval - x₂.eval := rfl

@[simp]
theorem addY_eval {p : Nat} [NeZero p] (x₁ y₁ x₃ ℓ : Expr p) :
    (LeanStableHLO.StableHLO.addY x₁ y₁ x₃ ℓ).eval =
    ℓ.eval * (x₁.eval - x₃.eval) - y₁.eval := rfl

theorem addDistinct_eval {p : Nat} [NeZero p] (x₁ y₁ x₂ y₂ : Expr p) :
    let ℓ := (y₁.eval - y₂.eval) * (x₁.eval - x₂.eval)⁻¹
    (addDistinct x₁ y₁ x₂ y₂).1.eval = ℓ * ℓ - x₁.eval - x₂.eval ∧
    (addDistinct x₁ y₁ x₂ y₂).2.eval =
      ℓ * (x₁.eval - (ℓ * ℓ - x₁.eval - x₂.eval)) - y₁.eval :=
  ⟨rfl, rfl⟩

theorem double_eval {p : Nat} [NeZero p] (x₁ y₁ : Expr p) :
    let ℓ := (3 : ZMod p) * (x₁.eval * x₁.eval) * (y₁.eval + y₁.eval)⁻¹
    (double x₁ y₁).1.eval = ℓ * ℓ - x₁.eval - x₁.eval ∧
    (double x₁ y₁).2.eval =
      ℓ * (x₁.eval - (ℓ * ℓ - x₁.eval - x₁.eval)) - y₁.eval :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Level 3: Mathlib Bridge (short Weierstrass, a₁=a₂=a₃=a₄=0)
-- ============================================================================

section MathlibBridge

variable {p : Nat} [Fact (Nat.Prime p)]

-- NeZero from primality (needed for Expr.eval)
instance instNeZeroOfPrime : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩

open WeierstrassCurve.Affine in
/-- Secant slope matches Mathlib's `slope` when x₁ ≠ x₂. -/
theorem slopeAdd_eq_slope
    (W : WeierstrassCurve (ZMod p))
    (x₁ y₁ x₂ y₂ : Expr p)
    (hne : x₁.eval ≠ x₂.eval) :
    (slopeAdd x₁ y₁ x₂ y₂).eval =
    slope W x₁.eval x₂.eval y₁.eval y₂.eval := by
  rw [slopeAdd_eval, slope_of_X_ne hne, div_eq_mul_inv]

open WeierstrassCurve.Affine in
/-- Tangent slope matches Mathlib's `slope` for doubling when y ≠ negY. -/
theorem slopeDouble_eq_slope
    (W : WeierstrassCurve (ZMod p))
    (hW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x₁ y₁ : Expr p)
    (hny : y₁.eval ≠ WeierstrassCurve.Affine.negY W x₁.eval y₁.eval) :
    (slopeDouble x₁ y₁).eval =
    slope W x₁.eval x₁.eval y₁.eval y₁.eval := by
  rw [slopeDouble_eval, slope_of_Y_ne rfl hny]
  simp only [WeierstrassCurve.Affine.negY, hW.1, hW.2.2.1, hW.2.1, hW.2.2.2,
    mul_zero, zero_mul, sub_zero, add_zero]
  rw [div_eq_mul_inv]
  congr 1
  · ring
  · congr 1; ring

/-- Our `addX` formula matches Mathlib's for short Weierstrass. -/
theorem addX_eq_mathlib
    (W : WeierstrassCurve (ZMod p))
    (hW : W.a₁ = 0 ∧ W.a₂ = 0)
    (x₁ x₂ ℓ : Expr p) :
    (LeanStableHLO.StableHLO.addX x₁ x₂ ℓ).eval =
    WeierstrassCurve.Affine.addX W x₁.eval x₂.eval ℓ.eval := by
  simp only [addX_eval, WeierstrassCurve.Affine.addX, hW.1, hW.2]
  ring

/-- Our `addY` formula matches Mathlib's for short Weierstrass. -/
theorem addY_eq_mathlib
    (W : WeierstrassCurve (ZMod p))
    (hW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (x₁ y₁ x₂ ℓ : Expr p) :
    (LeanStableHLO.StableHLO.addY x₁ y₁
      (LeanStableHLO.StableHLO.addX x₁ x₂ ℓ) ℓ).eval =
    WeierstrassCurve.Affine.addY W x₁.eval x₂.eval y₁.eval ℓ.eval := by
  simp only [addY_eval, addX_eval,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    hW.1, hW.2.1, hW.2.2]
  ring

open WeierstrassCurve.Affine in
/-- Full `addDistinct` matches Mathlib's point addition formulas
    for short Weierstrass when x₁ ≠ x₂. -/
theorem addDistinct_matches_mathlib
    (W : WeierstrassCurve (ZMod p))
    (hW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x₁ y₁ x₂ y₂ : Expr p)
    (hne : x₁.eval ≠ x₂.eval) :
    (addDistinct x₁ y₁ x₂ y₂).1.eval =
      WeierstrassCurve.Affine.addX W x₁.eval x₂.eval
        (slope W x₁.eval x₂.eval y₁.eval y₂.eval) ∧
    (addDistinct x₁ y₁ x₂ y₂).2.eval =
      WeierstrassCurve.Affine.addY W x₁.eval x₂.eval y₁.eval
        (slope W x₁.eval x₂.eval y₁.eval y₂.eval) := by
  -- Compose component bridge proofs (avoids expensive simp+ring)
  have hsl := slopeAdd_eq_slope W x₁ y₁ x₂ y₂ hne
  have hax := addX_eq_mathlib W ⟨hW.1, hW.2.1⟩ x₁ x₂ (slopeAdd x₁ y₁ x₂ y₂)
  have hay := addY_eq_mathlib W ⟨hW.1, hW.2.1, hW.2.2.1⟩ x₁ y₁ x₂ (slopeAdd x₁ y₁ x₂ y₂)
  refine ⟨?_, ?_⟩
  · show (LeanStableHLO.StableHLO.addX x₁ x₂ (slopeAdd x₁ y₁ x₂ y₂)).eval = _
    rw [hax, hsl]
  · show (LeanStableHLO.StableHLO.addY x₁ y₁
      (LeanStableHLO.StableHLO.addX x₁ x₂ (slopeAdd x₁ y₁ x₂ y₂))
      (slopeAdd x₁ y₁ x₂ y₂)).eval = _
    rw [hay, hsl]

open WeierstrassCurve.Affine in
/-- Full `double` matches Mathlib's point doubling formulas
    for short Weierstrass when y ≠ negY. -/
theorem double_matches_mathlib
    (W : WeierstrassCurve (ZMod p))
    (hW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x₁ y₁ : Expr p)
    (hny : y₁.eval ≠ WeierstrassCurve.Affine.negY W x₁.eval y₁.eval) :
    (double x₁ y₁).1.eval =
      WeierstrassCurve.Affine.addX W x₁.eval x₁.eval
        (slope W x₁.eval x₁.eval y₁.eval y₁.eval) ∧
    (double x₁ y₁).2.eval =
      WeierstrassCurve.Affine.addY W x₁.eval x₁.eval y₁.eval
        (slope W x₁.eval x₁.eval y₁.eval y₁.eval) := by
  -- Compose component bridge proofs
  have hsl := slopeDouble_eq_slope W hW x₁ y₁ hny
  have hax := addX_eq_mathlib W ⟨hW.1, hW.2.1⟩ x₁ x₁ (slopeDouble x₁ y₁)
  have hay := addY_eq_mathlib W ⟨hW.1, hW.2.1, hW.2.2.1⟩ x₁ y₁ x₁ (slopeDouble x₁ y₁)
  refine ⟨?_, ?_⟩
  · -- x-coordinate: expose reduced form for rw
    show (LeanStableHLO.StableHLO.addX x₁ x₁ (slopeDouble x₁ y₁)).eval = _
    rw [hax, hsl]
  · -- y-coordinate: expose reduced form for rw
    show (LeanStableHLO.StableHLO.addY x₁ y₁
      (LeanStableHLO.StableHLO.addX x₁ x₁ (slopeDouble x₁ y₁))
      (slopeDouble x₁ y₁)).eval = _
    rw [hay, hsl]

end MathlibBridge

end LeanStableHLO.StableHLO
