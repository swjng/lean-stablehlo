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

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-!
# CubicExt: Generic Cubic Extension

R[X] / (X³ - nr), representing elements c0 + c1 · X + c2 · X².

Multiplication uses the reduction rule X³ = nr:
  c0 = a₀b₀ + nr · (a₁b₂ + a₂b₁)
  c1 = a₀b₁ + a₁b₀ + nr · a₂b₂
  c2 = a₀b₂ + a₁b₁ + a₂b₀

The `ring` tactic treats `nr` as a variable in `CommRing R`,
so all ring axioms are proved automatically.
-/

namespace LeanStableHLO.StableHLO.FieldExt

/-- Generic cubic extension R[X] / (X³ - nr). Element c0 + c1 · X + c2 · X². -/
structure CubicExt (R : Type) (nr : R) where
  c0 : R
  c1 : R
  c2 : R
  deriving DecidableEq, Repr

variable {R : Type} {nr : R}

namespace CubicExt

-- ============================================================================
-- Basic Operations
-- ============================================================================

section Ops
variable [CommRing R]

instance : Inhabited (CubicExt R nr) := ⟨⟨0, 0, 0⟩⟩

def zero : CubicExt R nr := ⟨0, 0, 0⟩
def one : CubicExt R nr := ⟨1, 0, 0⟩

def add (a b : CubicExt R nr) : CubicExt R nr :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩
def neg (a : CubicExt R nr) : CubicExt R nr := ⟨-a.c0, -a.c1, -a.c2⟩
def sub (a b : CubicExt R nr) : CubicExt R nr :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩

/-- (a₀ + a₁X + a₂X²)(b₀ + b₁X + b₂X²) with X³ = nr -/
def mul (a b : CubicExt R nr) : CubicExt R nr :=
  ⟨a.c0 * b.c0 + nr * (a.c1 * b.c2 + a.c2 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + nr * (a.c2 * b.c2),
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩

/-- Cofactor c0': a₀² - nr · a₁a₂ -/
def cofactor0 (a : CubicExt R nr) : R :=
  a.c0 * a.c0 - nr * (a.c1 * a.c2)

/-- Cofactor c1': nr · a₂² - a₀a₁ -/
def cofactor1 (a : CubicExt R nr) : R :=
  nr * (a.c2 * a.c2) - a.c0 * a.c1

/-- Cofactor c2': a₁² - a₀a₂ -/
def cofactor2 (a : CubicExt R nr) : R :=
  a.c1 * a.c1 - a.c0 * a.c2

/-- Delta (determinant): a₀ · cof0 + nr · (a₁ · cof2 + a₂ · cof1) -/
def delta (a : CubicExt R nr) : R :=
  a.c0 * a.cofactor0 + nr * (a.c1 * a.cofactor2 + a.c2 * a.cofactor1)

def natCast (n : Nat) : CubicExt R nr := ⟨↑n, 0, 0⟩
def intCast (n : Int) : CubicExt R nr := ⟨↑n, 0, 0⟩

end Ops

section InvOps
variable [Field R]

/-- Inverse: cofactor matrix / delta -/
def inv (a : CubicExt R nr) : CubicExt R nr :=
  let d := a.delta⁻¹
  ⟨a.cofactor0 * d, a.cofactor1 * d, a.cofactor2 * d⟩

end InvOps

-- ============================================================================
-- Typeclass Instances
-- ============================================================================

instance [CommRing R] : Zero (CubicExt R nr) := ⟨CubicExt.zero⟩
instance [CommRing R] : One (CubicExt R nr) := ⟨CubicExt.one⟩
instance [CommRing R] : Add (CubicExt R nr) := ⟨CubicExt.add⟩
instance [CommRing R] : Neg (CubicExt R nr) := ⟨CubicExt.neg⟩
instance [CommRing R] : Sub (CubicExt R nr) := ⟨CubicExt.sub⟩
instance [CommRing R] : Mul (CubicExt R nr) := ⟨CubicExt.mul⟩
instance [Field R] : Inv (CubicExt R nr) := ⟨CubicExt.inv⟩
instance [CommRing R] : NatCast (CubicExt R nr) := ⟨CubicExt.natCast⟩
instance [CommRing R] : IntCast (CubicExt R nr) := ⟨CubicExt.intCast⟩
instance [Field R] : Div (CubicExt R nr) := ⟨fun a b => a * b⁻¹⟩

section Npow
variable [CommRing R]

def npow : Nat → CubicExt R nr → CubicExt R nr
  | 0, _ => 1
  | n + 1, a => a * npow n a

instance : HPow (CubicExt R nr) Nat (CubicExt R nr) := ⟨fun a n => npow n a⟩
instance : Pow (CubicExt R nr) Nat := ⟨fun a n => npow n a⟩

end Npow

-- ============================================================================
-- Simp lemmas
-- ============================================================================

section Simp
variable [CommRing R]

omit [CommRing R] in
@[ext]
theorem ext {a b : CubicExt R nr} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_c0 : (0 : CubicExt R nr).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : CubicExt R nr).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : CubicExt R nr).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : CubicExt R nr).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : CubicExt R nr).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : CubicExt R nr).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : CubicExt R nr) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : CubicExt R nr) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : CubicExt R nr) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : CubicExt R nr) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : CubicExt R nr) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : CubicExt R nr) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c0 (a b : CubicExt R nr) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : CubicExt R nr) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : CubicExt R nr) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem mul_c0 (a b : CubicExt R nr) :
    (a * b).c0 = a.c0 * b.c0 + nr * (a.c1 * b.c2 + a.c2 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : CubicExt R nr) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + nr * (a.c2 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : CubicExt R nr) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := rfl
@[simp] theorem natCast_c0 (n : Nat) : (n : CubicExt R nr).c0 = ↑n := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : CubicExt R nr).c1 = 0 := rfl
@[simp] theorem natCast_c2 (n : Nat) : (n : CubicExt R nr).c2 = 0 := rfl
@[simp] theorem intCast_c0 (n : Int) : (n : CubicExt R nr).c0 = ↑n := rfl
@[simp] theorem intCast_c1 (n : Int) : (n : CubicExt R nr).c1 = 0 := rfl
@[simp] theorem intCast_c2 (n : Int) : (n : CubicExt R nr).c2 = 0 := rfl

end Simp

-- ============================================================================
-- CommRing instance
-- ============================================================================

private theorem mul_comm' [CommRing R] (a b : CubicExt R nr) :
    CubicExt.mul a b = CubicExt.mul b a := by
  ext <;> simp [CubicExt.mul] <;> ring

instance [CommRing R] : CommRing (CubicExt R nr) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm := mul_comm'
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := by ext <;> simp [Nat.cast]
  natCast_succ n := by ext <;> simp [Nat.cast]
  intCast_negSucc n := by ext <;> simp [Int.cast, Int.negSucc_eq]
  intCast_ofNat n := by ext <;> simp [Int.cast]
  npow := fun n a => npow n a
  npow_zero _ := rfl
  npow_succ n a := by
    show a * npow n a = npow n a * a
    exact mul_comm' a (npow n a)

-- ============================================================================
-- Field instance
-- ============================================================================

section FieldInst
variable [Field R]

@[simp] theorem inv_c0 (a : CubicExt R nr) : (a⁻¹).c0 = a.cofactor0 * a.delta⁻¹ := rfl
@[simp] theorem inv_c1 (a : CubicExt R nr) : (a⁻¹).c1 = a.cofactor1 * a.delta⁻¹ := rfl
@[simp] theorem inv_c2 (a : CubicExt R nr) : (a⁻¹).c2 = a.cofactor2 * a.delta⁻¹ := rfl

/-- Build a Field instance given a proof that non-zero elements have non-zero delta. -/
def instField (delta_ne_zero : ∀ (a : CubicExt R nr), a ≠ 0 → a.delta ≠ 0) :
    Field (CubicExt R nr) where
  inv := CubicExt.inv
  exists_pair_ne := ⟨0, 1, by intro h; have := congrArg CubicExt.c0 h; simp at this⟩
  mul_inv_cancel a ha := by
    have hd : a.delta ≠ 0 := delta_ne_zero a ha
    ext
    · -- c0: factor out delta⁻¹, show numerator = delta
      show a.c0 * (a.cofactor0 * a.delta⁻¹) + nr * (a.c1 * (a.cofactor2 * a.delta⁻¹)
        + a.c2 * (a.cofactor1 * a.delta⁻¹)) = 1
      calc a.c0 * (a.cofactor0 * a.delta⁻¹) + nr * (a.c1 * (a.cofactor2 * a.delta⁻¹)
              + a.c2 * (a.cofactor1 * a.delta⁻¹))
          = (a.c0 * a.cofactor0 + nr * (a.c1 * a.cofactor2
              + a.c2 * a.cofactor1)) * a.delta⁻¹ := by ring
        _ = a.delta * a.delta⁻¹ := by rfl
        _ = 1 := mul_inv_cancel₀ hd
    · -- c1: factor out delta⁻¹, show numerator = 0
      show a.c0 * (a.cofactor1 * a.delta⁻¹) + a.c1 * (a.cofactor0 * a.delta⁻¹)
        + nr * (a.c2 * (a.cofactor2 * a.delta⁻¹)) = 0
      have : a.c0 * a.cofactor1 + a.c1 * a.cofactor0
          + nr * (a.c2 * a.cofactor2) = 0 := by
        unfold cofactor0 cofactor1 cofactor2; ring
      calc a.c0 * (a.cofactor1 * a.delta⁻¹) + a.c1 * (a.cofactor0 * a.delta⁻¹)
              + nr * (a.c2 * (a.cofactor2 * a.delta⁻¹))
          = (a.c0 * a.cofactor1 + a.c1 * a.cofactor0
              + nr * (a.c2 * a.cofactor2)) * a.delta⁻¹ := by ring
        _ = 0 * a.delta⁻¹ := by rw [this]
        _ = 0 := by ring
    · -- c2: factor out delta⁻¹, show numerator = 0
      show a.c0 * (a.cofactor2 * a.delta⁻¹) + a.c1 * (a.cofactor1 * a.delta⁻¹)
        + a.c2 * (a.cofactor0 * a.delta⁻¹) = 0
      have : a.c0 * a.cofactor2 + a.c1 * a.cofactor1
          + a.c2 * a.cofactor0 = 0 := by
        unfold cofactor0 cofactor1 cofactor2; ring
      calc a.c0 * (a.cofactor2 * a.delta⁻¹) + a.c1 * (a.cofactor1 * a.delta⁻¹)
              + a.c2 * (a.cofactor0 * a.delta⁻¹)
          = (a.c0 * a.cofactor2 + a.c1 * a.cofactor1
              + a.c2 * a.cofactor0) * a.delta⁻¹ := by ring
        _ = 0 * a.delta⁻¹ := by rw [this]
        _ = 0 := by ring
  inv_zero := by
    ext <;> simp [inv, cofactor0, cofactor1, cofactor2, delta]
  div_eq_mul_inv _ _ := rfl
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

end FieldInst

end CubicExt

end LeanStableHLO.StableHLO.FieldExt
