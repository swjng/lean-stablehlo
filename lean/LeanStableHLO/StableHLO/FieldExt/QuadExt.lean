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
# QuadExt: Generic Quadratic Extension

R[X] / (X² - nr), representing elements c0 + c1 · X.

Multiplication: (a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + nr · a₁b₁) + (a₀b₁ + a₁b₀)X
Norm: a₀² - nr · a₁²
Inverse: (a₀ / norm, -a₁ / norm)

The `ring` tactic treats `nr` as a variable in `CommRing R`,
so all ring axioms are proved automatically.
-/

namespace LeanStableHLO.StableHLO.FieldExt

/-- Generic quadratic extension R[X] / (X² - nr). Element c0 + c1 · X. -/
structure QuadExt (R : Type) (nr : R) where
  c0 : R
  c1 : R
  deriving DecidableEq, Repr

variable {R : Type} {nr : R}

namespace QuadExt

-- ============================================================================
-- Basic Operations
-- ============================================================================

section Ops
variable [CommRing R]

instance : Inhabited (QuadExt R nr) := ⟨⟨0, 0⟩⟩

def zero : QuadExt R nr := ⟨0, 0⟩
def one : QuadExt R nr := ⟨1, 0⟩

def add (a b : QuadExt R nr) : QuadExt R nr := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def neg (a : QuadExt R nr) : QuadExt R nr := ⟨-a.c0, -a.c1⟩
def sub (a b : QuadExt R nr) : QuadExt R nr := ⟨a.c0 - b.c0, a.c1 - b.c1⟩

/-- (a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + nr · a₁b₁) + (a₀b₁ + a₁b₀)X -/
def mul (a b : QuadExt R nr) : QuadExt R nr :=
  ⟨a.c0 * b.c0 + nr * (a.c1 * b.c1), a.c0 * b.c1 + a.c1 * b.c0⟩

/-- Norm: a₀² - nr · a₁² -/
def norm (a : QuadExt R nr) : R := a.c0 * a.c0 - nr * (a.c1 * a.c1)

/-- Conjugate: (a₀, -a₁) -/
def conj (a : QuadExt R nr) : QuadExt R nr := ⟨a.c0, -a.c1⟩

def natCast (n : Nat) : QuadExt R nr := ⟨↑n, 0⟩
def intCast (n : Int) : QuadExt R nr := ⟨↑n, 0⟩

end Ops

section InvOps
variable [Field R]

/-- Inverse: conj(a) / norm(a) -/
def inv (a : QuadExt R nr) : QuadExt R nr :=
  let t := a.norm⁻¹
  ⟨a.c0 * t, -a.c1 * t⟩

end InvOps

-- ============================================================================
-- Typeclass Instances
-- ============================================================================

instance [CommRing R] : Zero (QuadExt R nr) := ⟨QuadExt.zero⟩
instance [CommRing R] : One (QuadExt R nr) := ⟨QuadExt.one⟩
instance [CommRing R] : Add (QuadExt R nr) := ⟨QuadExt.add⟩
instance [CommRing R] : Neg (QuadExt R nr) := ⟨QuadExt.neg⟩
instance [CommRing R] : Sub (QuadExt R nr) := ⟨QuadExt.sub⟩
instance [CommRing R] : Mul (QuadExt R nr) := ⟨QuadExt.mul⟩
instance [Field R] : Inv (QuadExt R nr) := ⟨QuadExt.inv⟩
instance [CommRing R] : NatCast (QuadExt R nr) := ⟨QuadExt.natCast⟩
instance [CommRing R] : IntCast (QuadExt R nr) := ⟨QuadExt.intCast⟩
instance [Field R] : Div (QuadExt R nr) := ⟨fun a b => a * b⁻¹⟩

section Npow
variable [CommRing R]

def npow : Nat → QuadExt R nr → QuadExt R nr
  | 0, _ => 1
  | n + 1, a => a * npow n a

instance : HPow (QuadExt R nr) Nat (QuadExt R nr) := ⟨fun a n => npow n a⟩
instance : Pow (QuadExt R nr) Nat := ⟨fun a n => npow n a⟩

end Npow

-- ============================================================================
-- Simp lemmas
-- ============================================================================

section Simp
variable [CommRing R]

omit [CommRing R] in
@[ext]
theorem ext {a b : QuadExt R nr} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_c0 : (0 : QuadExt R nr).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : QuadExt R nr).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : QuadExt R nr).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : QuadExt R nr).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : QuadExt R nr) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : QuadExt R nr) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem neg_c0 (a : QuadExt R nr) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : QuadExt R nr) : (-a).c1 = -a.c1 := rfl
@[simp] theorem sub_c0 (a b : QuadExt R nr) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : QuadExt R nr) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem mul_c0 (a b : QuadExt R nr) :
    (a * b).c0 = a.c0 * b.c0 + nr * (a.c1 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : QuadExt R nr) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
@[simp] theorem natCast_c0 (n : Nat) : (n : QuadExt R nr).c0 = ↑n := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : QuadExt R nr).c1 = 0 := rfl
@[simp] theorem intCast_c0 (n : Int) : (n : QuadExt R nr).c0 = ↑n := rfl
@[simp] theorem intCast_c1 (n : Int) : (n : QuadExt R nr).c1 = 0 := rfl

end Simp

-- ============================================================================
-- CommRing instance
-- ============================================================================

private theorem mul_comm' [CommRing R] (a b : QuadExt R nr) :
    QuadExt.mul a b = QuadExt.mul b a := by
  ext <;> simp [QuadExt.mul] <;> ring

instance [CommRing R] : CommRing (QuadExt R nr) where
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

@[simp] theorem inv_c0 (a : QuadExt R nr) : (a⁻¹).c0 = a.c0 * a.norm⁻¹ := rfl
@[simp] theorem inv_c1 (a : QuadExt R nr) : (a⁻¹).c1 = -a.c1 * a.norm⁻¹ := rfl

/-- Build a Field instance given a proof that non-zero elements have non-zero norm. -/
def instField (norm_ne_zero : ∀ (a : QuadExt R nr), a ≠ 0 → a.norm ≠ 0) :
    Field (QuadExt R nr) where
  inv := QuadExt.inv
  exists_pair_ne := ⟨0, 1, by intro h; have := congrArg QuadExt.c0 h; simp at this⟩
  mul_inv_cancel a ha := by
    have hn : a.norm ≠ 0 := norm_ne_zero a ha
    ext
    · -- c0: (a₀² + nr · a₁²) · norm⁻¹ = norm · norm⁻¹ = 1
      change a.c0 * (a.c0 * a.norm⁻¹) + nr * (a.c1 * (-a.c1 * a.norm⁻¹)) = 1
      calc a.c0 * (a.c0 * a.norm⁻¹) + nr * (a.c1 * (-a.c1 * a.norm⁻¹))
          = (a.c0 * a.c0 - nr * (a.c1 * a.c1)) * a.norm⁻¹ := by ring
        _ = a.norm * a.norm⁻¹ := by rfl
        _ = 1 := mul_inv_cancel₀ hn
    · -- c1: (a₀ · (-a₁) + a₁ · a₀) · norm⁻¹ = 0
      change a.c0 * (-a.c1 * a.norm⁻¹) + a.c1 * (a.c0 * a.norm⁻¹) = 0
      ring
  inv_zero := by ext <;> simp [inv, norm]
  div_eq_mul_inv _ _ := rfl
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

end FieldInst

end QuadExt

end LeanStableHLO.StableHLO.FieldExt
