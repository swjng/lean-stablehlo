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

import LeanStableHLO.StableHLO.BN254
import Mathlib.Algebra.Field.ZMod

/-!
# Fp2: Quadratic Extension Field

F_p² = F_p[u] / (u² + 1), representing elements a₀ + a₁u.

This is a concrete, computable implementation using product types
instead of Mathlib's `AdjoinRoot`.

## BN254 Specifics

For BN254, p ≡ 3 (mod 4), so -1 is a quadratic non-residue in F_p
and u² + 1 is irreducible, making F_p² a valid field extension.
-/

namespace LeanStableHLO.StableHLO.FieldExt

/-- F_p² = F_p[u] / (u² + 1). Element a₀ + a₁u. -/
structure Fp2 (p : Nat) where
  c0 : ZMod p
  c1 : ZMod p
  deriving DecidableEq, Repr

variable {p : Nat}

namespace Fp2

instance : Inhabited (Fp2 p) := ⟨⟨0, 0⟩⟩

-- ============================================================================
-- Basic Operations
-- ============================================================================

def zero : Fp2 p := ⟨0, 0⟩
def one : Fp2 p := ⟨1, 0⟩

def add (a b : Fp2 p) : Fp2 p := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def neg (a : Fp2 p) : Fp2 p := ⟨-a.c0, -a.c1⟩
def sub (a b : Fp2 p) : Fp2 p := ⟨a.c0 - b.c0, a.c1 - b.c1⟩

/-- (a₀ + a₁u)(b₀ + b₁u) = (a₀b₀ - a₁b₁) + (a₀b₁ + a₁b₀)u -/
def mul (a b : Fp2 p) : Fp2 p :=
  ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩

/-- Conjugate: a₀ - a₁u. -/
def conj (a : Fp2 p) : Fp2 p := ⟨a.c0, -a.c1⟩

/-- Norm: a₀² + a₁² (= a · conj(a) in c0 component). -/
def norm (a : Fp2 p) : ZMod p := a.c0 * a.c0 + a.c1 * a.c1

/-- Inverse: conj(a) / norm(a) = (a₀ - a₁u) / (a₀² + a₁²). -/
def inv (a : Fp2 p) : Fp2 p :=
  let t := a.norm⁻¹
  ⟨a.c0 * t, -a.c1 * t⟩

def ofZMod (x : ZMod p) : Fp2 p := ⟨x, 0⟩
def natCast (n : Nat) : Fp2 p := ⟨↑n, 0⟩
def intCast (n : Int) : Fp2 p := ⟨↑n, 0⟩

-- ============================================================================
-- Typeclass Instances (basic)
-- ============================================================================

instance : Zero (Fp2 p) := ⟨Fp2.zero⟩
instance : One (Fp2 p) := ⟨Fp2.one⟩
instance : Add (Fp2 p) := ⟨Fp2.add⟩
instance : Neg (Fp2 p) := ⟨Fp2.neg⟩
instance : Sub (Fp2 p) := ⟨Fp2.sub⟩
instance : Mul (Fp2 p) := ⟨Fp2.mul⟩
instance : Inv (Fp2 p) := ⟨Fp2.inv⟩
instance : NatCast (Fp2 p) := ⟨Fp2.natCast⟩
instance : IntCast (Fp2 p) := ⟨Fp2.intCast⟩
instance : Div (Fp2 p) := ⟨fun a b => a * b⁻¹⟩

/-- Power by natural number (naive, linear; used by the `Monoid` instance). -/
def npow : Nat → Fp2 p → Fp2 p
  | 0, _ => 1
  | n + 1, a => a * npow n a

/-- Power by natural number via repeated squaring (binary; evaluatable for
    large exponents, unlike the linear `npow`). -/
def powNat (a : Fp2 p) (n : Nat) : Fp2 p :=
  if n = 0 then 1
  else
    (n.bits).foldl
      (fun (acc, running) bit =>
        (if bit then acc * running else acc, running * running))
      (1, a) |>.1

instance : HPow (Fp2 p) Nat (Fp2 p) := ⟨fun a n => npow n a⟩
instance : Pow (Fp2 p) Nat := ⟨fun a n => npow n a⟩

-- ============================================================================
-- Simp lemmas for component extraction
-- ============================================================================

@[ext]
theorem ext {a b : Fp2 p} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_c0 : (0 : Fp2 p).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2 p).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2 p).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2 p).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp2 p) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2 p) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2 p) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2 p) : (-a).c1 = -a.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2 p) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2 p) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2 p) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2 p) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
@[simp] theorem inv_c0 (a : Fp2 p) : (a⁻¹).c0 = a.c0 * a.norm⁻¹ := rfl
@[simp] theorem inv_c1 (a : Fp2 p) : (a⁻¹).c1 = -a.c1 * a.norm⁻¹ := rfl
@[simp] theorem natCast_c0 (n : Nat) : (n : Fp2 p).c0 = ↑n := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : Fp2 p).c1 = 0 := rfl
@[simp] theorem intCast_c0 (n : Int) : (n : Fp2 p).c0 = ↑n := rfl
@[simp] theorem intCast_c1 (n : Int) : (n : Fp2 p).c1 = 0 := rfl

-- ============================================================================
-- CommRing instance
-- ============================================================================

private theorem mul_comm' (a b : Fp2 p) : Fp2.mul a b = Fp2.mul b a := by
  ext <;> simp [Fp2.mul] <;> ring

instance : CommRing (Fp2 p) where
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

/-- For BN254's base prime (p ≡ 3 mod 4), -1 is a quadratic non-residue,
    so a₀² + a₁² = 0 implies a₀ = a₁ = 0. This ensures Fp2 is a field.
    Restricted to basePrime to avoid unsound generalization over all primes. -/
axiom norm_ne_zero_of_ne_zero (a : Fp2 BN254.basePrime) (ha : a ≠ 0) :
    a.norm ≠ 0

private theorem norm_mul_inv (a : Fp2 BN254.basePrime) (ha : a ≠ 0) :
    a.norm * a.norm⁻¹ = 1 := by
  exact mul_inv_cancel₀ (norm_ne_zero_of_ne_zero a ha)

instance : Field (Fp2 BN254.basePrime) where
  inv := Fp2.inv
  exists_pair_ne := ⟨0, 1, by intro h; have := congrArg Fp2.c0 h; simp at this⟩
  mul_inv_cancel a ha := by
    ext
    · -- (a * a⁻¹).c0 = a.c0² · t + a.c1² · t = norm · t = 1
      change a.c0 * (a.c0 * a.norm⁻¹) - a.c1 * (-a.c1 * a.norm⁻¹) = 1
      calc a.c0 * (a.c0 * a.norm⁻¹) - a.c1 * (-a.c1 * a.norm⁻¹)
          = (a.c0 * a.c0 + a.c1 * a.c1) * a.norm⁻¹ := by ring
        _ = a.norm * a.norm⁻¹ := by rfl
        _ = 1 := norm_mul_inv a ha
    · change a.c0 * (-a.c1 * a.norm⁻¹) + a.c1 * (a.c0 * a.norm⁻¹) = 0
      ring
  inv_zero := by ext <;> simp [inv, norm]
  div_eq_mul_inv _ _ := rfl
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

-- ============================================================================
-- BN254-specific constants
-- ============================================================================

open BN254 in
/-- Twist parameter ξ = 9 + u ∈ F_p². -/
def xi : Fp2 basePrime := ⟨9, 1⟩

/-- Multiply by the non-residue ξ = 9 + u.
    (a₀ + a₁u)(9 + u) = (9a₀ - a₁) + (a₀ + 9a₁)u -/
def mulByXi (a : Fp2 p) : Fp2 p :=
  ⟨9 * a.c0 - a.c1, a.c0 + 9 * a.c1⟩

@[simp] theorem mulByXi_c0 (a : Fp2 p) : (mulByXi a).c0 = 9 * a.c0 - a.c1 := rfl
@[simp] theorem mulByXi_c1 (a : Fp2 p) : (mulByXi a).c1 = a.c0 + 9 * a.c1 := rfl

end Fp2

end LeanStableHLO.StableHLO.FieldExt
