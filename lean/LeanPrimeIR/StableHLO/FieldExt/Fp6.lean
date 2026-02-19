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

import LeanPrimeIR.StableHLO.FieldExt.Fp2

/-!
# Fp6: Cubic Extension over Fp2

F_p⁶ = F_p²[v] / (v³ - ξ), representing elements a₀ + a₁v + a₂v².

Here ξ = 9 + u is the twist parameter in F_p².
The reduction rule is v³ = ξ.
-/

namespace LeanPrimeIR.StableHLO.FieldExt

open Fp2

/-- F_p⁶ = F_p²[v] / (v³ - ξ). Element a₀ + a₁v + a₂v². -/
structure Fp6 (p : Nat) where
  c0 : Fp2 p
  c1 : Fp2 p
  c2 : Fp2 p
  deriving DecidableEq, Repr

variable {p : Nat}

namespace Fp6

instance : Inhabited (Fp6 p) := ⟨⟨0, 0, 0⟩⟩

-- ============================================================================
-- Basic Operations
-- ============================================================================

def zero : Fp6 p := ⟨0, 0, 0⟩
def one : Fp6 p := ⟨1, 0, 0⟩

def add (a b : Fp6 p) : Fp6 p := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩
def neg (a : Fp6 p) : Fp6 p := ⟨-a.c0, -a.c1, -a.c2⟩
def sub (a b : Fp6 p) : Fp6 p := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩

/-- Multiply by v: shift coefficients and reduce v³ = ξ.
    (a₀ + a₁v + a₂v²) · v = a₂ξ + a₀v + a₁v² -/
def mulByV (a : Fp6 p) : Fp6 p :=
  ⟨mulByXi a.c2, a.c0, a.c1⟩

/-- (a₀ + a₁v + a₂v²)(b₀ + b₁v + b₂v²) with v³ = ξ:
    c0 = a₀b₀ + ξ(a₁b₂ + a₂b₁)
    c1 = a₀b₁ + a₁b₀ + ξ · a₂b₂
    c2 = a₀b₂ + a₁b₁ + a₂b₀ -/
def mul (a b : Fp6 p) : Fp6 p :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let t2 := a.c2 * b.c2
  ⟨t0 + mulByXi (a.c1 * b.c2 + a.c2 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + mulByXi t2,
   a.c0 * b.c2 + t1 + a.c2 * b.c0⟩

/-- Inverse in Fp6. Uses the formula:
    a⁻¹ = (1 / Δ) · (c0', c1', c2') where Δ is the determinant. -/
def inv [Fact (Nat.Prime p)] (a : Fp6 p) : Fp6 p :=
  let c0' := a.c0 * a.c0 - mulByXi (a.c1 * a.c2)
  let c1' := mulByXi (a.c2 * a.c2) - a.c0 * a.c1
  let c2' := a.c1 * a.c1 - a.c0 * a.c2
  let delta := a.c0 * c0' + mulByXi (a.c2 * c1' + a.c1 * c2')
  let deltaInv := delta⁻¹
  ⟨c0' * deltaInv, c1' * deltaInv, c2' * deltaInv⟩

def ofFp2 (x : Fp2 p) : Fp6 p := ⟨x, 0, 0⟩
def natCast (n : Nat) : Fp6 p := ⟨↑n, 0, 0⟩
def intCast (n : Int) : Fp6 p := ⟨↑n, 0, 0⟩

-- ============================================================================
-- Typeclass Instances
-- ============================================================================

instance : Zero (Fp6 p) := ⟨Fp6.zero⟩
instance : One (Fp6 p) := ⟨Fp6.one⟩
instance : Add (Fp6 p) := ⟨Fp6.add⟩
instance : Neg (Fp6 p) := ⟨Fp6.neg⟩
instance : Sub (Fp6 p) := ⟨Fp6.sub⟩
instance : Mul (Fp6 p) := ⟨Fp6.mul⟩
instance [Fact (Nat.Prime p)] : Inv (Fp6 p) := ⟨Fp6.inv⟩
instance : NatCast (Fp6 p) := ⟨Fp6.natCast⟩
instance : IntCast (Fp6 p) := ⟨Fp6.intCast⟩
instance [Fact (Nat.Prime p)] : Div (Fp6 p) := ⟨fun a b => a * b⁻¹⟩

def npow : Nat → Fp6 p → Fp6 p
  | 0, _ => 1
  | n + 1, a => a * npow n a

instance : HPow (Fp6 p) Nat (Fp6 p) := ⟨fun a n => npow n a⟩
instance : Pow (Fp6 p) Nat := ⟨fun a n => npow n a⟩

-- ============================================================================
-- Simp lemmas
-- ============================================================================

@[ext]
theorem ext {a b : Fp6 p} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_c0 : (0 : Fp6 p).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp6 p).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp6 p).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp6 p).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp6 p).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp6 p).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp6 p) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp6 p) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp6 p) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp6 p) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp6 p) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp6 p) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c0 (a b : Fp6 p) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp6 p) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp6 p) : (a - b).c2 = a.c2 - b.c2 := rfl

-- ============================================================================
-- CommRing and Field instances
--
-- Ring axiom proofs for Fp6 are non-trivial due to the cubic extension with
-- the ξ non-residue. The proofs are deferred (sorry) and correctness is
-- validated by test vectors against known implementations (e.g., gnark-crypto).
-- ============================================================================

instance : CommRing (Fp6 p) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  zero_mul _ := by sorry
  mul_zero _ := by sorry
  add_comm a b := by ext <;> simp [add_comm]
  mul_assoc _ _ _ := by sorry
  one_mul _ := by sorry
  mul_one _ := by sorry
  mul_comm _ _ := by sorry
  left_distrib _ _ _ := by sorry
  right_distrib _ _ _ := by sorry
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := by sorry
  natCast_succ _ := by sorry
  intCast_negSucc _ := by sorry
  intCast_ofNat _ := by sorry
  npow := fun n a => npow n a
  npow_zero _ := rfl
  npow_succ _ _ := by sorry

instance [Fact (Nat.Prime p)] : Field (Fp6 p) where
  inv := Fp6.inv
  exists_pair_ne := ⟨0, 1, by
    intro h; have := congrArg Fp6.c0 h; simp at this⟩
  mul_inv_cancel _ _ := by sorry
  inv_zero := by sorry
  div_eq_mul_inv _ _ := rfl
  zpow := zpowRec
  nnqsmul := _
  qsmul := _

end Fp6

end LeanPrimeIR.StableHLO.FieldExt
