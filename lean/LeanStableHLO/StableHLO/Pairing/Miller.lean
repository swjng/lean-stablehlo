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

import LeanStableHLO.StableHLO.FieldExt.Fp12
import LeanStableHLO.StableHLO.Pairing.G2

/-!
# Miller Loop for BN254 Optimal Ate Pairing

Implements the Miller loop for the optimal Ate pairing on BN254.
The loop iterates over bits of |6x + 2| where x is the BN parameter,
computing line function evaluations and accumulating the result in Fp12.

## Algorithm

For P ∈ G₁ (over Fp) and Q ∈ G₂ (over Fp2), the Miller loop computes:

  f = ∏ᵢ ℓ_T,T(P) · [ℓ_T,±Q(P)]^(sᵢ)

where sᵢ are the signed bits of 6x + 2 in NAF representation.

## Line Functions

Line functions evaluate the tangent/secant line at a G₁ point P = (xP, yP):
- Tangent at T = (xT, yT): ℓ(P) = yP - λ·xP - (yT - λ·xT) where λ = 3xT²/2yT
- Secant through T, Q: ℓ(P) = yP - λ·xP - (yT - λ·xT) where λ = (yQ-yT)/(xQ-xT)

Results are sparse Fp12 elements (most coefficients are zero).
-/

namespace LeanStableHLO.StableHLO.ConcretePairing

open FieldExt BN254

-- ============================================================================
-- BN254 Parameters
-- ============================================================================

/-- BN parameter x (also called u in some references). -/
def bnX : Nat := 4965661367192848881

/-- |6x + 2| = 29793968203157093288. This is the Miller loop iteration count. -/
def ateLoopCount : Nat := 29793968203157093288

/-- NAF (Non-Adjacent Form) representation of 6x + 2.
    Coefficients from MSB to LSB. Each entry ∈ {-1, 0, 1}.
    The first (MSB) entry is always 1 and is used as the starting point. -/
def ateLoopNAF : List Int :=
  [1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0,
   1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
   1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0,
   -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 1, 0,
   0, 0]

/-- The NAF list (MSB-first signed binary) encodes exactly `6x + 2`.
    Machine-checked guard against regression of the loop count. -/
example : ateLoopNAF.foldl (fun acc d => acc * 2 + d) 0 = (6 * (bnX : Int) + 2) := by
  native_decide

-- ============================================================================
-- Sparse Fp12 from Line Evaluation
-- ============================================================================

/-- Embed an Fp2 element into Fp12 at the c0.c0 position. -/
def fp2ToFp12_00 (a : Fp2 basePrime) : Fp12 basePrime :=
  ⟨⟨a, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- Embed a sparse line evaluation into `Fp12`.

    With the tower `Fp12 = Fp6[w]/(w²-v)`, `Fp6 = Fp2[v]/(v³-ξ)` (basis
    `{1, v, v², w, vw, v²w}`) and the D-type twist map `(x',y') ↦ (x'w², y'w³)`,
    the Miller line `ℓ(P) = y_P - λ_E x_P + (λ_E X_T - Y_T)` evaluates to
    `y_P · 1 + (-λ x_P) · w + (λ x_T - y_T) · vw` (using `w³ = vw`).

    The arguments keep their original names from the line steps:
    `a00 = λx_T - y_T` (→ `vw` slot), `a01 = -λx_P` (→ `w` slot),
    `a10 = y_P` (→ `1` slot). -/
def mkLineFp12 (a00 a01 a10 : Fp2 basePrime) : Fp12 basePrime :=
  ⟨⟨a10, 0, 0⟩, ⟨a01, a00, 0⟩⟩

-- ============================================================================
-- Line Function: Doubling Step
-- ============================================================================

/-- Doubling step: compute tangent line at T and double T.
    Returns (new T, line evaluation at P).
    T = (xT, yT) ∈ G₂, P = (xP, yP) ∈ G₁.

    Tangent slope: λ = 3xT² / 2yT
    Line: ℓ(P) = -λ·xP + yP + (λ·xT - yT)  (evaluated sparsely)
    New T: xT' = λ² - 2xT, yT' = λ(xT - xT') - yT -/
def doublingStep (T : Fp2 basePrime × Fp2 basePrime)
    (xP yP : ZMod basePrime) :
    (Fp2 basePrime × Fp2 basePrime) × Fp12 basePrime :=
  let (xT, yT) := T
  let lambda := (3 : Fp2 basePrime) * xT * xT / ((2 : Fp2 basePrime) * yT)
  let xT' := lambda * lambda - (2 : Fp2 basePrime) * xT
  let yT' := lambda * (xT - xT') - yT
  -- Line evaluation at P, sparse in the {1, w, vw} slots (see `mkLineFp12`):
  --   ell_vv  = λ·xT - yT  → vw coefficient
  --   ell_vw  = -λ·xP      → w  coefficient
  --   ell_vvw = yP         → 1  coefficient
  let ell_vv := lambda * xT - yT
  let ell_vw : Fp2 basePrime := ⟨-xP, 0⟩ * lambda
  let ell_vvw : Fp2 basePrime := ⟨yP, 0⟩
  ((xT', yT'), mkLineFp12 ell_vv ell_vw ell_vvw)

-- ============================================================================
-- Line Function: Addition Step
-- ============================================================================

/-- Addition step: compute secant line through T and Q, then add.
    Returns (new T, line evaluation at P).
    T = (xT, yT), Q = (xQ, yQ) ∈ G₂, P = (xP, yP) ∈ G₁. -/
def additionStep (T : Fp2 basePrime × Fp2 basePrime)
    (Q : Fp2 basePrime × Fp2 basePrime)
    (xP yP : ZMod basePrime) :
    (Fp2 basePrime × Fp2 basePrime) × Fp12 basePrime :=
  let (xT, yT) := T
  let (xQ, yQ) := Q
  let lambda := (yQ - yT) / (xQ - xT)
  let xT' := lambda * lambda - xT - xQ
  let yT' := lambda * (xT - xT') - yT
  let ell_vv := lambda * xT - yT
  let ell_vw : Fp2 basePrime := ⟨-xP, 0⟩ * lambda
  let ell_vvw : Fp2 basePrime := ⟨yP, 0⟩
  ((xT', yT'), mkLineFp12 ell_vv ell_vw ell_vvw)

-- ============================================================================
-- Twisted Frobenius (for the optimal-ate final steps)
-- ============================================================================

/-- Twisted-Frobenius constants for the BN254 sextic twist (ξ = 9 + u):
    γ₁ = ξ^((p-1)/3), γ₂ = ξ^((p-1)/2). Spec-level (computed by direct
    exponentiation; correctness, not speed, is what matters). -/
def frobGammaX : Fp2 basePrime := Fp2.powNat Fp2.xi ((basePrime - 1) / 3)
def frobGammaY : Fp2 basePrime := Fp2.powNat Fp2.xi ((basePrime - 1) / 2)

/-- Frobenius endomorphism ψ on the twist `E'(F_{p²})`:
    `ψ(x, y) = (γ₁ · x̄, γ₂ · ȳ)`, where `x̄` is the `F_{p²}`-conjugate (`= xᵖ`,
    since `p ≡ 3 mod 4`). Used for the two optimal-ate final line steps. -/
def g2Frobenius (Q : Fp2 basePrime × Fp2 basePrime) :
    Fp2 basePrime × Fp2 basePrime :=
  let (x, y) := Q
  (frobGammaX * x.conj, frobGammaY * y.conj)

-- ============================================================================
-- Miller Loop
-- ============================================================================

/-- Miller loop: compute the product of line evaluations for the optimal
    Ate pairing on BN254.

    Iterates over NAF bits of 6x + 2, performing doubling steps at each bit
    and addition steps at non-zero bits.

    Returns an element of Fp12 (before final exponentiation). -/
def millerLoop (P : Option (ZMod basePrime × ZMod basePrime))
    (Q : G2Point) : Fp12 basePrime :=
  match P, Q with
  | none, _ => 1
  | _, none => 1
  | some (xP, yP), some (xQ, yQ) =>
    let negQ := (xQ, -yQ)
    -- Start with T = Q, f = 1
    -- NAF: first bit is 1 (MSB), so skip it and start the loop from index 1
    let (f, T_final) := ateLoopNAF.tail.foldl
      (fun (f, T) si =>
        -- Doubling step
        let (T', ell) := doublingStep T xP yP
        let f' := f * f * ell
        -- Addition step if si ≠ 0
        if si == 1 then
          let (T'', ell2) := additionStep T' (xQ, yQ) xP yP
          (f' * ell2, T'')
        else if si == -1 then
          let (T'', ell2) := additionStep T' negQ xP yP
          (f' * ell2, T'')
        else
          (f', T'))
      (1, (xQ, yQ))
    -- Optimal-ate final steps for BN curves: two extra line evaluations with
    -- π(Q) and -π²(Q) (the twisted Frobenius). Omitting these yields a
    -- non-degenerate but non-bilinear map.
    let q1 := g2Frobenius (xQ, yQ)
    let q2 := g2Frobenius q1
    let nq2 := (q2.1, -q2.2)
    let (T₁, ell₁) := additionStep T_final q1 xP yP
    let (_, ell₂) := additionStep T₁ nq2 xP yP
    f * ell₁ * ell₂

end LeanStableHLO.StableHLO.ConcretePairing
