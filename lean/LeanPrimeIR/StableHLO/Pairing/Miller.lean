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

import LeanPrimeIR.StableHLO.FieldExt.Fp12
import LeanPrimeIR.StableHLO.Pairing.G2

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

namespace LeanPrimeIR.StableHLO.ConcretePairing

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
  [1, 0, 1, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0,
   0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0,
   -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]

-- ============================================================================
-- Sparse Fp12 from Line Evaluation
-- ============================================================================

/-- Embed an Fp2 element into Fp12 at the c0.c0 position. -/
def fp2ToFp12_00 (a : Fp2 basePrime) : Fp12 basePrime :=
  ⟨⟨a, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- Create a sparse Fp12 line evaluation result.
    A line function evaluates to an element of the form:
    a₀ + a₁·w where a₀, a₁ are sparse in Fp6. -/
def mkLineFp12 (a00 a01 a10 : Fp2 basePrime) : Fp12 basePrime :=
  ⟨⟨a00, a01, 0⟩, ⟨a10, 0, 0⟩⟩

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
  -- Line evaluation at P (sparse Fp12):
  --   c0.c0 = λ·xT - yT  (Fp2 coefficient of 1)
  --   c0.c1 = -λ·xP      (Fp2 coefficient of v, but xP is in Fp so embed)
  --   c1.c0 = yP          (Fp2 coefficient of w)
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
    let (f, _T) := ateLoopNAF.tail.foldl
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
    f

end LeanPrimeIR.StableHLO.ConcretePairing
