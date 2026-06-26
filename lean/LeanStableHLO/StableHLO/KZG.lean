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

import LeanStableHLO.StableHLO.Polynomial
import LeanStableHLO.StableHLO.EllipticCurve
import LeanStableHLO.StableHLO.BN254
import LeanStableHLO.StableHLO.Pairing
import LeanStableHLO.StableHLO.Serialize

namespace LeanStableHLO.StableHLO.KZG

open Polynomial Expr BN254

-- ============================================================================
-- KZG Evaluate (existing M2)
-- ============================================================================

/-- Build KZG evaluate AST: Horner evaluation + synthetic division.
    Returns (evalExpr, quotientExprs). -/
def evaluateExprs {p : Nat} (coeffs : List (ZMod p)) (z : ZMod p)
    : Expr p × List (Expr p) :=
  let coeffExprs := coeffs.map .const
  let zExpr := Expr.const z
  let evalExpr := hornerExpr coeffExprs zExpr
  let quotExprs := syntheticDivExpr coeffExprs zExpr
  (evalExpr, quotExprs)

/-- Generate a complete StableHLO module for KZG evaluate.

    Pipeline:
    1. Build `Expr p` AST for Horner + synthetic division (pure, proven)
    2. Serialize AST → MLIR text (trivial, inspectable) -/
def evaluateModule (p : Nat) [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p)
    (ft : FieldType := bn254SFm)
    (valStr : ZMod p → String) : String :=
  let (evalExpr, quotExprs) := evaluateExprs coeffs z
  let allExprs := evalExpr :: quotExprs

  let (ssaNames, lines) := runSer do
    serializeAll ft valStr allExprs

  let body := lines.toList |> String.intercalate "\n"
  let retNames := ssaNames |> String.intercalate ", "
  let retTypes := ssaNames.map (fun _ => s!"{ft}") |> String.intercalate ", "

  let ftType := ft.render.drop 7 |>.dropEnd 1  -- strip "tensor<" and ">"
  let typeAlias := s!"!SFm = {ftType}\n"
  let funcSig := s!"func.func @kzg_evaluate() -> ({retTypes}) \{"
  let ret := s!"  return {retNames} : {retTypes}"

  s!"{typeAlias}\n{funcSig}\n{body}\n\n{ret}\n}"

-- ============================================================================
-- SRS (Structured Reference String)
-- ============================================================================

/-- SRS for KZG: a list of G₁ points [G, [s]G, [s²]G, ...].
    At the AST level, these are `AffinePoint basePrime` values
    whose coordinates are `Expr basePrime`. -/
structure SRS where
  /-- G₁ points: srs[i] should equal [sⁱ] · G₁.gen. -/
  g1Points : List (AffinePoint basePrime)

-- ============================================================================
-- KZG Commit
-- ============================================================================

/-- KZG commitment: C = MSM(SRS, coeffs) = Σ coeffs[i] · SRS[i].
    Takes scalar-field coefficients (as Nat via `.val`) and base-field SRS points.
    Returns an `AffinePoint basePrime`. -/
def commit (coeffs : List (ZMod scalarPrime)) (srs : SRS)
    : AffinePoint basePrime :=
  msm (coeffs.map ZMod.val) srs.g1Points

-- ============================================================================
-- KZG Prove
-- ============================================================================

/-- KZG prove result: commitment, evaluation value, quotient, and proof. -/
structure ProveResult where
  /-- Commitment C = MSM(SRS, coeffs). -/
  commitment : AffinePoint basePrime
  /-- Evaluation expression v = p(z) as `Expr scalarPrime`. -/
  evalValue : Expr scalarPrime
  /-- Quotient coefficient expressions [q₀, ..., qₙ₋₁] as `Expr scalarPrime`. -/
  quotientCoeffs : List (Expr scalarPrime)
  /-- Proof π = MSM(SRS[0..deg(q)], q_coeffs). -/
  proof : AffinePoint basePrime

/-- Full KZG prove pipeline:
    1. Commit: C = MSM(SRS, coeffs)
    2. Evaluate: v = p(z) via Horner
    3. Quotient: q(x) = (p(x) - p(z)) / (x - z) via synthetic division
    4. Proof: π = MSM(SRS[0..deg(q)], q_coeffs)

    Polynomial operations use scalar field; EC operations use base field. -/
def prove (coeffs : List (ZMod scalarPrime)) (z : ZMod scalarPrime)
    (srs : SRS) : ProveResult :=
  let c := commit coeffs srs
  let (evalExpr, quotExprs) := evaluateExprs coeffs z
  let quotScalars := quotExprs.map (fun e => e.eval.val)
  let pi := msm quotScalars (srs.g1Points.take quotExprs.length)
  { commitment := c
    evalValue := evalExpr
    quotientCoeffs := quotExprs
    proof := pi }

-- ============================================================================
-- KZG Verify (spec-level predicate)
-- ============================================================================

/-- KZG verification equation (spec-level, uses axiomatized pairing).
    Checks: e(π, [s]G₂ - [z]G₂) = e(C - [v]G₁, G₂)

    This is a `Prop`, not an AST computation. Pairings are not expressible
    as StableHLO field ops — the verifier runs natively, not in MLIR. -/
def verify (C : Pairing.G1) (z v : ZMod scalarPrime) (π : Pairing.G1)
    (sG2 G2gen : Pairing.G2) : Prop :=
  Pairing.e π (Pairing.G2.add sG2 (Pairing.G2.smul (-z) G2gen)) =
  Pairing.e (Pairing.G1.add C (Pairing.G1.smul (-v) Pairing.G1.gen)) G2gen

end LeanStableHLO.StableHLO.KZG
