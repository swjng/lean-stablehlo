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

import LeanStableHLO.Polynomial

namespace LeanStableHLO.KZG

/-- Generate KZG evaluate function body:
    1. Create coefficient constants
    2. Horner evaluation → p(z)
    3. Synthetic division → quotient coefficients
    Returns (evaluation, quotientCoeffs). -/
def evaluate (coeffs : List Int) (z : Int) : IRBuilder (Value × List Value) := do
  let terms := coeffs.zip (List.range coeffs.length) |>.map (fun (c, i) => s!"{c}x^{i}")
  emitComment s!"p(x) = {terms |> String.intercalate " + "}"
  let coeffVals ← coeffs.mapM (fun c => Field.const c)
  emitBlank
  let zVal ← Field.const z
  emitBlank

  emitComment "Horner evaluation"
  let v ← Polynomial.hornerEval coeffVals zVal
  emitBlank

  emitComment "Synthetic division"
  let q ← Polynomial.syntheticDiv coeffVals zVal

  return (v, q)

/-- Generate a complete StableHLO module for KZG evaluate.
    Includes type alias and function definition. -/
def evaluateModule (coeffs : List Int) (z : Int) : String :=
  let sfmType := MLIRType.fieldPF BN254.scalarPrime 256 true
  let header := s!"!SFm = {sfmType}\n"
  let tensorTy := BN254.SFm

  let body := buildMLIR do
    let (v, q) ← evaluate coeffs z
    emitBlank
    let retVals := v :: q
    let retNames := retVals.map (·.name) |> String.intercalate ", "
    let retTypes := retVals.map (fun _ => s!"{tensorTy}") |> String.intercalate ", "
    emit s!"  return {retNames} : {retTypes}"

  let retCount := coeffs.length  -- 1 eval + (n-1) quotient coeffs
  let retTypes := List.replicate retCount s!"{tensorTy}" |> String.intercalate ", "
  let funcSig := s!"func.func @kzg_evaluate() -> ({retTypes}) \{"

  s!"{header}\n{funcSig}\n{body}\n}"

end LeanStableHLO.KZG
