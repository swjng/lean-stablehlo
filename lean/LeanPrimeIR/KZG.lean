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

import LeanPrimeIR.Polynomial

namespace LeanPrimeIR.KZG

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

end LeanPrimeIR.KZG
