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

import LeanPrimeIR.StableHLO.Polynomial
import LeanPrimeIR.StableHLO.Serialize

namespace LeanPrimeIR.StableHLO.KZG

open Polynomial Expr

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

end LeanPrimeIR.StableHLO.KZG
