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

import LeanStableHLO.StableHLO.Expr

namespace LeanStableHLO.StableHLO

-- Serialization: the only unverified component in the trust chain.
-- This module converts a proven `Expr p` AST into StableHLO MLIR text.
-- It is intentionally kept trivial and inspectable.

/-- MLIR type for a prime field element in tensor form.
    Renders as `tensor<!field.pf<modulus:iN, montgomery>>`. -/
structure FieldType where
  modulus : String
  bitwidth : Nat
  montgomery : Bool

def FieldType.render (ft : FieldType) : String :=
  let mont := if ft.montgomery then ", true" else ""
  s!"tensor<!field.pf<{ft.modulus}:i{ft.bitwidth}{mont}>>"

instance : ToString FieldType where
  toString := FieldType.render

/-- BN254 scalar field in Montgomery form. -/
def bn254SFm : FieldType :=
  { modulus := "21888242871839275222246405745257275088548364400416034343698204186575808495617"
    bitwidth := 256
    montgomery := true }

/-- BN254 base (point coordinate) field in Montgomery form. -/
def bn254PFm : FieldType :=
  { modulus := "21888242871839275222246405745257275088696311157297823662689037894645226208583"
    bitwidth := 256
    montgomery := true }

/-- Serialization state: SSA counter + accumulated MLIR lines. -/
structure SerState where
  nextId : Nat := 0
  lines : Array String := #[]

/-- Serialization monad. -/
abbrev Ser := StateM SerState

/-- Generate a fresh SSA name `%v0`, `%v1`, ... -/
def freshSSA : Ser String := do
  let s ← get
  let name := s!"%v{s.nextId}"
  set { s with nextId := s.nextId + 1 }
  return name

/-- Emit one line of MLIR text. -/
def emitLine (line : String) : Ser Unit := do
  let s ← get
  set { s with lines := s.lines.push line }

/-- Serialize an `Expr p` to StableHLO MLIR, returning the SSA name
    that holds the result. Each AST node becomes exactly one MLIR op.

    This is the **trust boundary**: correctness of the overall pipeline
    depends on this function faithfully translating the AST structure.
    It is kept simple enough to be inspected by eye. -/
def serialize {p : Nat} (ft : FieldType) (valStr : ZMod p → String) : Expr p → Ser String
  | .const v => do
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.constant dense<{valStr v}> : {ft}"
    return name
  | .add a b => do
    let la ← serialize ft valStr a
    let lb ← serialize ft valStr b
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.add {la}, {lb} : {ft}"
    return name
  | .mul a b => do
    let la ← serialize ft valStr a
    let lb ← serialize ft valStr b
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.multiply {la}, {lb} : {ft}"
    return name
  | .sub a b => do
    let la ← serialize ft valStr a
    let lb ← serialize ft valStr b
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.subtract {la}, {lb} : {ft}"
    return name
  | .neg a => do
    let la ← serialize ft valStr a
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.negate {la} : {ft}"
    return name
  | .div a b => do
    let la ← serialize ft valStr a
    let lb ← serialize ft valStr b
    let name ← freshSSA
    emitLine s!"  {name} = stablehlo.divide {la}, {lb} : {ft}"
    return name

/-- Run serialization and collect all MLIR lines. -/
def runSer {α : Type} (action : Ser α) : α × Array String :=
  let (result, state) := action.run {}
  (result, state.lines)

/-- Serialize multiple expressions, returning their SSA names. -/
def serializeAll {p : Nat} (ft : FieldType) (valStr : ZMod p → String)
    (exprs : List (Expr p)) : Ser (List String) :=
  exprs.mapM (serialize ft valStr)

end LeanStableHLO.StableHLO
