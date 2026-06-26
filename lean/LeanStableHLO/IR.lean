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

namespace LeanStableHLO

/-- MLIR type representation. -/
inductive MLIRType where
  | i (width : Nat)
  | index
  | fieldPF (modulus : String) (bitwidth : Nat) (mont : Bool)
  | tensor (shape : List Nat) (elem : MLIRType)

/-- Render an MLIR type to its textual form. -/
def MLIRType.render : MLIRType → String
  | .i w => s!"i{w}"
  | .index => "index"
  | .fieldPF m bw mont =>
    let montStr := if mont then ", true" else ""
    s!"!field.pf<{m}:i{bw}{montStr}>"
  | .tensor shape elem =>
    let shapeStr := shape.map Nat.repr |>.intersperse "x" |> String.join
    let sep := if shapeStr.isEmpty then "" else "x"
    s!"tensor<{shapeStr}{sep}{elem.render}>"

instance : ToString MLIRType where
  toString := MLIRType.render

-- BN254 curve constants
namespace BN254

def scalarPrime : String :=
  "21888242871839275222246405745257275088548364400416034343698204186575808495617"

def basePrime : String :=
  "21888242871839275222246405745257275088696311157297823662689037894645226208583"

/-- BN254 scalar field in Montgomery form: `tensor<!field.pf<p:i256, true>>` -/
def SFm : MLIRType := .tensor [] (.fieldPF scalarPrime 256 true)

/-- BN254 scalar field in standard form: `tensor<!field.pf<p:i256>>` -/
def SF : MLIRType := .tensor [] (.fieldPF scalarPrime 256 false)

end BN254

/-- SSA value reference. -/
structure Value where
  name : String
  ty : MLIRType

instance : ToString Value where
  toString v := v.name

/-- Builder monad state: SSA name counter + accumulated MLIR lines. -/
structure BuilderState where
  nextId : Nat := 0
  lines : Array String := #[]

/-- IR builder monad for generating MLIR text. -/
abbrev IRBuilder := StateM BuilderState

/-- Generate a fresh SSA name like `%v0`, `%v1`, ... -/
def freshName (pfx : String := "v") : IRBuilder String := do
  let s ← get
  let name := s!"%{pfx}{s.nextId}"
  set { s with nextId := s.nextId + 1 }
  return name

/-- Emit a line of MLIR text. -/
def emit (line : String) : IRBuilder Unit := do
  let s ← get
  set { s with lines := s.lines.push line }

/-- Emit a blank line. -/
def emitBlank : IRBuilder Unit := emit ""

/-- Emit a comment line. -/
def emitComment (comment : String) : IRBuilder Unit :=
  emit s!"  // {comment}"

/-- Run a builder and return the result plus generated lines. -/
def runBuilder {α : Type} (b : IRBuilder α) : α × Array String :=
  let (result, state) := b.run {}
  (result, state.lines)

/-- Run a builder and return only the generated MLIR text. -/
def buildMLIR {α : Type} (b : IRBuilder α) : String :=
  let (_, lines) := runBuilder b
  lines.toList |> String.intercalate "\n"

end LeanStableHLO
