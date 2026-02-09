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

import LeanPrimeIR.IR

namespace LeanPrimeIR.Field

/-- Emit `stablehlo.constant dense<val> : tensor<!SFm>`. -/
def const (val : Int) (ty : MLIRType := BN254.SFm) : IRBuilder Value := do
  let name ← freshName
  emit s!"  {name} = stablehlo.constant dense<{val}> : {ty}"
  return ⟨name, ty⟩

private def binOp (opName : String) (lhs rhs : Value) : IRBuilder Value := do
  let name ← freshName
  emit s!"  {name} = stablehlo.{opName} {lhs.name}, {rhs.name} : {lhs.ty}"
  return ⟨name, lhs.ty⟩

/-- Emit `stablehlo.add`. -/
def add (lhs rhs : Value) : IRBuilder Value := binOp "add" lhs rhs

/-- Emit `stablehlo.multiply`. -/
def mul (lhs rhs : Value) : IRBuilder Value := binOp "multiply" lhs rhs

/-- Emit `stablehlo.subtract`. -/
def sub (lhs rhs : Value) : IRBuilder Value := binOp "subtract" lhs rhs

/-- Emit `stablehlo.divide`. -/
def div (lhs rhs : Value) : IRBuilder Value := binOp "divide" lhs rhs

/-- Emit `stablehlo.power`. -/
def pow (base exp : Value) : IRBuilder Value := binOp "power" base exp

/-- Emit `stablehlo.negate`. -/
def neg (operand : Value) : IRBuilder Value := do
  let name ← freshName
  emit s!"  {name} = stablehlo.negate {operand.name} : {operand.ty}"
  return ⟨name, operand.ty⟩

end LeanPrimeIR.Field
