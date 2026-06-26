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

import LeanStableHLO.IR

namespace LeanStableHLO.Field

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

end LeanStableHLO.Field
