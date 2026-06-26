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

import Mathlib.Data.ZMod.Basic

namespace LeanStableHLO.StableHLO

/-- Deep-embedded StableHLO expression AST over a prime field 𝔽ₚ.

    This is the core of the deep embedding approach: programs are
    represented as Lean terms (AST nodes), not as strings. Proofs
    are stated about `eval` of these AST nodes, and the only
    unverified component is the trivial `Expr → String` serializer. -/
inductive Expr (p : Nat) where
  /-- Field constant: `stablehlo.constant dense<v>` -/
  | const : ZMod p → Expr p
  /-- Field addition: `stablehlo.add` -/
  | add : Expr p → Expr p → Expr p
  /-- Field multiplication: `stablehlo.multiply` -/
  | mul : Expr p → Expr p → Expr p
  /-- Field subtraction: `stablehlo.subtract` -/
  | sub : Expr p → Expr p → Expr p
  /-- Field negation: `stablehlo.negate` -/
  | neg : Expr p → Expr p
  /-- Field division: `stablehlo.divide` (a * b⁻¹ in ZMod p) -/
  | div : Expr p → Expr p → Expr p
  deriving Repr, BEq

/-- Denotational semantics: evaluate an `Expr p` to a value in `ZMod p`.

    This gives formal meaning to the AST. Correctness theorems relate
    `eval` of a constructed AST to a specification (e.g., polynomial
    evaluation), and the serializer maps the same AST to MLIR text. -/
def Expr.eval {p : Nat} [NeZero p] : Expr p → ZMod p
  | .const v => v
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .sub a b => a.eval - b.eval
  | .neg a => -a.eval
  | .div a b => a.eval * b.eval⁻¹

end LeanStableHLO.StableHLO
