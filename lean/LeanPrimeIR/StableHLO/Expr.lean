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

import Mathlib.Data.ZMod.Basic

namespace LeanPrimeIR.StableHLO

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

end LeanPrimeIR.StableHLO
