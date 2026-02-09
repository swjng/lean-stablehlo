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

import LeanPrimeIR.StableHLO.KZG

/-!
# Correctness Theorems for Deep-Embedded StableHLO

This module proves that `Expr.eval` of the AST built by `hornerExpr` and
`syntheticDivExpr` matches the value-level specification. Together with
the trivially inspectable serializer, this establishes the correctness
chain:

    Lean proof (this file)  →  Expr AST  →  serializer  →  MLIR text
         ↕ (formal)              ↕ (eval)      ↕ (inspectable)
    polyEval spec           ZMod p value    StableHLO ops
-/

namespace LeanPrimeIR.StableHLO

open Expr Polynomial

-- ============================================================================
-- Specifications (value-level, no Expr)
-- ============================================================================

/-- Polynomial evaluation via Horner's method (specification).
    Given coefficients [c₀, c₁, ..., cₙ] (ascending degree) and point z:
      polyEval [c₀, c₁, ..., cₙ] z = (...((cₙ * z + cₙ₋₁) * z + ...)...) * z + c₀ -/
def polyEval {p : Nat} [NeZero p] (coeffs : List (ZMod p)) (z : ZMod p) : ZMod p :=
  match coeffs.reverse with
  | [] => 0
  | cn :: rest => rest.foldl (fun acc ci => acc * z + ci) cn

/-- Synthetic division quotient coefficients (specification).
    Given coefficients [c₀, c₁, ..., cₙ] (ascending) and point z,
    returns [q₀, q₁, ..., qₙ₋₁] (ascending) where:
      qₙ₋₁ = cₙ
      qᵢ₋₁ = cᵢ + z * qᵢ  for i = n-1, ..., 1 -/
def syntheticDivSpec {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) : List (ZMod p) :=
  match coeffs.reverse with
  | [] | [_] => []
  | cn :: rest =>
    let inner := rest.dropLast
    let (_, quotient) := inner.foldl
      (fun (acc, qs) ci => let q := ci + z * acc; (q, q :: qs))
      (cn, [cn])
    quotient

-- ============================================================================
-- Lemmas
-- ============================================================================

/-- Core structural lemma: Horner foldl over `const`-mapped list evaluates
    to the value-level Horner foldl. Generalized over the accumulator. -/
private theorem foldl_horner_eval {p : Nat} [NeZero p]
    (rest : List (ZMod p)) (acc : Expr p) (z : Expr p) :
    ((rest.map Expr.const).foldl (fun a ci => .add (.mul a z) ci) acc).eval =
    rest.foldl (fun a ci => a * z.eval + ci) acc.eval := by
  induction rest generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map, List.foldl]
    exact ih (.add (.mul acc z) (.const hd))

/-- Structural lemma for synthetic division foldl. -/
private theorem foldl_syndiv_eval {p : Nat} [NeZero p]
    (inner : List (ZMod p)) (acc : Expr p) (qs : List (Expr p)) (z : Expr p) :
    let f := fun (st : Expr p × List (Expr p)) (ci : Expr p) =>
      let q := Expr.add ci (.mul z st.1); (q, q :: st.2)
    let g := fun (st : ZMod p × List (ZMod p)) (ci : ZMod p) =>
      let q := ci + z.eval * st.1; (q, q :: st.2)
    let (accE, qsE) := (inner.map Expr.const).foldl f (acc, qs)
    let (accV, qsV) := inner.foldl g (acc.eval, qs.map Expr.eval)
    accE.eval = accV ∧ qsE.map Expr.eval = qsV := by
  induction inner generalizing acc qs with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    simp only [List.map, List.foldl]
    exact ih (.add (.const hd) (.mul z acc)) (Expr.add (.const hd) (.mul z acc) :: qs)

-- ============================================================================
-- Main Theorems
-- ============================================================================

/-- **Horner correctness**: evaluating the `hornerExpr` AST yields the same
    result as the value-level `polyEval` specification.

    This is the main theorem that bridges the deep-embedded AST world
    with the mathematical specification world. -/
theorem horner_correct {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    (hornerExpr (coeffs.map Expr.const) (.const z)).eval = polyEval coeffs z := by
  unfold hornerExpr polyEval
  rw [List.map_reverse.symm]
  match h : coeffs.reverse with
  | [] => simp [Expr.eval]
  | cn :: rest =>
    simp only [List.map]
    exact foldl_horner_eval rest (.const cn) (.const z)

/-- **Synthetic division correctness**: evaluating each quotient expression
    from `syntheticDivExpr` yields the same coefficients as the value-level
    `syntheticDivSpec`. -/
theorem syntheticDiv_correct {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    (syntheticDivExpr (coeffs.map Expr.const) (.const z)).map Expr.eval
    = syntheticDivSpec coeffs z := by
  unfold syntheticDivExpr syntheticDivSpec
  rw [List.map_reverse.symm]
  match h : coeffs.reverse with
  | [] => simp
  | [_] => simp
  | cn :: r :: rest' =>
    simp only [List.map]
    have hlast : (Expr.const r :: List.map Expr.const rest').dropLast
                 = List.map Expr.const (r :: rest').dropLast :=
      (List.map_dropLast (f := Expr.const) (l := r :: rest')).symm
    rw [hlast]
    exact (foldl_syndiv_eval (r :: rest').dropLast (.const cn) [.const cn] (.const z)).2

/-- **KZG evaluate correctness**: the evaluation expression from
    `evaluateExprs` computes `polyEval`, and the quotient expressions
    compute `syntheticDivSpec`. -/
theorem evaluate_correct {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    (KZG.evaluateExprs coeffs z).1.eval = polyEval coeffs z
    ∧ (KZG.evaluateExprs coeffs z).2.map Expr.eval = syntheticDivSpec coeffs z := by
  simp only [KZG.evaluateExprs]
  exact ⟨horner_correct coeffs z, syntheticDiv_correct coeffs z⟩

end LeanPrimeIR.StableHLO
