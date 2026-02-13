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
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree

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
-- Polynomial Bridge: polyEval ↔ Mathlib Polynomial.eval
-- ============================================================================

/-- Convert a list of coefficients (ascending degree) to a Mathlib polynomial.
    `listPoly [c₀, c₁, ..., cₙ₋₁]` is the polynomial c₀ + c₁·X + ... + cₙ₋₁·Xⁿ⁻¹. -/
noncomputable def listPoly {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) : _root_.Polynomial (ZMod p) :=
  _root_.Polynomial.ofFn coeffs.length (fun i => coeffs.get i)

/-- Horner foldr equals ascending-power sum. -/
private theorem foldr_horner_eq_sum {p : Nat} [NeZero p]
    (l : List (ZMod p)) (z : ZMod p) :
    l.foldr (fun ci a => a * z + ci) 0 =
    ∑ i ∈ Finset.range l.length, l.getD i 0 * z ^ i := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `polyEval` equals the right fold with Horner's step. -/
private theorem polyEval_eq_foldr {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    polyEval coeffs z = coeffs.foldr (fun ci a => a * z + ci) 0 := by
  unfold polyEval
  match hr : coeffs.reverse with
  | [] =>
    have : coeffs = [] := List.reverse_eq_nil_iff.mp hr
    subst this; rfl
  | cn :: rest =>
    show rest.foldl (fun acc ci => acc * z + ci) cn =
        coeffs.foldr (fun ci a => a * z + ci) 0
    have hfold : rest.foldl (fun a ci => a * z + ci) cn =
        coeffs.reverse.foldl (fun a ci => a * z + ci) 0 := by
      rw [hr]; simp [List.foldl_cons]
    rw [hfold, List.foldl_reverse]

/-- `polyEval` equals the ascending-power sum ∑ cᵢ · zⁱ. -/
private theorem polyEval_eq_sum {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    polyEval coeffs z =
    ∑ i ∈ Finset.range coeffs.length, coeffs.getD i 0 * z ^ i := by
  rw [polyEval_eq_foldr]; exact foldr_horner_eq_sum coeffs z

/-- `listPoly` evaluation equals the ascending-power sum. -/
private theorem listPoly_eval {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    (listPoly coeffs).eval z =
    ∑ i ∈ Finset.range coeffs.length, coeffs.getD i 0 * z ^ i := by
  simp only [listPoly]
  by_cases hlen : coeffs.length = 0
  · have : coeffs = [] := by cases coeffs <;> simp_all
    subst this; simp
  · rw [_root_.Polynomial.eval_eq_sum_range'
        (_root_.Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hlen) _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    rw [_root_.Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
    exact (List.getD_eq_getElem _ _ hi).symm

/-- **Polynomial bridge**: `polyEval` equals Mathlib's `Polynomial.eval` applied to
    the polynomial with the same coefficients. This connects our Horner-based
    specification to the standard mathematical definition ∑ cᵢ · zⁱ. -/
theorem polyEval_eq_polynomial_eval {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    polyEval coeffs z = (listPoly coeffs).eval z := by
  rw [polyEval_eq_sum, listPoly_eval]

-- ============================================================================
-- Synthetic Division Polynomial Identity: q(x)·(x-z) + p(z) = p(x)
-- ============================================================================

/-- `polyEval` respects list cons: `polyEval (c :: cs) z = c + z * polyEval cs z`. -/
private theorem polyEval_cons {p : Nat} [NeZero p]
    (c : ZMod p) (cs : List (ZMod p)) (z : ZMod p) :
    polyEval (c :: cs) z = c + z * polyEval cs z := by
  rw [polyEval_eq_foldr, List.foldr_cons, polyEval_eq_foldr]; ring

/-- `listPoly` respects list cons: ascending-degree decomposition. -/
private theorem listPoly_cons {p : Nat} [NeZero p]
    (a : ZMod p) (l : List (ZMod p)) :
    listPoly (a :: l) = _root_.Polynomial.C a + _root_.Polynomial.X * listPoly l := by
  apply _root_.Polynomial.ext; intro n
  simp only [listPoly, List.length_cons, _root_.Polynomial.coeff_add]
  cases n with
  | zero =>
    simp [_root_.Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.zero_lt_succ _),
          _root_.Polynomial.coeff_C_zero]
  | succ m =>
    rw [_root_.Polynomial.coeff_C_succ, zero_add, _root_.Polynomial.coeff_X_mul]
    by_cases hm : m < l.length
    · simp [_root_.Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega : m + 1 < l.length + 1),
            _root_.Polynomial.ofFn_coeff_eq_val_of_lt _ hm]
    · rw [_root_.Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : l.length + 1 ≤ m + 1),
          _root_.Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : l.length ≤ m)]

/-- First component of the synthetic division foldl equals a scalar Horner foldl. -/
private theorem foldl_syndiv_fst {p : Nat} [NeZero p]
    (items : List (ZMod p)) (acc : ZMod p) (qs : List (ZMod p)) (z : ZMod p) :
    (items.foldl (fun (st : ZMod p × List (ZMod p)) ci =>
      let q := ci + z * st.1; (q, q :: st.2)) (acc, qs)).1 =
    items.foldl (fun a ci => a * z + ci) acc := by
  induction items generalizing acc qs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih, show hd + z * acc = acc * z + hd from by ring]

/-- `syntheticDivSpec` respects list cons. -/
private theorem syntheticDivSpec_cons {p : Nat} [NeZero p]
    (c₀ c₁ : ZMod p) (cs : List (ZMod p)) (z : ZMod p) :
    syntheticDivSpec (c₀ :: c₁ :: cs) z =
    polyEval (c₁ :: cs) z :: syntheticDivSpec (c₁ :: cs) z := by
  cases cs with
  | nil =>
    -- Both sides reduce to [c₁] by kernel computation
    rfl
  | cons c₂ cs' =>
    -- Only unfold syntheticDivSpec (not polyEval) to avoid match interference
    unfold syntheticDivSpec
    simp only [List.reverse_cons]
    -- Abstract the common reversed sublist and decompose it
    generalize hrev : cs'.reverse ++ [c₂] ++ [c₁] = rev
    have hlen : 2 ≤ rev.length := by rw [← hrev]; simp
    obtain ⟨a, b, tl, rfl⟩ : ∃ a b tl, rev = a :: b :: tl := by
      match rev, hlen with
      | a :: b :: tl, _ => exact ⟨a, b, tl, rfl⟩
      | [], h | [_], h => simp at h
    -- Both matches now have constructor-headed scrutinees and reduce
    simp only [List.cons_append]
    -- After match reduction, relate the foldl results
    -- LHS processes (b :: tl ++ [c₀]).dropLast = b :: tl (drop final c₀)
    -- RHS processes (b :: tl).dropLast
    have htl_ne : tl ++ [c₀] ≠ [] := by simp
    rw [List.dropLast_cons_of_ne_nil htl_ne, List.dropLast_concat]
    -- Now LHS folds over (b :: tl), RHS folds over (b :: tl).dropLast
    -- (b :: tl) ends with c₁ (from hrev: a :: b :: tl = cs'.reverse ++ [c₂, c₁])
    have htl_split : b :: tl = (b :: tl).dropLast ++ [c₁] := by
      have hdl : a :: (b :: tl).dropLast = cs'.reverse ++ [c₂] := by
        have h := congr_arg List.dropLast hrev.symm
        rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b tl)] at h
        rwa [List.dropLast_concat] at h
      have h2 : a :: b :: tl = a :: ((b :: tl).dropLast ++ [c₁]) := by
        rw [← List.cons_append, hdl]; exact hrev.symm
      exact congrArg List.tail h2
    -- Split LHS foldl over (b :: tl) = (b :: tl).dropLast ++ [c₁]
    conv_lhs => rw [htl_split, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set base := (b :: tl).dropLast.foldl (fun (st : ZMod p × List (ZMod p)) ci =>
      let q := ci + z * st.1; (q, q :: st.2)) (a, [a])
    -- First component = scalar Horner foldl
    have hfst : base.1 = (b :: tl).dropLast.foldl (fun acc ci => acc * z + ci) a :=
      foldl_syndiv_fst (b :: tl).dropLast a [a] z
    -- Connect scalar foldl to polyEval via reversed list
    have hfull : a :: (b :: tl).dropLast = (c₂ :: cs').reverse := by
      have h := congr_arg List.dropLast hrev.symm
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b tl)] at h
      rwa [List.dropLast_concat, ← List.reverse_cons] at h
    have hfst_eval : base.1 = polyEval (c₂ :: cs') z := by
      rw [hfst]
      have : (b :: tl).dropLast.foldl (fun a ci => a * z + ci) a =
          (c₂ :: cs').reverse.foldl (fun a ci => a * z + ci) 0 := by
        rw [← hfull]; simp [List.foldl_cons]
      rw [this, List.foldl_reverse]
      exact (polyEval_eq_foldr (c₂ :: cs') z).symm
    congr 1
    rw [hfst_eval]; exact (polyEval_cons c₁ (c₂ :: cs') z).symm

/-- **Synthetic division polynomial identity**: the quotient polynomial `q(x)` from
    synthetic division satisfies `q(x) · (x - z) + p(z) = p(x)`.

    This proves that `syntheticDivSpec` computes the correct polynomial long division
    quotient when dividing by the linear factor `(x - z)`. -/
theorem syntheticDiv_polynomial_correct {p : Nat} [NeZero p]
    (coeffs : List (ZMod p)) (z : ZMod p) :
    listPoly (syntheticDivSpec coeffs z) *
      (_root_.Polynomial.X - _root_.Polynomial.C z) +
    _root_.Polynomial.C (polyEval coeffs z) = listPoly coeffs := by
  induction coeffs with
  | nil => simp [syntheticDivSpec, polyEval, listPoly]
  | cons c₀ tl ih =>
    cases tl with
    | nil =>
      have h1 : syntheticDivSpec [c₀] z = [] := rfl
      have h2 : polyEval [c₀] z = c₀ := rfl
      have h3 : listPoly ([] : List (ZMod p)) = 0 := by
        simp [listPoly, _root_.Polynomial.ofFn_zero']
      rw [h1, h2, h3, listPoly_cons, h3]
      ring
    | cons c₁ cs =>
      rw [syntheticDivSpec_cons, listPoly_cons, listPoly_cons, ← ih]
      rw [polyEval_cons c₀ (c₁ :: cs) z, _root_.Polynomial.C_add, _root_.Polynomial.C_mul]
      ring

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
