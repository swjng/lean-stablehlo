-- Copyright 2026 Soowon Jeong.
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

import LeanStableHLO.StableHLO.Expr

namespace LeanStableHLO.StableHLO.Polynomial

open Expr

/-- Horner evaluation of a polynomial at point z.
    Given coefficients [c₀, c₁, ..., cₙ] (ascending degree) and point z,
    builds an `Expr p` representing:
      p(z) = (...((cₙ * z + cₙ₋₁) * z + cₙ₋₂)...) * z + c₀ -/
def hornerExpr {p : Nat} (coeffs : List (Expr p)) (z : Expr p) : Expr p :=
  match coeffs.reverse with
  | [] => .const 0
  | cn :: rest => rest.foldl (fun acc ci => .add (.mul acc z) ci) cn

/-- Synthetic division: build quotient expressions for
    q(x) = (p(x) - p(z)) / (x - z).

    Given coefficients [c₀, c₁, ..., cₙ] (ascending) and point z,
    returns quotient coefficient expressions [q₀, q₁, ..., qₙ₋₁] (ascending).

    Algorithm (descending):
      qₙ₋₁ = cₙ
      qᵢ₋₁ = cᵢ + z * qᵢ  for i = n-1, ..., 1 -/
def syntheticDivExpr {p : Nat} (coeffs : List (Expr p)) (z : Expr p) : List (Expr p) :=
  match coeffs.reverse with
  | [] | [_] => []
  | cn :: rest =>
    let inner := rest.dropLast  -- [cₙ₋₁, ..., c₁] (skip c₀)
    let (_, quotient) := inner.foldl
      (fun (acc, qs) ci => let q := Expr.add ci (.mul z acc); (q, q :: qs))
      (cn, [cn])
    quotient

end LeanStableHLO.StableHLO.Polynomial
