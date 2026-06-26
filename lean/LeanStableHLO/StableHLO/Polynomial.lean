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
