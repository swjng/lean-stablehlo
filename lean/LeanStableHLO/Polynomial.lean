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

import LeanStableHLO.Field

namespace LeanStableHLO.Polynomial

/-- Horner evaluation of polynomial at point z.
    Given coefficients [c₀, c₁, ..., cₙ] and point z,
    computes p(z) = (...((cₙ * z + cₙ₋₁) * z + cₙ₋₂)...) * z + c₀ -/
def hornerEval (coeffs : List Value) (z : Value) : IRBuilder Value := do
  match coeffs.reverse with
  | [] => Field.const 0
  | [c] => return c
  | cn :: rest =>
    let mut acc := cn
    for ci in rest do
      let t ← Field.mul acc z
      acc ← Field.add t ci
    return acc

/-- Synthetic division: compute quotient q(x) = (p(x) - p(z)) / (x - z).
    Given coefficients [c₀, c₁, ..., cₙ] (ascending) and point z,
    returns quotient coefficients [q₀, q₁, ..., qₙ₋₁] (ascending).

    Algorithm (descending):
      qₙ₋₁ = cₙ
      qᵢ₋₁ = cᵢ + z * qᵢ  for i = n-1, ..., 1 -/
def syntheticDiv (coeffs : List Value) (z : Value) : IRBuilder (List Value) := do
  match coeffs.reverse with
  | [] | [_] => return []
  | cn :: rest =>
    -- rest = [cₙ₋₁, cₙ₋₂, ..., c₁, c₀] (descending, but we skip c₀)
    let inner := rest.dropLast  -- [cₙ₋₁, cₙ₋₂, ..., c₁]
    let mut acc := cn
    let mut quotient : List Value := [acc]
    for ci in inner do
      let t ← Field.mul z acc
      acc ← Field.add ci t
      quotient := acc :: quotient
    -- quotient is [q₀, q₁, ..., qₙ₋₁] after reversal from construction
    return quotient

end LeanStableHLO.Polynomial
