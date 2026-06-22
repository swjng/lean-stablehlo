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
