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

import LeanPrimeIR.StableHLO.FieldExt.CubicExt
import LeanPrimeIR.StableHLO.FieldExt.Fp2

/-!
# Fp6: Cubic Extension over Fp2

F_p⁶ = F_p²[v] / (v³ - ξ), representing elements a₀ + a₁v + a₂v².

Here ξ = 9 + u is the twist parameter in F_p².
Implemented as `CubicExt (Fp2 p) ξ` — all ring/field axioms
are inherited from the generic `CubicExt` proofs.
-/

namespace LeanPrimeIR.StableHLO.FieldExt

/-- F_p⁶ = F_p²[v] / (v³ - ξ) where ξ = 9 + u. -/
abbrev Fp6 (p : Nat) := CubicExt (Fp2 p) (⟨9, 1⟩ : Fp2 p)

variable {p : Nat}

namespace Fp6

-- CommRing: inherited from CubicExt

-- Field: axiom + instField
axiom delta_ne_zero {p : Nat} [Fact (Nat.Prime p)]
    (a : Fp6 p) (ha : a ≠ 0) : CubicExt.delta a ≠ 0

instance [Fact (Nat.Prime p)] : Field (Fp6 p) :=
  CubicExt.instField delta_ne_zero

-- Domain-specific convenience functions

/-- Multiply by v (the degree-1 generator): (0 + 1·v + 0·v²) · a -/
def mulByV (a : Fp6 p) : Fp6 p := (⟨0, 1, 0⟩ : Fp6 p) * a

/-- Embed an Fp2 element into Fp6 at the c0 position. -/
def ofFp2 (x : Fp2 p) : Fp6 p := ⟨x, 0, 0⟩

end Fp6

end LeanPrimeIR.StableHLO.FieldExt
