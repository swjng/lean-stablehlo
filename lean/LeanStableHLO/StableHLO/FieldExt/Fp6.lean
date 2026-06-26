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

import LeanStableHLO.StableHLO.BN254
import LeanStableHLO.StableHLO.FieldExt.CubicExt
import LeanStableHLO.StableHLO.FieldExt.Fp2

/-!
# Fp6: Cubic Extension over Fp2

F_p⁶ = F_p²[v] / (v³ - ξ), representing elements a₀ + a₁v + a₂v².

Here ξ = 9 + u is the twist parameter in F_p².
Implemented as `CubicExt (Fp2 p) ξ` — all ring/field axioms
are inherited from the generic `CubicExt` proofs.
-/

namespace LeanStableHLO.StableHLO.FieldExt

/-- F_p⁶ = F_p²[v] / (v³ - ξ) where ξ = 9 + u. -/
abbrev Fp6 (p : Nat) := CubicExt (Fp2 p) (⟨9, 1⟩ : Fp2 p)

variable {p : Nat}

namespace Fp6

-- CommRing: inherited from CubicExt

-- Field: axiom + instField (restricted to basePrime for soundness)
axiom delta_ne_zero
    (a : Fp6 BN254.basePrime) (ha : a ≠ 0) : CubicExt.delta a ≠ 0

instance : Field (Fp6 BN254.basePrime) :=
  CubicExt.instField delta_ne_zero

-- Domain-specific convenience functions

/-- Multiply by v (the degree-1 generator): (0 + 1·v + 0·v²) · a -/
def mulByV (a : Fp6 p) : Fp6 p := (⟨0, 1, 0⟩ : Fp6 p) * a

/-- Embed an Fp2 element into Fp6 at the c0 position. -/
def ofFp2 (x : Fp2 p) : Fp6 p := ⟨x, 0, 0⟩

end Fp6

end LeanStableHLO.StableHLO.FieldExt
