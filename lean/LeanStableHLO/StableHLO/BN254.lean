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
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# BN254 Curve Parameters

BN254 constants, primality axioms, and Weierstrass curve definition.

Two fields are involved:
- **Base field** (p_base): EC curve coordinate field
- **Scalar field** (p_scalar): polynomial coefficient and scalar mul field

Primality is declared via `axiom` (BN254 is a well-known, independently
verified pairing-friendly curve).
-/

namespace LeanStableHLO.StableHLO.BN254

/-- BN254 base field prime (curve coordinate field). -/
def basePrime : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- BN254 scalar field prime (polynomial coefficient field). -/
def scalarPrime : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Primality axioms: BN254 primes are well-known and independently verified.
axiom basePrime_prime : Nat.Prime basePrime
axiom scalarPrime_prime : Nat.Prime scalarPrime

instance : Fact (Nat.Prime basePrime) := ⟨basePrime_prime⟩
instance : Fact (Nat.Prime scalarPrime) := ⟨scalarPrime_prime⟩

-- NeZero instances (implied by primality, but useful directly)
instance : NeZero basePrime := ⟨Nat.Prime.ne_zero basePrime_prime⟩
instance : NeZero scalarPrime := ⟨Nat.Prime.ne_zero scalarPrime_prime⟩

/-- BN254 short Weierstrass curve: y² = x³ + 3 (a₁=a₂=a₃=a₄=0, a₆=3). -/
noncomputable def curve : WeierstrassCurve (ZMod basePrime) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 3 }

end LeanStableHLO.StableHLO.BN254
