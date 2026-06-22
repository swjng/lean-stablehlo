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
