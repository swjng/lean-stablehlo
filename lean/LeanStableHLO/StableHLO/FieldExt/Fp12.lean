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

import LeanStableHLO.StableHLO.BN254
import LeanStableHLO.StableHLO.FieldExt.QuadExt
import LeanStableHLO.StableHLO.FieldExt.Fp6

/-!
# Fp12: Quadratic Extension over Fp6

F_p¹² = F_p⁶[w] / (w² - v), representing elements a₀ + a₁w.

The reduction rule is w² = v, where v = ⟨0, 1, 0⟩ in Fp6.
Implemented as `QuadExt (Fp6 p) v` — all ring/field axioms
are inherited from the generic `QuadExt` proofs.
-/

namespace LeanStableHLO.StableHLO.FieldExt

/-- F_p¹² = F_p⁶[w] / (w² - v) where v = (0, 1, 0) ∈ Fp6. -/
abbrev Fp12 (p : Nat) := QuadExt (Fp6 p) (⟨0, 1, 0⟩ : Fp6 p)

variable {p : Nat}

namespace Fp12

-- CommRing: inherited from QuadExt

-- Field: axiom + instField (restricted to basePrime for soundness)
axiom norm_ne_zero
    (a : Fp12 BN254.basePrime) (ha : a ≠ 0) : QuadExt.norm a ≠ 0

instance : Field (Fp12 BN254.basePrime) :=
  QuadExt.instField norm_ne_zero

-- Domain-specific functions

/-- Unitary conjugation: a₀ - a₁w. -/
def conj (a : Fp12 p) : Fp12 p := QuadExt.conj a

/-- Cyclotomic squaring (currently naive). -/
def cyclotomicSq (a : Fp12 p) : Fp12 p := a * a

/-- Power by natural number using binary expansion (left-to-right). -/
def powNat (base : Fp12 p) (n : Nat) : Fp12 p :=
  if n = 0 then 1
  else
    let bits := n.bits
    bits.foldl
      (fun (acc, running) bit =>
        let acc' := if bit then acc * running else acc
        let running' := running * running
        (acc', running'))
      (1, base) |>.1

end Fp12

end LeanStableHLO.StableHLO.FieldExt
