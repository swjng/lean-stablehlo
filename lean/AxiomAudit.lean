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

import LeanStableHLO

/-!
# Axiom audit

Machine-checkable record of the axiom base behind the headline theorems.
Run with:

    lake env lean AxiomAudit.lean

Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are expected
everywhere. Anything else is a project axiom; see the "Trust model and axiom
base" section of `README.md` for what each one means and why it is (or is not
yet) discharged.

Expected highlights:
* `evaluate_correct` — NO custom axioms (the polynomial/evaluation layer is
  fully verified from first principles).
* `kzg_correctness` / `kzg_end_to_end` / `evaluation_binding` — depend on the
  named pairing axioms (`e_smul_*`, `e_add_*`), the order-`r` power axioms, the
  elliptic-curve group laws, and field-tower / primality axioms.
-/

open LeanStableHLO.StableHLO
open LeanStableHLO.StableHLO.KZG

#print axioms evaluate_correct
#print axioms kzg_correctness
#print axioms kzg_end_to_end
#print axioms evaluation_binding
#print axioms polynomial_binding_security
