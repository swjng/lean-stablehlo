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
