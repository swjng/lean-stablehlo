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

import Lake
open Lake DSL

package «lean-stablehlo» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.27.0"

@[default_target]
lean_lib «LeanStableHLO» where
  srcDir := "."

lean_exe «lean-stablehlo» where
  root := `Main

lean_exe «pairing-test» where
  root := `PairingTest
