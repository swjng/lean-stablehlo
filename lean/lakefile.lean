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
