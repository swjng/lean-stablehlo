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

import LeanPrimeIR.KZG
import LeanPrimeIR.StableHLO

open LeanPrimeIR

/-- BN254 scalar field prime. -/
private abbrev bn254p : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

private instance : NeZero bn254p := ⟨by decide⟩

/-- Convert a `ZMod bn254p` value to its string representation. -/
private def zmodToStr (v : ZMod bn254p) : String :=
  toString v.val

def main : IO Unit := do
  -- M1 string codegen (existing)
  IO.println "=== M1: String Codegen ==="
  IO.println (KZG.evaluateModule [1, 2, 3, 4] 5)

  IO.println ""

  -- M2 deep embedding
  IO.println "=== M2: Deep Embedding ==="
  let coeffs : List (ZMod bn254p) := [1, 2, 3, 4]
  let z : ZMod bn254p := 5
  IO.println (StableHLO.KZG.evaluateModule bn254p coeffs z StableHLO.bn254SFm zmodToStr)
