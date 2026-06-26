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

import LeanStableHLO.KZG
import LeanStableHLO.StableHLO

open LeanStableHLO

/-- BN254 scalar field prime. -/
private abbrev bn254p : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

private instance : NeZero bn254p := ⟨by decide⟩

/-- Convert a `ZMod bn254p` value to its string representation. -/
private def zmodToStr (v : ZMod bn254p) : String :=
  toString v.val

private abbrev bp : Nat := StableHLO.BN254.basePrime

private instance : NeZero bp := ⟨StableHLO.BN254.basePrime_prime.ne_zero⟩

/-- BN254 generator G = (1, 2) as an `AffinePoint bp`. -/
private def bnG : StableHLO.AffinePoint bp :=
  some (.const 1, .const 2)

/-- Serialize an `AffinePoint` for display. -/
private def showPoint (pt : StableHLO.AffinePoint bp) : String :=
  match pt with
  | none => "∞"
  | some (x, y) => s!"({x.eval.val}, {y.eval.val})"

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

  IO.println ""

  -- M4: EC point operations
  IO.println "=== M4: EC Point Operations ==="
  IO.println s!"G = {showPoint bnG}"
  IO.println s!"[5]G = {showPoint (StableHLO.scalarMul 5 bnG)}"

  IO.println ""

  -- M5: KZG commit + prove
  IO.println "=== M5: KZG Commit + Prove ==="
  let srs : StableHLO.KZG.SRS :=
    { g1Points := [bnG,
                   StableHLO.scalarMul 2 bnG,
                   StableHLO.scalarMul 3 bnG,
                   StableHLO.scalarMul 4 bnG] }
  let kzgCoeffs : List (ZMod bn254p) := [1, 2, 3, 4]
  let kzgZ : ZMod bn254p := 5
  let result := StableHLO.KZG.prove kzgCoeffs kzgZ srs
  IO.println s!"C   = {showPoint result.commitment}"
  IO.println s!"v   = {result.evalValue.eval.val}"
  IO.println s!"q   = {(result.quotientCoeffs.map (fun e => e.eval.val))}"
  IO.println s!"π   = {showPoint result.proof}"

  IO.println ""

  -- M6: Pairing field tower
  IO.println "=== M6: Pairing Field Tower ==="
  let a : StableHLO.FieldExt.Fp2 bp := ⟨3, 7⟩
  let b : StableHLO.FieldExt.Fp2 bp := ⟨5, 11⟩
  let c := a * b
  IO.println s!"Fp2: ({a.c0.val}, {a.c1.val}) * ({b.c0.val}, {b.c1.val}) = ({c.c0.val}, {c.c1.val})"
  let aInv := a⁻¹
  let check := a * aInv
  IO.println s!"Fp2: a * a⁻¹ = ({check.c0.val}, {check.c1.val})"

  -- M6: G2 point operations
  IO.println ""
  IO.println "=== M6: G2 Point Operations ==="
  let g2 := StableHLO.ConcretePairing.g2Gen
  match g2 with
  | some (x, y) =>
    IO.println s!"G2.gen.x = ({x.c0.val}, {x.c1.val})"
    IO.println s!"G2.gen.y = ({y.c0.val}, {y.c1.val})"
  | none => IO.println "G2.gen = ∞"
  let g2_2 := StableHLO.ConcretePairing.G2.double g2
  match g2_2 with
  | some (x, y) =>
    IO.println s!"[2]G2.x = ({x.c0.val}, {x.c1.val})"
    IO.println s!"[2]G2.y = ({y.c0.val}, {y.c1.val})"
  | none => IO.println "[2]G2 = ∞"

  -- M6: Miller loop (computable but very slow for large primes)
  IO.println ""
  IO.println "=== M6: Pairing (Miller Loop) ==="
  IO.println "(Pairing computation is available but slow for BN254-size primes)"
  IO.println "e(G1, G2) computation requires optimized Frobenius — deferred to runtime test"
