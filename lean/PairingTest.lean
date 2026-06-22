import LeanStableHLO

open LeanStableHLO.StableHLO

/-- Compiled diagnostic harness for the concrete BN254 pairing.
    Run with `lake exe pairing-test`. -/

abbrev FP := Option (ZMod BN254.basePrime × ZMod BN254.basePrime)

def P : FP := some (1, 2)
def Q : ConcretePairing.G2Point := ConcretePairing.g2Gen

def e (a : FP) (b : ConcretePairing.G2Point) : FieldExt.Fp12 BN254.basePrime :=
  ConcretePairing.ate a b

def main : IO Unit := do
  let r := BN254.scalarPrime
  let base := e P Q
  IO.println s!"nondeg  e(P,Q) != 1        : {base != 1}"
  IO.println s!"in_mu_r e(P,Q)^r == 1      : {FieldExt.Fp12.powNat base r == 1}"
  -- G1-linearity
  let e2P := e (Pairing.G1.scalarMulNat 2 P) Q
  let e3P := e (Pairing.G1.scalarMulNat 3 P) Q
  IO.println s!"bilinG1 e([2]P,Q) == e^2   : {e2P == base * base}"
  IO.println s!"bilinG1 e([3]P,Q) == e^3   : {e3P == base * base * base}"
  -- G2-linearity
  let e2Q := e P (ConcretePairing.G2.scalarMul 2 Q)
  let e3Q := e P (ConcretePairing.G2.scalarMul 3 Q)
  IO.println s!"bilinG2 e(P,[2]Q) == e^2   : {e2Q == base * base}"
  IO.println s!"bilinG2 e(P,[3]Q) == e^3   : {e3Q == base * base * base}"
  -- cross check
  IO.println s!"cross   e([2]P,Q)==e(P,[2]Q): {e2P == e2Q}"
  -- mixed bilinearity and a larger scalar
  let e6 := FieldExt.Fp12.powNat base 6
  let eMix := e (Pairing.G1.scalarMulNat 2 P) (ConcretePairing.G2.scalarMul 3 Q)
  IO.println s!"mixed   e([2]P,[3]Q) == e^6: {eMix == e6}"
  let e7P := e (Pairing.G1.scalarMulNat 7 P) Q
  IO.println s!"bilinG1 e([7]P,Q) == e^7   : {e7P == FieldExt.Fp12.powNat base 7}"
