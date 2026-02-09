// Copyright 2026 The PrimeIR Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// ==============================================================================

// Full KZG prove: commit + evaluate + quotient + proof.
//
// p(x) = 1 + 2x + 3x² + 4x³
// SRS: [G, 2G, 3G, 4G]
// z = 5, v = p(5) = 586
// C = 30 * G
// q(x) = 117 + 23x + 4x²
// pi = 117 * G + 23 * 2G + 4 * 3G = (117 + 46 + 12) * G = 175 * G

func.func @printScalar(%val: !SFm) {
  %std = field.from_mont %val : !SF
  %i = field.bitcast %std : !SF -> i256
  %alloc = memref.alloca() : memref<1xi256>
  %c0_idx = arith.constant 0 : index
  memref.store %i, %alloc[%c0_idx] : memref<1xi256>
  %cast = memref.cast %alloc : memref<1xi256> to memref<*xi256>
  func.call @printMemrefI256(%cast) : (memref<*xi256>) -> ()
  return
}

// CHECK-LABEL: @test_kzg_prove
func.func @test_kzg_prove() {
  // === Setup: polynomial coefficients and SRS ===
  %c0 = field.constant 1 : !SFm
  %c1 = field.constant 2 : !SFm
  %c2 = field.constant 3 : !SFm
  %c3 = field.constant 4 : !SFm

  // SRS points: [G, 2G, 3G, 4G]
  %s1 = field.constant 1 : !SF
  %s2 = field.constant 2 : !SF
  %s3 = field.constant 3 : !SF
  %s4 = field.constant 4 : !SF

  %srs0 = func.call @getG1GeneratorMultiple(%s1) : (!SF) -> !affine
  %srs1 = func.call @getG1GeneratorMultiple(%s2) : (!SF) -> !affine
  %srs2 = func.call @getG1GeneratorMultiple(%s3) : (!SF) -> !affine
  %srs3 = func.call @getG1GeneratorMultiple(%s4) : (!SF) -> !affine

  %j_srs0 = elliptic_curve.convert_point_type %srs0 : !affine -> !jacobian
  %j_srs1 = elliptic_curve.convert_point_type %srs1 : !affine -> !jacobian
  %j_srs2 = elliptic_curve.convert_point_type %srs2 : !affine -> !jacobian
  %j_srs3 = elliptic_curve.convert_point_type %srs3 : !affine -> !jacobian

  // === Step 1: Commit C = MSM(SRS, [1,2,3,4]) = 30 * G ===
  %commit_scalars = tensor.from_elements %c0, %c1, %c2, %c3 : tensor<4x!SFm>
  %commit_points = tensor.from_elements %j_srs0, %j_srs1, %j_srs2, %j_srs3 : tensor<4x!jacobian>
  %commitment = elliptic_curve.msm %commit_scalars, %commit_points degree=2 parallel : tensor<4x!SFm>, tensor<4x!jacobian> -> !jacobian
  func.call @printG1AffineFromJacobianMont(%commitment) : (!jacobian) -> ()

  // Verify: C == 30 * G
  %s30 = field.constant 30 : !SF
  %expected_c = func.call @getG1GeneratorMultiple(%s30) : (!SF) -> !affine
  func.call @printG1AffineMont(%expected_c) : (!affine) -> ()

  // === Step 2: Evaluate v = p(5) = 586 (Horner) ===
  %z = field.constant 5 : !SFm
  %h0 = field.mul %c3, %z : !SFm
  %h1 = field.add %h0, %c2 : !SFm
  %h2 = field.mul %h1, %z : !SFm
  %h3 = field.add %h2, %c1 : !SFm
  %h4 = field.mul %h3, %z : !SFm
  %v = field.add %h4, %c0 : !SFm
  func.call @printScalar(%v) : (!SFm) -> ()  // 586

  // === Step 3: Quotient q(x) = [117, 23, 4] (synthetic division) ===
  %q2 = field.constant 4 : !SFm
  %zq2 = field.mul %z, %q2 : !SFm
  %q1 = field.add %c2, %zq2 : !SFm   // 3 + 20 = 23
  %zq1 = field.mul %z, %q1 : !SFm
  %q0 = field.add %c1, %zq1 : !SFm   // 2 + 115 = 117

  // === Step 4: Proof pi = MSM(SRS[0..2], [117, 23, 4]) = 175 * G ===
  %proof_scalars = tensor.from_elements %q0, %q1, %q2 : tensor<3x!SFm>
  %proof_points = tensor.from_elements %j_srs0, %j_srs1, %j_srs2 : tensor<3x!jacobian>
  %proof = elliptic_curve.msm %proof_scalars, %proof_points degree=2 parallel : tensor<3x!SFm>, tensor<3x!jacobian> -> !jacobian
  func.call @printG1AffineFromJacobianMont(%proof) : (!jacobian) -> ()

  // Verify: pi == 175 * G
  %s175 = field.constant 175 : !SF
  %expected_pi = func.call @getG1GeneratorMultiple(%s175) : (!SF) -> !affine
  func.call @printG1AffineMont(%expected_pi) : (!affine) -> ()

  return
}

// Expected output:
// [C_affine]     — 30 * G (from MSM)
// [C_affine]     — 30 * G (direct, should match)
// [586]          — p(5)
// [pi_affine]    — 175 * G (from MSM)
// [pi_affine]    — 175 * G (direct, should match)
