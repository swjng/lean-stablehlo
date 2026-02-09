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

// KZG commitment via MSM over BN254.
//
// SRS: [G, 2G, 3G, 4G] where G = (1, 2)
// Coefficients: [1, 2, 3, 4]
// C = 1 * G + 2 * 2G + 3 * 3G + 4 * 4G = (1 + 4 + 9 + 16) * G = 30 * G
//
// Three-way comparison:
//   1. Manual: scalar_mul + add
//   2. MSM: elliptic_curve.msm
//   3. Direct: 30 * G via getG1GeneratorMultiple

// CHECK-LABEL: @test_kzg_commit
func.func @test_kzg_commit() {
  // SRS points: [G, 2G, 3G, 4G]
  %s1 = field.constant 1 : !SF
  %s2 = field.constant 2 : !SF
  %s3 = field.constant 3 : !SF
  %s4 = field.constant 4 : !SF

  %srs0 = func.call @getG1GeneratorMultiple(%s1) : (!SF) -> !affine
  %srs1 = func.call @getG1GeneratorMultiple(%s2) : (!SF) -> !affine
  %srs2 = func.call @getG1GeneratorMultiple(%s3) : (!SF) -> !affine
  %srs3 = func.call @getG1GeneratorMultiple(%s4) : (!SF) -> !affine

  // Polynomial coefficients (scalar field, mont)
  %c0 = field.constant 1 : !SFm
  %c1 = field.constant 2 : !SFm
  %c2 = field.constant 3 : !SFm
  %c3 = field.constant 4 : !SFm

  // === Method 1: Manual scalar_mul + add ===
  %j_srs0 = elliptic_curve.convert_point_type %srs0 : !affine -> !jacobian
  %j_srs1 = elliptic_curve.convert_point_type %srs1 : !affine -> !jacobian
  %j_srs2 = elliptic_curve.convert_point_type %srs2 : !affine -> !jacobian
  %j_srs3 = elliptic_curve.convert_point_type %srs3 : !affine -> !jacobian

  %m0 = elliptic_curve.scalar_mul %c0, %j_srs0 : !SFm, !jacobian -> !jacobian
  %m1 = elliptic_curve.scalar_mul %c1, %j_srs1 : !SFm, !jacobian -> !jacobian
  %m2 = elliptic_curve.scalar_mul %c2, %j_srs2 : !SFm, !jacobian -> !jacobian
  %m3 = elliptic_curve.scalar_mul %c3, %j_srs3 : !SFm, !jacobian -> !jacobian

  %a01 = elliptic_curve.add %m0, %m1 : !jacobian, !jacobian -> !jacobian
  %a23 = elliptic_curve.add %m2, %m3 : !jacobian, !jacobian -> !jacobian
  %manual = elliptic_curve.add %a01, %a23 : !jacobian, !jacobian -> !jacobian
  func.call @printG1AffineFromJacobianMont(%manual) : (!jacobian) -> ()

  // === Method 2: MSM ===
  %scalars = tensor.from_elements %c0, %c1, %c2, %c3 : tensor<4x!SFm>
  %points = tensor.from_elements %j_srs0, %j_srs1, %j_srs2, %j_srs3 : tensor<4x!jacobian>
  %msm = elliptic_curve.msm %scalars, %points degree=2 parallel : tensor<4x!SFm>, tensor<4x!jacobian> -> !jacobian
  func.call @printG1AffineFromJacobianMont(%msm) : (!jacobian) -> ()

  // === Method 3: Direct 30 * G ===
  %s30 = field.constant 30 : !SF
  %direct = func.call @getG1GeneratorMultiple(%s30) : (!SF) -> !affine
  func.call @printG1AffineMont(%direct) : (!affine) -> ()

  return
}

// Expected: all three outputs should be the same affine point (30 * G)
