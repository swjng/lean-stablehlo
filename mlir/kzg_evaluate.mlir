// Copyright (C) 2026 Soowon Jeong.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
// ==============================================================================

// KZG polynomial evaluation and synthetic division over BN254 scalar field.
//
// Test vector: p(x) = 1 + 2x + 3x² + 4x³, z = 5
//   Horner:    v = ((4 * 5 + 3) * 5 + 2) * 5 + 1 = 586
//   Quotient:  q₂ = 4, q₁ = 3 + 5 * 4 = 23, q₀ = 2 + 5 * 23 = 117
//   Verify:    q(7) * (7 - 5) == p(7) - 586 → 474 * 2 == 948

func.func @printScalar(%val: !SFm) {
  %std = field.from_mont %val : !SF
  %i = field.bitcast %std : !SF -> i256
  %alloc = memref.alloca() : memref<1xi256>
  %c0 = arith.constant 0 : index
  memref.store %i, %alloc[%c0] : memref<1xi256>
  %cast = memref.cast %alloc : memref<1xi256> to memref<*xi256>
  func.call @printMemrefI256(%cast) : (memref<*xi256>) -> ()
  return
}

// CHECK-LABEL: @test_kzg_evaluate
func.func @test_kzg_evaluate() {
  // Polynomial coefficients: p(x) = 1 + 2x + 3x² + 4x³
  %c0 = field.constant 1 : !SFm
  %c1 = field.constant 2 : !SFm
  %c2 = field.constant 3 : !SFm
  %c3 = field.constant 4 : !SFm

  // Evaluation point z = 5
  %z = field.constant 5 : !SFm

  // === Horner evaluation: v = ((c₃ * z + c₂) * z + c₁) * z + c₀ ===
  // Step 1: acc = c₃ * z + c₂ = 4 * 5 + 3 = 23
  %h0 = field.mul %c3, %z : !SFm
  %h1 = field.add %h0, %c2 : !SFm
  // Step 2: acc = acc * z + c₁ = 23 * 5 + 2 = 117
  %h2 = field.mul %h1, %z : !SFm
  %h3 = field.add %h2, %c1 : !SFm
  // Step 3: acc = acc * z + c₀ = 117 * 5 + 1 = 586
  %h4 = field.mul %h3, %z : !SFm
  %v = field.add %h4, %c0 : !SFm

  // Print p(5) = 586
  func.call @printScalar(%v) : (!SFm) -> ()

  // === Synthetic division: q(x) = (p(x) - v) / (x - z) ===
  // q₂ = c₃ = 4
  // q₁ = c₂ + z * q₂ = 3 + 5 * 4 = 23
  // q₀ = c₁ + z * q₁ = 2 + 5 * 23 = 117
  %q2 = field.constant 4 : !SFm
  %zq2 = field.mul %z, %q2 : !SFm
  %q1 = field.add %c2, %zq2 : !SFm   // 3 + 20 = 23
  %zq1 = field.mul %z, %q1 : !SFm
  %q0 = field.add %c1, %zq1 : !SFm   // 2 + 115 = 117

  // Print quotient coefficients
  func.call @printScalar(%q0) : (!SFm) -> ()   // 117
  func.call @printScalar(%q1) : (!SFm) -> ()   // 23
  func.call @printScalar(%q2) : (!SFm) -> ()   // 4

  // === Verification: q(7) * (7 - 5) == p(7) - v ===
  %seven = field.constant 7 : !SFm
  %five = field.constant 5 : !SFm

  // q(7) = 117 + 23 * 7 + 4 * 49 = 117 + 161 + 196 = 474
  %q7_t0 = field.mul %q1, %seven : !SFm
  %q7_t1 = field.add %q0, %q7_t0 : !SFm
  %seven_sq = field.mul %seven, %seven : !SFm
  %q7_t2 = field.mul %q2, %seven_sq : !SFm
  %q7 = field.add %q7_t1, %q7_t2 : !SFm

  // (7 - 5) = 2
  %diff = field.sub %seven, %five : !SFm

  // LHS = q(7) * 2 = 474 * 2 = 948
  %lhs = field.mul %q7, %diff : !SFm

  // p(7) = 1 + 14 + 147 + 1372 = 1534
  %p7_t0 = field.mul %c1, %seven : !SFm
  %p7_t1 = field.add %c0, %p7_t0 : !SFm
  %p7_t2 = field.mul %c2, %seven_sq : !SFm
  %p7_t3 = field.add %p7_t1, %p7_t2 : !SFm
  %seven_cu = field.mul %seven_sq, %seven : !SFm
  %p7_t4 = field.mul %c3, %seven_cu : !SFm
  %p7 = field.add %p7_t3, %p7_t4 : !SFm

  // RHS = p(7) - v = 1534 - 586 = 948
  %rhs = field.sub %p7, %v : !SFm

  // Print LHS and RHS (should both be 948)
  func.call @printScalar(%lhs) : (!SFm) -> ()  // 948
  func.call @printScalar(%rhs) : (!SFm) -> ()  // 948

  return
}

// Expected output:
// [586]
// [117]
// [23]
// [4]
// [948]
// [948]
