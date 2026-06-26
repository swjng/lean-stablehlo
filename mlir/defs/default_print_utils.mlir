// Copyright (C) 2025 Soowon Jeong.
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

func.func private @printMemrefI32(memref<*xi32>) attributes { llvm.emit_c_interface }
func.func private @printMemrefI64(memref<*xi64>) attributes { llvm.emit_c_interface }
func.func private @printMemrefI256(memref<*xi256>) attributes { llvm.emit_c_interface }
