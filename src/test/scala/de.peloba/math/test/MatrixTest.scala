/**
 * The peloba zero-knowledge library
 * Copyright (C) 2013 peloba UG & Co. KG
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.peloba
package math
package test

import de.peloba.zk.CommonReferenceString
import org.scalatest.FunSpec

class MatrixTest extends FunSpec {
	val crs = CommonReferenceString.generate("typeD_224_496659")

	describe("A matrix") {
		it("should be correctly created") {
			val matrix = new Matrix(5, 3, crs.Zr)
			assert(matrix.numberOfRows === 5)
			assert(matrix.numberOfCols === 3)
			assert(matrix.field.equals(crs.Zr))
			assert(matrix(1, 1).isEqual(crs.Zr.newZeroElement()))
			intercept[Exception] {
				matrix(6, 1)
			}
		}

		it("should correctly compute addition with another matrix") {
			val matrix1 = new Matrix(3, 2, crs.Zr)
			matrix1.set(1, 1, crs.Zr.newElement(3))
			matrix1.set(1, 2, crs.Zr.newElement(7))
			matrix1.set(2, 1, crs.Zr.newElement(56))
			matrix1.set(2, 2, crs.Zr.newElement(14))
			matrix1.set(3, 1, crs.Zr.newElement(23))
			matrix1.set(3, 2, crs.Zr.newElement(19))

			val matrix2 = new Matrix(3, 2, crs.Zr)
			matrix2.set(1, 1, crs.Zr.newElement(14))
			matrix2.set(1, 2, crs.Zr.newElement(94))
			matrix2.set(2, 1, crs.Zr.newElement(26))
			matrix2.set(2, 2, crs.Zr.newElement(59))
			matrix2.set(3, 1, crs.Zr.newElement(345))
			matrix2.set(3, 2, crs.Zr.newElement(23))

			val res = matrix1 + matrix2

			assert(res(1, 1).toBigInteger.toString === "17")
			assert(res(1, 2).toBigInteger.toString === "101")
			assert(res(2, 1).toBigInteger.toString === "82")
			assert(res(2, 2).toBigInteger.toString === "73")
			assert(res(3, 1).toBigInteger.toString === "368")
			assert(res(3, 2).toBigInteger.toString === "42")
		}

		it("should not compute addition with another matrix of wrong dimensions") {
			val matrix1 = new Matrix(3, 2, crs.Zr)
			val matrix2 = new Matrix(3, 3, crs.Zr)

			intercept[Exception] {
				matrix1 + matrix2
			}
		}

		it("should not compute addition with another matrix of the wrong field") {
			val matrix1 = new Matrix(3, 2, crs.Zr)
			val matrix2 = new Matrix(3, 2, crs.G1)

			intercept[Exception] {
				matrix1 + matrix2
			}
		}

		it("should correctly compute multiplication with another matrix") {
			val matrix1 = new Matrix(3, 2, crs.Zr)
			matrix1.set(1, 1, crs.Zr.newElement(3))
			matrix1.set(1, 2, crs.Zr.newElement(7))
			matrix1.set(2, 1, crs.Zr.newElement(56))
			matrix1.set(2, 2, crs.Zr.newElement(14))
			matrix1.set(3, 1, crs.Zr.newElement(23))
			matrix1.set(3, 2, crs.Zr.newElement(19))

			val matrix2 = new Matrix(2, 3, crs.Zr)
			matrix2.set(1, 1, crs.Zr.newElement(14))
			matrix2.set(1, 2, crs.Zr.newElement(94))
			matrix2.set(1, 3, crs.Zr.newElement(26))
			matrix2.set(2, 1, crs.Zr.newElement(59))
			matrix2.set(2, 2, crs.Zr.newElement(345))
			matrix2.set(2, 3, crs.Zr.newElement(23))

			val res = matrix1 * matrix2

			assert(res.numberOfRows === 3)
			assert(res.numberOfCols === 3)
			assert(res(1, 1).toBigInteger.toString === "455")
			assert(res(2, 3).toBigInteger.toString === "1778")
		}

		it("should correctly compute scalar multiplication") {
			val scalar = crs.Zr.newElement(81)
			val matrix1 = new Matrix(3, 2, crs.Zr)
			matrix1.set(1, 1, crs.Zr.newElement(3))
			matrix1.set(1, 2, crs.Zr.newElement(7))
			matrix1.set(2, 1, crs.Zr.newElement(56))
			matrix1.set(2, 2, crs.Zr.newElement(14))
			matrix1.set(3, 1, crs.Zr.newElement(23))
			matrix1.set(3, 2, crs.Zr.newElement(19))

			val res = matrix1 * scalar

			assert(res(1, 1).toBigInteger.toString === "243")
			assert(res(3, 2).toBigInteger.toString === "1539")
		}
	}
}