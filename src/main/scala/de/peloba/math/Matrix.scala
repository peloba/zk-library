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

import it.unisa.dia.gas.jpbc.{Field, Element}
import zk.CommonReferenceString
import java.io.{ObjectOutputStream, ObjectInputStream, Serializable}
import java.lang.{IllegalArgumentException, IndexOutOfBoundsException, Exception}

/**
 * A class representing a matrix. Note that we start with (1, 1)
 * in the top left corner; this data structure tries to be immutable so all
 * modifying operations except set(...) return a new matrix object
 */
class Matrix(val numberOfRows: Int, val numberOfCols: Int, @transient var field: Field[_ <: Element],
             @transient initializationValue: Element, @transient randomInit: Boolean) extends Serializable {

	def this(numberOfRows: Int, numberOfCols: Int, field: Field[_ <: Element]) =
		this(numberOfRows, numberOfCols, field, field.newZeroElement(), false)

	def this(numberOfRows: Int, numberOfCols: Int, initializationValue: Element) =
		this(numberOfRows, numberOfCols, initializationValue.getField, initializationValue, false)

	def this(numberOfRows: Int, numberOfCols: Int, field: Field[_ <: Element], x: Boolean) =
		this(numberOfRows, numberOfCols, field, field.newZeroElement(), true)

	private var dataBuff: Array[Byte] = null
	private var groupID: String = null

	def setGroup(s: String) {
		if (s == null) {
			groupID = null
		} else {
			groupID = new String(s)
		}
	}

	def getGroup = groupID

	@transient private var data = Array.ofDim[Element](numberOfRows, numberOfCols)

	{
		if (randomInit) {
			for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
				set(i, j, field.newRandomElement())
		} else {
			for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
				set(i, j, initializationValue)
		}
	}

	def flatten = {
		if (numberOfRows != 1 || numberOfCols != 1)
			throw new Exception("Cannot flatten a non 1x1 Matrix")

		apply(1, 1)
	}

	def numRows() = {
		numberOfRows
	}

	def numCols() = {
		numberOfCols
	}

	def F(crs: CommonReferenceString, otherMatrix: Matrix) = {
		if (numberOfRows != 2 || numberOfCols != 1 || otherMatrix.numberOfRows != 2 || otherMatrix.numberOfCols != 1)
			throw new Exception("Matrices do not have 2x1 dimensions to apply F")

		if (!field.equals(crs.G1) || !otherMatrix.field.equals(crs.G2))
			throw new Exception("The two matrices have wrong groups")

		val res = new Matrix(2, 2, crs.pairing.getGT)
		res.set(1, 1, crs.pairing.pairing(apply(1, 1).duplicate(), otherMatrix(1, 1).duplicate()))
		res.set(1, 2, crs.pairing.pairing(apply(1, 1).duplicate(), otherMatrix(2, 1).duplicate()))
		res.set(2, 1, crs.pairing.pairing(apply(2, 1).duplicate(), otherMatrix(1, 1).duplicate()))
		res.set(2, 2, crs.pairing.pairing(apply(2, 1).duplicate(), otherMatrix(2, 1).duplicate()))

		res
	}

	/**
	 * Multiplies this matrix with another matrix
	 */
	def *(otherMatrix: Matrix): Matrix = {
		if (numberOfCols != otherMatrix.numberOfRows)
			throw new Exception("The matrix dimensions do not match")

		if (!field.equals(otherMatrix.field))
			throw new Exception("The fields of the matrices do not match")

		val res = new Matrix(numberOfRows, otherMatrix.numberOfCols, field)
		for (i <- 1 to numberOfRows; j <- 1 to otherMatrix.numberOfCols) {
			val tmp = field.newZeroElement()

			for (k <- 1 to numberOfCols) {
				tmp.add(this(i, k).duplicate.mul(otherMatrix(k, j)))
			}

			res.set(i, j, tmp)
		}

		res
	}

	def *(otherMatrix: FatMatrix): FatMatrix = {
		if (numberOfCols != otherMatrix.numberOfRows)
			throw new Exception("The matrix dimensions do not match")

		/*if(!field.equals(otherMatrix.field))
			throw new Exception("The fields of the matrices do not match")*/

		val res = new FatMatrix(numberOfRows, otherMatrix.numberOfCols, otherMatrix.innerNumberOfRows, otherMatrix.innerNumberOfCols, otherMatrix.field)
		for (i <- 1 to numberOfRows; j <- 1 to otherMatrix.numberOfCols) {
			var tmp = new Matrix(otherMatrix.innerNumberOfRows, otherMatrix.innerNumberOfCols, otherMatrix.field.newZeroElement())

			for (k <- 1 to numberOfCols) {
				tmp = tmp + (otherMatrix(k, j) * this(i, k))
			}

			res.set(i, j, tmp)
		}

		res
	}

	def map(f: Element => Element) = {
		val res = new Matrix(numberOfRows, numberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, f(this(i, j).duplicate))

		res
	}

	def fatMap(innerNumberOfRows: Int, innerNumberOfCols: Int, targetField: Field[_ <: Element], f: Element => Matrix) = {
		val res = new FatMatrix(numberOfRows, numberOfCols, innerNumberOfRows, innerNumberOfCols, targetField)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, f(this(i, j).duplicate))

		res
	}

	def rowAsMatrix(rowId: Int) = {
		val res = new Matrix(1, numberOfCols, field)
		(1 to numberOfCols).foreach(i => res.set(1, i, this(rowId, i)))
		res
	}

	def replaceRowFromMatrix(rowId: Int, matrix: Matrix): Matrix = replaceRowFromMatrix(rowId, matrix, 1)

	def replaceRowFromMatrix(rowId: Int, matrix: Matrix, otherRowId: Int): Matrix = {
		(1 to numberOfCols).foreach(i => set(rowId, i, matrix(otherRowId, i)))
		this
	}

	/**
	 * Scalar multiplication
	 */
	def *(value: Element): Matrix = {
		val res = new Matrix(numberOfRows, numberOfCols, field)
		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, this(i, j).duplicate().mulZn(value))

		res
	}

	def +(otherMatrix: Matrix) = pairMap(otherMatrix, (e1, e2) => e1.add(e2))

	def -(otherMatrix: Matrix) = pairMap(otherMatrix, (e1, e2) => e1.sub(e2))

	def pairMap(otherMatrix: Matrix, f: (Element, Element) => Element) = {
		if (numberOfRows != otherMatrix.numberOfRows || numberOfCols != otherMatrix.numberOfCols)
			throw new Exception("The Matrix dimensions do not match")

		if (!field.equals(otherMatrix.field))
			throw new Exception("The field of the two matrices do not match")

		val res = new Matrix(numberOfRows, numberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, f(this(i, j).duplicate, otherMatrix(i, j).duplicate))

		res
	}

	/**
	 * Returns a new matrix which is the transposed version of
	 * the original matrix
	 */
	def transpose = {
		val res = new Matrix(numberOfCols, numberOfRows, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.setUntouched_!(j, i, this(i, j))

		res
	}

	/**
	 * Gets the value of a specific coordinate
	 */
	def apply(rowId: Int, colId: Int) = {
		if (rowId > numberOfRows || colId > numberOfCols)
			throw new IndexOutOfBoundsException("Trying to access " + rowId + "/" + colId + " but maximum is " + numberOfRows + "/" + numberOfCols)

		data(rowId - 1)(colId - 1)
	}

	def get(rowId: Int, colId: Int) = apply(rowId, colId)

	/**
	 * Sets a specific coordinate to a new value; the value is forced to be immutable
	 */
	def set(rowId: Int, colId: Int, newValue: Element) = {
		setUntouched_!(rowId, colId, newValue.duplicate())
	}

	/**
	 * Sets a specific coordinate to a new value; this value is NOT forced to be
	 * immutable so use with care
	 */
	protected def setUntouched_!(rowId: Int, colId: Int, newValue: Element) = {
		if (!newValue.getField.equals(field))
			throw new Exception("Cannot set matrix element: wrong field")

		data(rowId - 1).update(colId - 1, newValue)
		this
	}

	def setFromBytes(data: Array[Byte]): Matrix = setFromBytes(data, 0)

	def setFromBytes(data: Array[Byte], offset: Int): Matrix = {
		var _offset = offset
		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols) {
			val element = field.newElement()
			_offset += element.setFromBytes(data, _offset)
			set(i, j, element)
		}
		this
	}

	def toBytes: Array[Byte] = {
		data.flatMap(_.flatMap(_.toBytes))
	}

	def duplicate = {
		val res = new Matrix(numberOfRows, numberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, this(i, j).duplicate)

		res.setGroup(getGroup)

		res
	}

	def isEqual(otherMatrix: Matrix) = {
		(numberOfRows == otherMatrix.numberOfRows && numberOfCols == otherMatrix.numberOfCols && {
			var res = true

			for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
				res = res && this(i, j).isEqual(otherMatrix(i, j))

			res
		})
	}

	override def toString = {
		"[" + data.indices.map(i => data(i).indices.map(j => "(" + (i + 1) + "/" + (j + 1) + ") = " + data(i)(j).toString)).flatten.mkString(", ") + "]"
	}

	private def writeObject(out: ObjectOutputStream) {
		if (groupID == null) {
			throw new IllegalArgumentException("Matrix.writeObject: groupID not set")
		}

		dataBuff = toBytes

		out.defaultWriteObject()
	}

	private def readObject(in: ObjectInputStream) {
		in.defaultReadObject()

		val crs = CommonReferenceString.getInstance()

		if (groupID.compareTo("G1") == 0) {
			field = crs.pairing.getG1
		} else if (groupID.compareTo("G2") == 0) {
			field = crs.pairing.getG2
		} else if (groupID.compareTo("Zr") == 0) {
			field = crs.pairing.getZr
		} else {
			throw new IllegalArgumentException("Matrix.readObject: given groupID invalid")
		}

		data = Array.ofDim[Element](numberOfRows, numberOfCols)

		setFromBytes(dataBuff)

		dataBuff = null
	}
}

object Matrix {
	def fromMatrixArray(arr: Array[Matrix], numCols: Int, field: Field[_ <: Element]): Matrix = {
		val Iarr = new Array[Int](arr.length)

		for (i <- 1 to arr.length) {
			Iarr.update(i - 1, i)
		}

		fromMatrixArray(arr, numCols, field, Iarr)
	}

	/* only use with nx1 matrices
	* TODO: fix so that it works for all kinds of matrices */
	def fromMatrixArray(arr: Array[Matrix], numCols: Int, field: Field[_ <: Element], Iarr: Array[Int]): Matrix = {

		val res = new Matrix(Iarr.length, numCols, field)

		for (i <- 1 to Iarr.length) {
			if (arr(Iarr(i - 1) - 1) == null) {
				res.replaceRowFromMatrix(i, new Matrix(1, numCols, field.newZeroElement()))
			} else if (arr(Iarr(i - 1) - 1).numRows != 1 || arr(Iarr(i - 1) - 1).numCols != numCols) {
				throw new IllegalArgumentException("Matrix(Array[Matrix]): Matrix Dimensions inconsistent")
			} else {
				res.replaceRowFromMatrix(i, arr(Iarr(i - 1) - 1))
			}
		}

		res
	}

	def fromElementArray(arr: Array[Element], field: Field[_ <: Element]): Matrix = {
		val Iarr = new Array[Int](arr.length)

		for (i <- 1 to arr.length) {
			Iarr.update(i - 1, i)
		}

		fromElementArray(arr, field, Iarr)
	}

	def fromElementArray(arr: Array[Element], field: Field[_ <: Element], Iarr: Array[Int]): Matrix = {
		val res = new Matrix(Iarr.length, 1, field)

		for (i <- 1 to Iarr.length) {
			if (arr(Iarr(i - 1) - 1) == null) {
				res.set(i, 1, field.newZeroElement())
			} else {
				res.set(i, 1, arr(Iarr(i - 1) - 1))
			}
		}

		res
	}

	def getMatrixArray(m: Matrix): Array[Matrix] = {
		val res = new Array[Matrix](m.numRows())

		for (i <- 1 to res.length) {
			res.update(i - 1, m.rowAsMatrix(i))
		}

		res
	}

	def getMatrixArray(m: Array[Element], field: Field[_ <: Element]): Array[Matrix] = {
		getMatrixArray(fromElementArray(m, field))
	}

	def getRandomMatrix(nR: Int, nC: Int, field: Field[_ <: Element]) = {
		new Matrix(nR, nC, field, true)
	}
}
