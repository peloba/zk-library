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
import java.lang.Exception
import java.io.{ObjectInputStream, ObjectOutputStream, Serializable}

class FatMatrix(val numberOfRows: Int, val numberOfCols: Int, @transient initializationValue: Matrix) extends Serializable {
	def this(numberOfRows: Int, numberOfCols: Int, innerNumberOfRows: Int, innerNumberOfCols: Int, @transient field: Field[_ <: Element]) = this(numberOfRows, numberOfCols, new Matrix(innerNumberOfRows, innerNumberOfCols, field))

	def numRows() = {
		numberOfRows
	}

	def numCols() = {
		numberOfCols
	}

	def iNumRows() = {
		innerNumberOfRows
	}

	def iNumCols() = {
		innerNumberOfCols
	}

	private val data = Array.ofDim[Matrix](numberOfRows, numberOfCols)
	@transient var field = initializationValue.field
	val innerNumberOfRows = initializationValue.numberOfRows
	val innerNumberOfCols = initializationValue.numberOfCols

	{
		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			set(i, j, initializationValue.duplicate)
	}

	def set(rowId: Int, colId: Int, newValue: Matrix) = {
		setUntouched_!(rowId, colId, newValue.duplicate)
	}

	def map(f: Matrix => Matrix) = {
		val res = new FatMatrix(numberOfRows, numberOfCols, innerNumberOfRows, innerNumberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, f(this(i, j).duplicate))

		res
	}

	def fatPoint(crs: CommonReferenceString, otherMatrix: FatMatrix) = {
		if (numberOfCols != 1 || otherMatrix.numberOfCols != 1 || numberOfRows != otherMatrix.numberOfRows)
			throw new Exception("The matrix dimensions do not match for fatPoint")

		var res = new Matrix(2, 2, crs.Gt)

		for (i <- 1 to numberOfRows)
			res = res + this(i, 1).F(crs, otherMatrix(i, 1))

		res
	}

	def flatten = {
		if (numberOfRows != 1 || numberOfCols != 1)
			throw new Exception("Cannot flatten a non 1x1 FatMatrix")

		this(1, 1)
	}

	def duplicate() = {
		/* this may break if the matrix is empty*/
		val res = new FatMatrix(numberOfRows, numberOfCols, get(1, 1))

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols) {
			res.set(i, j, get(i, j))
		}

		res.setGroup(getGroup)

		res
	}

	def +(otherMatrix: FatMatrix) = pairMap(otherMatrix, (m1, m2) => m1 + m2)

	def -(otherMatrix: FatMatrix) = pairMap(otherMatrix, (m1, m2) => m1 - m2)

	def pairMap(otherMatrix: FatMatrix, f: (Matrix, Matrix) => Matrix) = {
		if (numberOfRows != otherMatrix.numberOfRows || numberOfCols != otherMatrix.numberOfCols)
			throw new Exception("The matrix dimensions do not match")

		if (innerNumberOfRows != otherMatrix.innerNumberOfRows || innerNumberOfCols != otherMatrix.innerNumberOfCols) {
			/*
			System.out.println("iNR: " + innerNumberOfRows)
			System.out.println("iNC: " + innerNumberOfCols)
			System.out.println("o-iNR: " + innerNumberOfRows)
			System.out.println("o-iNC: " + otherMatrix.innerNumberOfCols)
			 */
			throw new Exception("The inner matrix dimensions do not match")
		}

		if (!field.getClass.equals(otherMatrix.field.getClass))
			throw new Exception("The field of the two matrices do not match")

		val res = new FatMatrix(numberOfRows, numberOfCols, innerNumberOfRows, innerNumberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.set(i, j, f(this(i, j).duplicate, otherMatrix(i, j).duplicate))

		res
	}

	def transpose = {
		val res = new FatMatrix(numberOfCols, numberOfRows, innerNumberOfRows, innerNumberOfCols, field)

		for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
			res.setUntouched_!(j, i, this(i, j))

		res
	}

	def isEqual(otherMatrix: FatMatrix) = {
		(numberOfRows == otherMatrix.numberOfRows && numberOfCols == otherMatrix.numberOfCols && {
			var res = true

			for (i <- 1 to numberOfRows; j <- 1 to numberOfCols)
				res = res && this(i, j).isEqual(otherMatrix(i, j))

			res
		})
	}

	def apply(rowId: Int, colId: Int) = {
		if (rowId > numberOfRows || colId > numberOfCols)
			throw new IndexOutOfBoundsException("Trying to access " + rowId + "/" + colId + " but maximum is " + numberOfRows + "/" + numberOfCols)

		data(rowId - 1)(colId - 1)
	}

	def get(rowId: Int, colId: Int) = apply(rowId, colId)

	/**
	 * Sets a specific coordinate to a new value; this value is NOT forced to be
	 * immutable so use with care
	 */
	protected def setUntouched_!(rowId: Int, colId: Int, newValue: Matrix) = {
		if (!field.getClass.equals(newValue.field.getClass))
			throw new Exception("The matrix fields do not match")

		data(rowId - 1).update(colId - 1, newValue)
		this
	}


	override def toString = {
		"[" + data.indices.map(i => data(i).indices.map(j => "(" + (i + 1) + "/" + (j + 1) + ") = " + data(i)(j).toString)).flatten.mkString(", ") + "]"
	}

	var groupID: String = null

	def setGroup(s: String) {
		groupID = new String(s)
	}

	def getGroup = {
		groupID
	}

	def rowAsFatMatrix(rowId: Int) = {
		val res = new FatMatrix(1, numberOfCols, innerNumberOfRows, innerNumberOfCols, field)
		(1 to numberOfCols).foreach(i => res.set(1, i, this(rowId, i)))
		res
	}

	def replaceRowFromFatMatrix(rowId: Int, matrix: FatMatrix, otherRowId: Int): FatMatrix = {
		(1 to numberOfCols).foreach(i => set(rowId, i, matrix(otherRowId, i)))
		this
	}

	private def writeObject(out: ObjectOutputStream) {
		if (groupID == null) {
			throw new IllegalArgumentException("FatMatrix.writeObject: groupID not set")
		}

		for (i <- 0 to numRows() - 1; j <- 0 to numCols() - 1) {
			data(i)(j).setGroup(groupID)
		}

		out.defaultWriteObject()
	}

	private def readObject(in: ObjectInputStream) {
		in.defaultReadObject()
		// don't think we need anything else here
		val crs = CommonReferenceString.getInstance()

		if (groupID.compareTo("G1") == 0) {
			field = crs.pairing.getG1
		} else if (groupID.compareTo("G2") == 0) {
			field = crs.pairing.getG2
		} else if (groupID.compareTo("Zr") == 0) {
			field = crs.pairing.getZr
		} else {
			throw new IllegalArgumentException("FatMatrix.readObject: given groupID invalid")
		}
	}
}

object FatMatrix {
	def fromFatMatrixArray(arr: Array[FatMatrix], numCols: Int, iNumRows: Int, iNumCols: Int, field: Field[_ <: Element]): FatMatrix = {
		val Iarr = new Array[Int](arr.length)

		for (i <- 1 to arr.length) {
			Iarr.update(i - 1, i)
		}

		fromFatMatrixArray(arr, numCols, iNumRows, iNumCols, field, Iarr)
	}

	def fromFatMatrixArray(arr: Array[FatMatrix], numCols: Int, iNumRows: Int, iNumCols: Int,
	                       field: Field[_ <: Element], Iarr: Array[Int]): FatMatrix = {

		val res = new FatMatrix(Iarr.length, numCols, iNumRows, iNumCols, field)

		for (i <- 1 to Iarr.length) {
			if (arr(Iarr(i - 1) - 1) == null) {
				res.replaceRowFromFatMatrix(i, new FatMatrix(1, numCols, iNumRows, iNumCols, field), 1)
			} else if (arr(Iarr(i - 1) - 1).numRows != 1 || arr(Iarr(i - 1) - 1).numCols != numCols) {
				throw new IllegalArgumentException("FatMatrix(Array[FatMatrix]): FatMatrix Dimensions inconsistent")
			} else {
				res.replaceRowFromFatMatrix(i, arr(Iarr(i - 1) - 1), 1)
			}
		}

		res
	}

	def getFatMatrixArray(m: FatMatrix): Array[FatMatrix] = {
		val res = new Array[FatMatrix](m.numRows())

		for (i <- 1 to res.length) {
			res.update(i - 1, m.rowAsFatMatrix(i))
		}

		res
	}

	def fromMatrixArray(arr: Array[Matrix], iNumRows: Int, iNumCols: Int, field: Field[_ <: Element]) = {
		val res = new FatMatrix(arr.length, 1, iNumRows, iNumCols, field)

		for (i <- 1 to arr.length) {
			res.set(i, 1, arr(i - 1))
		}

		res
	}
}
