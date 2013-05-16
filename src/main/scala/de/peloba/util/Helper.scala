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
package util

import de.peloba.math.Matrix
import java.util.zip.ZipFile
import java.io.InputStream
import it.unisa.dia.gas.jpbc.{Element, Field}

object Helper {
	//def elementFromFile(fileName: String, field: Field): Element = field.newElement().getImmutable

	def vectorFromZipFile(file: ZipFile, entryName: String, vectorSize: Int, field: Field[_ <: Element]) = {
		//val res = new Matrix(1, vectorSize, field)
    val res = new Matrix(vectorSize, 1, field)
		bytesFromZipFile(file, entryName).map(res.setFromBytes(_)) getOrElse res
	}

	def curveElementFromBytes(field: Field[_ <: Element], data: Array[Byte]) = {
		val element = field.newElement()
		element.setFromBytes(data)
		element
	}

	def curveElementFromZipFile(file: ZipFile, entryName: String, field: Field[_ <: Element]): Option[Element] = bytesFromZipFile(file, entryName).map(curveElementFromBytes(field, _))

	def bytesFromInputStream(is: InputStream, length: Int): Option[Array[Byte]] = {
		val res = new Array[Byte](length)

		var offset = 0
		var numRead = 0

		while (offset < res.length && { numRead = is.read(res, offset, res.length - offset); numRead} >= 0)
			offset += numRead

		if (offset < res.length)
			return None

		Some(res)
	}

	def bytesFromZipFile(file: ZipFile, entryName: String): Option[Array[Byte]] = {
		val entry = file.getEntry(entryName)

		if(entry == null)
			return None

		if(entry.getSize > Int.MaxValue)
			return None

		val is = file.getInputStream(entry)

		val res = bytesFromInputStream(is, entry.getSize.toInt)

		is.close()

		res
	}

	def stringToInt(data: String, defaultValue: Int): Int = {
		try {
			data.toInt
		} catch {
			case _: Throwable => defaultValue
		}
	}

	def stringToInt(data: String): Int = stringToInt(data, 0)
}
