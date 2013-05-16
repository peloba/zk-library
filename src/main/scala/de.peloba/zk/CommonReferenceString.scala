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
package zk

import de.peloba.math.{FatMatrix, Curves, Matrix}
import de.peloba.util.Helper
import java.io.{FileOutputStream, File, DataOutputStream}
import java.util.zip.{ZipEntry, ZipOutputStream, ZipFile}
import java.util.Properties
import scala.collection.JavaConverters._
import it.unisa.dia.gas.jpbc.{Field, Element}

/**
 * The class CommonReferenceString models a Groth-Sahai CRS for the
 * SXDH instantiation and information-theoretically binding commitments,
 * i.e., a CRS for proofs of knowledge.
 *
 * The class provides the necessary group definitions, commitment keys, and so on.
 *
 * The normal usage is to either randomly generate a CRS or to load a CRS from a zip file.
 * To obtain an instance of CommonReferenceString, the class offers a static method getInstance. This function will
 * generate a new CRS if no CRS has been loaded before. Further calls to getInstance will return the same CRS,
 * unless a new curve is loaded, a CRS is loaded from file, or a CRS is freshly generated.
 *
 * The CRS class draws upon the de.peloba.math.Curves class that supplies several pre-defined curves
 * for various security parameters.
 *
 * In the following, we let
 * G,,1,, and G,,2,, denote two subgroups of an elliptic curve
 * G,,T,, denote a field extension
 * Z,,r,, denote a prime-order group (group of exponents)
 * e: G,,1,,xG,,2,, -> G,,T,, denote the asymmetric bilinear map
 *
 * For more information, please refer to
 * Jens Groth and Amit Sahai: Efficient Noninteractive Proof Systems for Bilinear Groups,
 * SIAM Journal on Computing, vol. 41(5), pages 1193-1232.
 *
 * @constructor Creates a new CRS object. Usually, the CRS is read from file via the object methods
 *              [[de.peloba.zk.CommonReferenceString$.generate generate]] and
 *              [[de.peloba.zk.CommonReferenceString$.fromZipFile fromZipFile]]
 * @param curveKey String describing the curve (cf. [[de.peloba.math.Curves]])
 * @param G Designated generator of G,,1,,
 * @param H Designated generator of G,,2,,
 * @param u1 Part of the commitment key
 * @param u2 Part of the commitment key
 * @param v1 Part of the commitment key
 * @param v2 Part of the commitment key
 *
 * @author Julian Backes
 * @author Stefan Lorenz
 * @author Kim Pecina
 */
class CommonReferenceString(val curveKey: String, val G: Element, val H: Element, val u1: Matrix, val u2: Matrix,
                            val v1: Matrix, val v2: Matrix) {
	/**
	 * Group G,,1,,
	 */
	def G1 = pairing.getG1

	/**
	 * Group G,,2,,
	 */
	def G2 = pairing.getG2

	/**
	 * Group Z,,r,, of exponents
	 */
	def Zr = pairing.getZr

	/**
	 * Group G,,T,,, target group of the pairing
	 */
	def Gt = pairing.getGT

	/**
	 * @return the ''n''x''n'' unity matrix (neutral element of matrix multiplication)
	 * @param dimension n
	 */
	def unitMatrix(dimension: Int) = {
		val res = new Matrix(dimension, dimension, Zr.newZeroElement())
		(1 to dimension).foreach(i => res.set(i, i, Zr.newOneElement()))
		res
	}

	/**
	 * Returns a random ''n''x''m'' matrix with entries from Z,,r,,
	 *
	 * @return a random ''n'' x ''m'' matrix filled with random elements from Z,,r,,
	 * @param numberOfRows n
	 * @param numberOfCols m
	 */
	def randomZrMatrix(numberOfRows: Int, numberOfCols: Int) = Matrix.getRandomMatrix(numberOfRows, numberOfCols, Zr)

	/**
	 * Commitment key u
	 *
	 * u = (u,,1,,, u,,2,,)
	 */
	def u = {
		val res = new FatMatrix(2, 1, u1.numberOfRows, u1.numberOfCols, G1)
		res.set(1, 1, u1).set(2, 1, u2)
	}

	/**
	 * Commitment key v
	 *
	 * v = (v,,1,,, v,,2,,)
	 */
	def v = {
		val res = new FatMatrix(2, 1, v1.numberOfRows, v1.numberOfCols, G2)
		res.set(1, 1, v1).set(2, 1, v2)
	}

	/**
	 * Used internally
	 */
	def u1Fat(numberOfRows: Int, numberOfCols: Int) = {
		new FatMatrix(numberOfRows, numberOfCols, u1)
	}

	/**
	 * Used internally
	 */
	def v1Fat(numberOfRows: Int, numberOfCols: Int) = {
		new FatMatrix(numberOfRows, numberOfCols, v1)
	}

	/**
	 * Used internally
	 */
	def debugPrintField(field: Field[_ <: Element]) {
		if (field.equals(G1)) println("The field is G1")
		else if (field.equals(G2)) println("The field is G2")
		else if (field.equals(Zr)) println("The field is Zr")
		else if (field.equals(Gt)) println("The field is Gr")
		else println("Unknown field")
	}

	/**
	 * The bilinear map e.
	 *
	 * The bilinear map maps pairs from G,,1,, x G,,2,, into the target group G,,T,, and it is bilinear, i.e.,
	 * e(aG, bH) = e(G,bH)^a^ = e(G,H)^ab^ = e(aG, H)^b^
	 * for all a, b from Z,,r,,, G from G,,1,, and H from G,,2,,.
	 */
	val pairing = Curves.pairing(curveKey)

	/**
	 * Writes ''this'' into ''fileName'' in zip format
	 *
	 * @param fileName filename to store file to
	 * @throws ZipException if a ZIP format error has occurred
	 * @throws IOException if an I/O error has occurred
	 */
	def writeToZipFile(fileName: String) {
		val os = new ZipOutputStream(new FileOutputStream(fileName))

		os.putNextEntry(new ZipEntry("params"))
		params.store(os, "AUTO GENERATED\nDO NOT TOUCH")

		os.putNextEntry(new ZipEntry("G"))
		os.write(G.toBytes)

		os.putNextEntry(new ZipEntry("H"))
		os.write(H.toBytes)

		os.putNextEntry(new ZipEntry("u1"))
		os.write(u1.toBytes)

		os.putNextEntry(new ZipEntry("u2"))
		os.write(u2.toBytes)

		os.putNextEntry(new ZipEntry("v1"))
		os.write(v1.toBytes)

		os.putNextEntry(new ZipEntry("v2"))
		os.write(v2.toBytes)

		os.closeEntry()
		os.close()
	}

	/**
	 * The parameters of the CRS as a map.
	 *
	 * Contains the following keys:
	 * "curve_key" -> name of the current curve,
	 * "u1_size" -> number of rows of u,,1,,
	 * "u2_size" -> number of rows of u,,2,,
	 * "v1_size" -> number of rows of v,,1,,
	 * "v2_size" -> number of rows of v,,2,,
	 */
	lazy val params = {
		val res = new Properties
		res.putAll(Map(
			"curve_key" -> curveKey,
			"u1_size" -> u1.numberOfRows.toString,
			"u2_size" -> u2.numberOfRows.toString,
			"v1_size" -> v1.numberOfRows.toString,
			"v2_size" -> v2.numberOfRows.toString
		).asJava)
		res
	}

	/**
	 * Provides a nice textual description of the CRS.
	 *
	 * @return a textual description of ''this''
	 */
	override def toString = {
		"[curve_key = '" + curveKey + "', G = " + G.toString + ", H = " + H.toString + ", u1 = " + u1.toString + ", u2 = " + u2.toString + ", v1 = " + v1.toString + ", v2 = " + v2.toString + "]"
	}
}

/**
 * The class CommonReferenceString models a Groth-Sahai CRS for the
 * SXDH instantiation and information-theoretically binding commitments,
 * i.e., a CRS for proofs of knowledge.
 *
 * The class provides the necessary group definitions, commitment keys, and so on.
 *
 * The normal usage is to either randomly generate a CRS or to load a CRS from a zip file.
 * To obtain an instance of CommonReferenceString, the class offers a static method getInstance. This function will
 * generate a new CRS if no CRS has been loaded before. Further calls to getInstance will return the same CRS,
 * unless a new curve is loaded, a CRS is loaded from file, or a CRS is freshly generated.
 *
 * The CRS class draws upon the de.peloba.math.Curves class that supplies several pre-defined curves
 * for various security parameters.
 *
 * In the following, we let
 * G,,1,, and G,,2,, denote two subgroups of an elliptic curve
 * G,,T,, denote a field extension
 * Z,,r,, denote a prime-order group (group of exponents)
 * e: G,,1,,xG,,2,, -> G,,T,, denote the asymmetric bilinear map
 *
 * For more information, pleaserefer to
 * Jens Groth and Amit Sahai: Efficient Noninteractive Proof Systems for Bilinear Groups,
 * SIAM Journal on Computing, vol. 41(5), pages 1193-1232.
 *
 *
 * @author Julian Backes
 * @author Stefan Lorenz
 * @author Kim Pecina
 */
object CommonReferenceString {

	private var instance: CommonReferenceString = null
	private var curveKey: String = "typeD_224_496659"
	private var newCurve = false

	/**
	 * Sets the curve to the given parameters. The new CRS is retrieved using [[de.peloba.zk.CommonReferenceString#getInstance]]
	 *
	 * For a description of the available curves, please refer to de.peloba.math.Curves
	 *
	 * @param s curve description
	 */
	def setCurve(s: String) {
		curveKey = s
		newCurve = true
	}

	/**
	 * Returns the current instance of CommonReferenceString. If no such instance has been loaded or generated,
	 * getInstance creates and returns a random CRS for the set curve.
	 *
	 * getInstance will always return the same CRS if call multiple times if no new curve is generated, the curve
	 * is changed, or a new CRS is loaded from a file.
	 *
	 * Use writeToZipFile to store a CRS to file.
	 *
	 * The default is a curve with a 112 bit security parameter (group size is 224 bits).
	 *
	 * @return a CRS
	 */
	def getInstance() = {
		if (instance == null || newCurve) {
			instance = CommonReferenceString.generate(curveKey)
			newCurve = false
		}

		instance
	}

	/**
	 * Used internally
	 */
	def fromZipFile(data: Array[Byte]): CommonReferenceString = {
		val tmpfile = File.createTempFile("tales", ".crs")
		val fout = new FileOutputStream(tmpfile)
		val dout = new DataOutputStream(fout)
		dout.write(data)
		dout.close()

		val ret = fromZipFile(tmpfile.toString)

		tmpfile.delete()

		ret
	}

	/**
	 * Loads a previously stored CRS from file. This will become the new instance, i.e., calls to
	 * getInstance will return the loaded CRS.
	 *
	 * @param fileName file containing the zipped CRS
	 * @return the loaded CRS instance.
	 */
	def fromZipFile(fileName: String) = {
		val zipFile = new ZipFile(fileName)
		val params = new Properties
		params.load(zipFile.getInputStream(zipFile.getEntry("params")))
		val pairing = Curves.pairing(params.getProperty("curve_key"))

		instance = new CommonReferenceString(
			params.getProperty("curve_key"),
			Helper.curveElementFromZipFile(zipFile, "G", pairing.getG1) getOrElse pairing.getG1.newOneElement(),
			Helper.curveElementFromZipFile(zipFile, "H", pairing.getG2) getOrElse pairing.getG2.newOneElement(),
			Helper.vectorFromZipFile(zipFile, "u1", Helper.stringToInt(params.getProperty("u1_size")), pairing.getG1),
			Helper.vectorFromZipFile(zipFile, "u2", Helper.stringToInt(params.getProperty("u2_size")), pairing.getG1),
			Helper.vectorFromZipFile(zipFile, "v1", Helper.stringToInt(params.getProperty("v1_size")), pairing.getG2),
			Helper.vectorFromZipFile(zipFile, "v2", Helper.stringToInt(params.getProperty("v2_size")), pairing.getG2)
		)
		newCurve = false

		instance
	}

	/**
	 * Generates and returns a randomized CRS. This will become the new instance, i.e., calls to [[de.peloba.zk.CommonReferenceString#getInstance]]
	 * will return the generated CRS.
	 *
	 * @param curveKey curve description
	 * @return generated instance
	 */
	def generate(curveKey: String) = {
		val pairing = Curves.pairing(curveKey)
		val G = pairing.getG1.newRandomElement
		val H = pairing.getG2.newRandomElement

		val u1 = new Matrix(2, 1, pairing.getG1)
		u1.set(1, 1, G.duplicate).set(2, 1, G.duplicate.mulZn(pairing.getZr.newRandomElement))
		val u2 = u1 * pairing.getZr.newRandomElement

		val v1 = new Matrix(2, 1, pairing.getG2)
		v1.set(1, 1, H.duplicate).set(2, 1, H.duplicate.mulZn(pairing.getZr.newRandomElement))
		val v2 = v1 * pairing.getZr.newRandomElement

		instance = new CommonReferenceString(curveKey, G, H, u1, u2, v1, v2)
		newCurve = false

		instance
	}

}
