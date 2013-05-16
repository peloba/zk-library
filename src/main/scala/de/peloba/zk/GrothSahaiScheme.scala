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

import it.unisa.dia.gas.jpbc.{Field, Element}
import math.{FatMatrix, Matrix}

/**
 * The class GrothSahaiScheme implements the Groth-Sahai zero-knowledge proof scheme for the
 * SXDH instantiation and information-theoretically binding commitments,
 * i.e., the zero-knowledge proofs are proofs of knowledge. The class provides methods for pairing product
 * equations, multi-scalar multiplication equations in G,,1,, and G,,2,,, and quadratic equations in Z,,r,,.
 *
 * For more information, please refer to
 * [1] Jens Groth and Amit Sahai: Efficient Noninteractive Proof Systems for Bilinear Groups,
 * SIAM Journal on Computing, vol. 41(5), pages 1193-1232.
 *
 * @constructor Instantiates the Groth-Sahai proof system with the information stored in the provided CRS.
 *              After calling the constructor, the scheme is fully usable an no further actions are necessary.

 * @param crs common reference string with the necessary cryptographic setup information
 *
 * @author Julian Backes
 * @author Stefan Lorenz
 * @author Kim Pecina
 */
class GrothSahaiScheme(crs: CommonReferenceString) {

	/**
	 * Used internally
	 *
	 * maps elements '''x''' into the corresponding module of G1 or G2
	 * Technically, it returns a (0 x '''x''') Matrix.
	 * @param x
	 * @return
	 */
	def iota(x: Element) = {
		val res = new Matrix(2, 1, x.getField)
		res.set(2, 1, x)
	}


	/**
	 * Computes a commitment to element x with randomness T
	 *
	 * @param x element to commit to
	 * @param T (1 x 2) Matrix, randomness to use in the commitment
	 * @return (2 x 1) Matrix - (1 x 2) Matrix pair, the first is the commitment on '''x''' with randomness '''T''', the second is '''T'''
	 */
	def commit(x: Element, T: Matrix): Pair[Matrix, Matrix] = {
		val X = new Matrix(1, 1, x)
		val p = commit(X, T)
		(p._1(1, 1), p._2)
	}


	/**
	 * Computes a random commitment to element x
	 *
	 * @param x element to commit to
	 * @return (2 x 1) Matrix - (1 x 2) Matrix pair, the first is the commitment '''c''' on '''x''', the second is the randomness used in '''c'''
	 */
	def commit(x: Element): Pair[Matrix, Matrix] = commit(x, crs.randomZrMatrix(1, 2))


	/**
	 * Computes a commitment to element X with randomness T
	 * The return value is a pair consisting of a FatMatrix and a Matrix.
	 *
	 * @param X '''n''' x 1 Matrix, elements to commit to
	 * @param T '''n''' x 2 Matrix, randomness to use in the commitment for '''n''' commitments
	 * @return ('''n''' x 1 with 2 x 1) FatMatrix - ('''n''' x 2) Matrix pair, the FatMatrix contains the commitments '''c''' on '''X''', the second is the randomness used in '''c'''
	 */
	def commit(X: Matrix, T: Matrix): Pair[FatMatrix, Matrix] = {
		val E = {
			if (X.field.getClass.equals(crs.G1.getClass))
				X.fatMap(2, 1, crs.G1, iota(_)) + (T * crs.u)
			else if (X.field.getClass.equals(crs.G2.getClass))
				X.fatMap(2, 1, crs.G2, iota(_)) + (T * crs.v)
			else
				throw new Exception("The elements neither belong to G1 nor to G2")
		}

		(E, T)
	}


	/**
	 * Computes a random commitment to element X
	 * The return value is a pair consisting of a FatMatrix and a Matrix.
	 *
	 * @param X ('''n''' x 1) Matrix, element to commit to
	 * @return ('''n''' x 1 with 2 x 1 entries) FatMatrix - ('''n''' x 2) Matrix pair, the first is a random commitment '''c''' on '''x''', the second is the randomness used in '''c'''
	 */
	def commit(X: Matrix): Pair[FatMatrix, Matrix] = commit(X, crs.randomZrMatrix(X.numberOfRows, 2))

	/*def commit(x: Element) = {
		val r1 = crs.pairing.getZr.newRandomElement()
		val r2 = crs.pairing.getZr.newRandomElement()

		if (x.getField.equals(crs.pairing.getG1))
			iota(x) + (crs.u1 * r1) + (crs.u2 * r2)
		else if (x.getField.equals(crs.pairing.getG2))
			iota(x) + (crs.v1 * r1) + (crs.v2 * r2)
		else
			throw new Exception("The group element neither belongs to G1 nor to G2")
	}*/


	/**
	 * Used internally
	 *
	 * iota prime maps elements of Zr into the G1 or G2 module ()

	 * @param z element of Z,,r,,
	 * @return vector of the module for Z,,r,,
	 */
	def iotaPrime(field: Field[_ <: Element], z: Element) = {
		if (field.getClass.equals(crs.G1.getClass))
			(crs.u2 + iota(crs.G)) * z
		else if (field.getClass.equals(crs.G2.getClass))
			(crs.v2 + iota(crs.H)) * z
		else
			throw new Exception("The field is neither G1 nor G2")
	}


	/**
	 * Used internally
	 *
	 * commits values of Z,,r,, into G,,1,, or G,,2,, modules
	 *
	 * @param z ('''n''' x 1) Matrix
	 * @param t ('''n''' x 1) Matrix
	 *
	 * @return ('''n''' x 1 with 2 x 1 entries) FatMatrix - ('''n''' x 1) Matrix pair
	 */
	def commitPrime(field: Field[_ <: Element], z: Matrix, t: Matrix): Pair[FatMatrix, Matrix] = {
		val ePrime = new FatMatrix(z.numberOfRows, 1, 2, 1, field)

		if (field.getClass.equals(crs.G1.getClass))
			(1 to z.numberOfRows).foreach(i => ePrime.set(i, 1, iotaPrime(field, z(i, 1)) + (crs.u1 * t(i, 1))))
		else if (field.getClass.equals(crs.G2.getClass)) {
			(1 to z.numberOfRows).foreach(i => ePrime.set(i, 1, iotaPrime(field, z(i, 1)) + (crs.v1 * t(i, 1))))
		}
		else
			throw new Exception("The field is neither G1 nor G2")

		(ePrime, t)
	}


	/**
	 * Used internally
	 *
	 * @param z ('''n''' x 1) Matrix
	 * @return ('''n''' x 1 with 2 x 1) FatMatrix - ('''n''' x 1) Matrix pair
	 */
	def commitPrime(field: Field[_ <: Element], z: Matrix): Pair[FatMatrix, Matrix] = commitPrime(field, z, crs.randomZrMatrix(z.numberOfRows, 1))

	/*def commitPrime(field: Field[_ <: Element], x: Element) = {
		val r = crs.pairing.getZr.newRandomElement()

		if (field.equals(crs.G1))
			(iotaPrime(field, x) + (crs.u1 * r), r)
		else if (field.equals(crs.G2))
			(iotaPrime(field, x) + (crs.v1 * r), r)
		else
			throw new Exception("The field is neither G1 nor G2")
	}*/


	/**
	 * Computes a zero-knowledge proof for a pairing product equation.
	 *
	 * The arguments are all passed as row-vectors, i.e., '''n''' x 1 matrices
	 *
	 * In the following, we let P,,i=0,,^n^ p,,i,, := p,,1,, * ... * p,,n,,
	 *
	 * ppEquation(R, S, A, B, X, Y, gamma, T) computes a zero-knowledge proof for the equation<br/>
	 * P,,i=0,,^n^ e(A,,i,,, Y,,i,,) * P,,i=0,,^m^ e(X,,i,,, B,,i,,) * P,,i=0,,^n^ P,,j=0,,^m^ e(X,,i,,, Y,,j,,)^{gamma,,ij,,}^ = 1
	 *
	 * For technical reasons, the result of an equation is always 1, the neutral element of G,,T,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * @example For instance, ppEquation(_, _, (G, 0), (0, 0), (X,,1,,, X,,2,,), (Y,,1,,, Y,,2,,), ((0, 1), (0, 0)), _)
	 *          yields a zero-knowledge proof for for the equation e(G, Y,,1,,) * e(X,,1,,, Y,,2,,) = 1
	 *
	 *
	 * @param R ('''n''' x 2) Matrix, randomness used for the commitments on '''X'''
	 * @param S ('''m''' x 2) Matrix, randomness used for the commitment on '''Y'''
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param B ('''n''' x 1) Matrix, revealed constant values from G,,2,,
	 * @param X ('''n''' x 1) Matrix, committed values from G,,1,,
	 * @param Y ('''m''' x 1) Matrix, committed values from G,,2,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @param T (2 x 2) Matrix, randomness used to randomize the zero-knowledge proof
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (pi) - (2 x 1 with 2 x 1) FatMatrix (theta) pair zero-knowledge proof
	 */
	def ppEquation(R: Matrix, S: Matrix, A: Matrix, B: Matrix, X: Matrix, Y: Matrix, gamma: Matrix, T: Matrix): (FatMatrix, FatMatrix) = {

		val pi = (R.transpose * B.fatMap(2, 1, crs.G2, iota(_))) + ((R.transpose * gamma) * Y.fatMap(2, 1, crs.G2, iota(_))) + ((((R.transpose * gamma) * S) - T.transpose) * crs.v)
		val theta = (S.transpose * A.fatMap(2, 1, crs.G1, iota(_))) + ((S.transpose * gamma.transpose) * X.fatMap(2, 1, crs.G1, iota(_))) + (T * crs.u)

		(pi, theta)
	}


	/**
	 * Computes a zero-knowledge proof for a pairing product equation.
	 *
	 * The arguments are all passed as row-vectors, i.e., '''n''' x 1 matrices
	 *
	 * In the following, we let P,,i=0,,^n^ p,,i,, := p,,1,, * ... * p,,n,,
	 *
	 * ppEquation(R, S, A, B, X, Y, gamma, T) computes a zero-knowledge proof for the equation<br/>
	 * P,,i=0,,^n^ e(A,,i,,, Y,,i,,) * P,,i=0,,^m^ e(X,,i,,, B,,i,,) * P,,i=0,,^n^ P,,j=0,,^m^ e(X,,i,,, Y,,j,,)^{gamma,,ij,,}^ = 1
	 *
	 * For technical reasons, the result of an equation is always 1, the neutral element of G,,T,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * The randomness used to compute the actual zero-knowledge proof (called '''T''') is chosen uniformly at random
	 *
	 * @example For instance, ppEquation(_, _, (G, 0), (0, 0), (X,,1,,, X,,2,,), (Y,,1,,, Y,,2,,), ((0, 1), (0, 0)), _)
	 *          yields a zero-knowledge proof for for the equation e(G, Y,,1,,) * e(X,,1,,, Y,,2,,) = 1
	 *
	 *
	 * @param R ('''n''' x 2) Matrix, randomness used for the commitments on '''X'''
	 * @param S ('''m''' x 2) Matrix, randomness used for the commitment on '''Y'''
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param B ('''n''' x 1) Matrix, revealed constant values from G,,2,,
	 * @param X ('''n''' x 1) Matrix, committed values from G,,1,,
	 * @param Y ('''m''' x 1) Matrix, committed values from G,,2,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (pi) - (2 x 1 with 2 x 1) FatMatrix (theta) pair zero-knowledge proof
	 */
	def ppEquation(R: Matrix, S: Matrix, A: Matrix, B: Matrix, X: Matrix, Y: Matrix, gamma: Matrix): (FatMatrix, FatMatrix) = {
		val T = crs.randomZrMatrix(2, 2)

		ppEquation(R, S, A, B, X, Y, gamma, T)
	}


	/**
	 * Computes a zero-knowledge proof for a multi-scalar multiplication equation in G,,1,,
	 *
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,1,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * The randomness used to compute the actual zero-knowledge proof (called '''T''') is chosen uniformly at random
	 *
	 * @param R ('''n''' x 2) Matrix, randomness used for the commitments on '''X'''
	 * @param s ('''m''' x 1) Matrix, randomness used for the commitment on '''y'''
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param X ('''n''' x 1) Matrix, committed values from G,,1,,
	 * @param y ('''m''' x 1) Matrix, committed values from Z,,r,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (pi) - (2 x 1) Matrix (theta) pair zero-knowledge proof
	 */
	def msmEquationG1(R: Matrix, s: Matrix, A: Matrix, b: Matrix, X: Matrix, y: Matrix, gamma: Matrix) = {
		val T = crs.randomZrMatrix(1, 2)

		val pi = (R.transpose * b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))) + ((R.transpose * gamma) * y.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))) + ((((R.transpose * gamma) * s) - T.transpose) * crs.v1Fat(1, 1))
		/* changed from fatmap1,2 to 1,1 */
		val theta = ((s.transpose * A.fatMap(2, 1, crs.G1, iota(_))) + ((s.transpose * gamma.transpose) * X.fatMap(2, 1, crs.G1, iota(_))) + (T * crs.u)).flatten

		(pi, theta)
	}


	/**
	 * Computes a zero-knowledge proof for a linear multi-scalar multiplication equation in G,,1,,
	 * The linear part is in G,,1,, ('''X''' * '''b''') and the result is in G,,1,,
	 *
	 * Linear means that no terms with two variables (e.g., '''X''' * '''y''') occur.
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,1,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param R ('''n''' x 2) Matrix, randomness used for the commitments on '''X'''
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (pi) zero-knowledge proof
	 */
	def linG1MsMEquationG1(R: Matrix, b: Matrix) = {
		val pi = (R.transpose * b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _)))

		pi
	}


	/**
	 * Computes a zero-knowledge proof for a linear multi-scalar multiplication equation in G,,1,,
	 * The linear part is in Z,,r,, ('''y''' * '''A''') and the result is in G,,1,,
	 *
	 * Linear means that no terms with two variables (e.g., '''X''' * '''y''') occur.
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,1,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param s ('''m''' x 2) Matrix, randomness used for the commitments on '''y'''
	 * @param A ('''m''' x 1) Matrix, revealed constant '''A''' values from G,,1,,
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (theta) zero-knowledge proof
	 */
	def linZrMsMEquationG1(s: Matrix, A: Matrix) = {
		val theta = (s.transpose * A.fatMap(2, 1, crs.G1, iota(_))).flatten

		theta
	}


	/**
	 * Computes a zero-knowledge proof for a multi-scalar multiplication equation in G,,2,,
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,2,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * The randomness used to compute the actual zero-knowledge proof (called '''T''') is chosen uniformly at random
	 *
	 * @param r ('''n''' x 1) Matrix, randomness used for the commitments on '''x'''
	 * @param S ('''m''' x 2) Matrix, randomness used for the commitment on '''Y'''
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param B ('''n''' x 1) Matrix, revealed constant values from G,,2,,
	 * @param x ('''n''' x 1) Matrix, committed values from Z,,r,,
	 * @param Y ('''m''' x 2) Matrix, committed values from G,,2,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @return (2 x 1) Matrix (pi) - (2 x 1 with 2 x 1 entries) FatMatrix (theta) pair zero-knowledge proof
	 */
	def msmEquationG2(r: Matrix, S: Matrix, a: Matrix, B: Matrix, x: Matrix, Y: Matrix, gamma: Matrix) = {
		val T = crs.randomZrMatrix(2, 1)

		val pi = ((r.transpose * B.fatMap(2, 1, crs.G1, iota(_))) + ((r.transpose * gamma) * Y.fatMap(2, 1, crs.G2, iota(_))) + ((((r.transpose * gamma) * S) - T.transpose) * crs.v)).flatten
		val theta = (S.transpose * a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))) + ((S.transpose * gamma.transpose) * x.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))) + (T * crs.u1Fat(2, 1))

		(pi, theta)
	}


	/**
	 * Computes a zero-knowledge proof for a linear multi-scalar multiplication equation in G,,2,,
	 * The linear part is in G,,2,, ('''a''' * '''Y''') and the result is in G,,2,,
	 *
	 * Linear means that no terms with two variables (e.g., '''X''' * '''Y''') occur.
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,2,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param S ('''m''' x 2) Matrix, randomness used for the commitments on '''Y'''
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @return (2 x 1 with 2 x 1 entries) FatMatrix (theta) zero-knowledge proof
	 */
	def linG2MsmEquationG2(S: Matrix, a: Matrix) = {
		val theta = S.transpose * a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))

		theta
	}


	/**
	 * Computes a zero-knowledge proof for a linear multi-scalar multiplication equation in G,,2,,
	 * The linear part is in Z,,r,, ('''x''' * '''B''') and the result is in G,,2,,
	 *
	 * Linear means that no terms with two variables (e.g., '''X''' * '''Y''') occur.
	 *
	 * For technical reasons, the result of an equation is always 0, the neutral element of G,,2,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param r ('''n''' x 1) Matrix, randomness used for the commitments on '''x'''
	 * @param B ('''n''' x 1) Matrix, revealed constant values from G,,2,,
	 * @return (2 x 1) Matrix (pi) zero-knowledge proof
	 */
	def linZrMsMEquationG2(r: Matrix, B: Matrix) = {
		val pi = (r.transpose * B.fatMap(2, 1, crs.G2, iota(_))).flatten

		pi
	}


	/**
	 * Computes a zero-knowledge proof for a quadratic equation in Z,,r,,
	 *
	 * For technical reasons, the result of a ppEquation is always 1, the neutral element of Z,,r,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param r ('''n''' x 1) Matrix, randomness used for the commitments on '''x'''
	 * @param s ('''m''' x 1) Matrix, randomness used for the commitment on '''y'''
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param x ('''n''' x 1) Matrix, committed values from Z,,r,,
	 * @param y ('''m''' x 1) Matrix, committed values from Z,,r,,
	 * @param gamma ('''m''' x '''n''') Matrix, constants from Z,,r,,
	 * @return (2 x 1) Matrix - (2 x 1) Matrix pair, zero-knowledge proof
	 */
	def quadraticEquation(r: Matrix, s: Matrix, a: Matrix, b: Matrix, x: Matrix, y: Matrix, gamma: Matrix) = {
		val T = crs.Zr.newRandomElement

		val pi = (r.transpose * b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))).flatten +
			((r.transpose * gamma) * y.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))).flatten +
			(crs.v1 * (((r.transpose * gamma) * s).flatten.duplicate().sub(T)))
		val theta = (s.transpose * a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))).flatten +
			((s.transpose * gamma) * x.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))).flatten +
			(crs.u1 * T)

		(pi, theta)
	}


	/**
	 * Computes a zero-knowledge proof for a linear quadratic equation in Z,,r,,
	 * Linear means that no terms with two variables (e.g., '''X''' * '''Y''') occur.
	 *
	 * For technical reasons, the result of an equation is always 1, the neutral element of Z,,r,,, since otherwise, the
	 * resulting proof is not zero-knowledge.
	 *
	 * Notice that multi-scalar equations can always be rewritten to satisfy the above condition, more precisely,
	 * a given equation '''f''' = '''g''' can be rewritten as '''f''' - '''g''' = 0
	 *
	 * @param s ('''m''' x 1) Matrix, randomness used for the commitment on '''y'''
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @return (2 x 1) Matrix (theta), zero-knowledge proof
	 */
	def linQuadraticEquation(s: Matrix, a: Matrix) = {
		val theta = (s.transpose * a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _))).flatten

		theta
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param B ('''n''' x 1) Matrix, revealed constant values from G,,2,,
	 * @param c ('''n''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,1,,
	 * @param d ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,2,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @param pi (2 x 1 with 2 x 1 entries) FatMatrix, first component of the zero-knowledge proof
	 * @param theta (2 x 1 with 2 x 1 entries) FatMatrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyPpEquation(A: Matrix, B: Matrix, c: FatMatrix, d: FatMatrix, gamma: Matrix, pi: FatMatrix, theta: FatMatrix) = {
		val lhs = A.fatMap(2, 1, crs.G1, iota(_)).fatPoint(crs, d) + c.fatPoint(crs, B.fatMap(2, 1, crs.G2, iota(_))) + c.fatPoint(crs, gamma * d)
		val rhs = /* iota_T(t_T) + */ crs.u.fatPoint(crs, pi) + theta.fatPoint(crs, crs.v)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param c ('''n''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,1,,
	 * @param dPrime ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @param pi (2 x 1 with 2 x 1 entries) FatMatrix, first component of the zero-knowledge proof
	 * @param theta (2 x 1) Matrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyMsmEquationG1(A: Matrix, b: Matrix, c: FatMatrix, dPrime: FatMatrix, gamma: Matrix, pi: FatMatrix, theta: Matrix) = {
		val lhs = A.fatMap(2, 1, crs.G1, iota(_)).fatPoint(crs, dPrime) + c.fatPoint(crs, b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))) + c.fatPoint(crs, gamma * dPrime)
		val rhs = /* iota^~_T(T_1) + */ crs.u.fatPoint(crs, pi) + theta.F(crs, crs.v1)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param c ('''n''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,1,,
	 * @param pi (2 x 1 with 2 x 1 entries) FatMatrix, first component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyLinG1MsmEquationG1(b: Matrix, c: FatMatrix, pi: FatMatrix) = {
		val lhs = c.fatPoint(crs, b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _)))
		val rhs = /* iota^~_T(T_1) + */ crs.u.fatPoint(crs, pi)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param A ('''m''' x 1) Matrix, revealed constant values from G,,1,,
	 * @param dPrime ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param theta (2 x 1 with 2 x 1 entries) FatMatrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyLinZrMsmEquationG1(A: Matrix, dPrime: FatMatrix, theta: Matrix) = {
		val lhs = A.fatMap(2, 1, crs.G1, iota(_)).fatPoint(crs, dPrime)
		val rhs = /* iota^~_T(T_1) + */ theta.F(crs, crs.v1)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param a ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param B ('''m''' x 1) Matrix, revealed constant values from G,,2,,
	 * @param cPrime ('''n''' x 2 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param d ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,2,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @param pi (2 x 1) Matrix, first component of the zero-knowledge proof
	 * @param theta (2 x 1 with 2 x 1 entries) FatMatrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyMsmEquationG2(a: Matrix, B: Matrix, cPrime: FatMatrix, d: FatMatrix, gamma: Matrix, pi: Matrix, theta: FatMatrix) = {
		val lhs = a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _)).fatPoint(crs, d) + cPrime.fatPoint(crs, B.fatMap(2, 1, crs.G2, iota(_))) + cPrime.fatPoint(crs, gamma * d)
		val rhs = /* iota^_T(T_2) + */ crs.u1.F(crs, pi) + theta.fatPoint(crs, crs.v)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param d ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from G,,2,,
	 * @param theta (2 x 1 with 2 x 1 entries) FatMatrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyLinZrMsmEquationG1(a: Matrix, d: FatMatrix, theta: FatMatrix) = {
		val lhs = a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _)).fatPoint(crs, d)
		val rhs = /* iota^_T(T_2) + */ theta.fatPoint(crs, crs.v)

		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param b ('''n''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param cPrime ('''n''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param dPrime ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param gamma ('''n''' x '''m''') Matrix, constants from Z,,r,,
	 * @param pi (2 x 1) Matrix, first component of the zero-knowledge proof
	 * @param theta (2 x 1) Matrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyQuadraticEquation(a: Matrix, b: Matrix, cPrime: FatMatrix, dPrime: FatMatrix, gamma: Matrix, pi: Matrix, theta: Matrix) = {
		val lhs = a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _)).fatPoint(crs, dPrime) + cPrime.fatPoint(crs, b.fatMap(2, 1, crs.G2, iotaPrime(crs.G2, _))) + cPrime.fatPoint(crs, gamma * dPrime)
		val rhs = /* iota'_T(t) + */ crs.u1.F(crs, pi) + theta.F(crs, crs.v1)
		lhs isEqual rhs
	}


	/**
	 * Verifies a zero-knowledge proof with the provided public components and the given commitments.
	 *
	 * @param a ('''m''' x 1) Matrix, revealed constant values from Z,,r,,
	 * @param dPrime ('''m''' x 1 with 2 x 1 entries) FatMatrix, commitments to values from Z,,r,,
	 * @param theta (2 x 1) Matrix, second component of the zero-knowledge proof
	 * @return '''true''' if and only if the verification of the zero-knowledge proof with the given public parameters and commitments succeeds
	 */
	def verifyLinQuadraticEquation(a: Matrix, dPrime: FatMatrix, theta: Matrix) = {
		val lhs = a.fatMap(2, 1, crs.G1, iotaPrime(crs.G1, _)).fatPoint(crs, dPrime)
		val rhs = /* iota'_T(t) + */ theta.F(crs, crs.v1)

		lhs isEqual rhs
	}
}
