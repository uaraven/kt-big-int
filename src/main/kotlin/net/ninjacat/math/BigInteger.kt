/* java.math.BigInteger -- Arbitary precision integers
   Copyright (C) 1998, 1999, 2000, 2001, 2002, 2003, 2005, 2006, 2007, 2010
   Free Software Foundation, Inc.

This file is part of GNU Classpath.

GNU Classpath is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2, or (at your option)
any later version.

GNU Classpath is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Classpath; see the file COPYING.  If not, write to the
Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.

Linking this library statically or dynamically with other modules is
making a combined work based on this library.  Thus, the terms and
conditions of the GNU General Public License cover the whole
combination.

As a special exception, the copyright holders of this library give you
permission to link this library with independent modules to produce an
executable, regardless of the license terms of these independent
modules, and to copy and distribute the resulting executable under
terms of your choice, provided that you also meet, for each linked
independent module, the terms and conditions of the license of that
module.  An independent module is a module which is not derived from
or based on this library.  If you modify this library, you may extend
this exception to your version of the library, but you are not
obligated to do so.  If you do not wish to do so, delete this
exception statement from your version. */
package net.ninjacat.math

import kotlin.experimental.and
import kotlin.random.Random


/**
 * Written using on-line Java Platform 1.2 API Specification, as well
 * as "The Java Class Libraries", 2nd edition (Addison-Wesley, 1998) and
 * "Applied Cryptography, Second Edition" by Bruce Schneier (Wiley, 1996).
 *
 *
 * Based primarily on IntNum.java BitOps.java by Per Bothner (per@bothner.com)
 * (found in Kawa 1.6.62).
 *
 * @author Warren Levy (warrenl@cygnus.com)
 * @date December 20, 1999.
 * @status believed complete and correct.
 *
 * Converted to Kotlin to use with different target platforms
 *
 * @author Oleksiy Voronin (me@ovoronin.info)
 * @date January 30, 2020
 * @status Passes Jdk 14 unit tests (some of them
 */
class BigInteger : Number, Comparable<BigInteger?> {
    /**
     * All integers are stored in 2's-complement form.
     * If words == null, the ival is the value of this BigInteger.
     * Otherwise, the first ival elements of words make the value
     * of this BigInteger, stored in little-endian order, 2's-complement form.
     */
    @Transient
    private var ival = 0
    @Transient
    private var words: IntArray? = null
    // Serialization fields.
    // the first three, although not used in the code, are present for
    // compatibility with older RI versions of this class. DO NOT REMOVE.
    private val bitCount = -1
    private val bitLength = -1
    private val lowestSetBit = -2
    private val signum = 0

    companion object {
        private const val serialVersionUID = -8287574255936472291L
        /**
         * We pre-allocate integers in the range minFixNum..maxFixNum.
         * Note that we must at least preallocate 0, 1, and 10.
         */
        private const val minFixNum = -100
        private const val maxFixNum = 1024
        private const val numFixNum = maxFixNum - minFixNum + 1
        private val smallFixNums: Array<BigInteger?>
        /**
         * The constant zero as a BigInteger.
         *
         * @since 1.2
         */
        lateinit var ZERO: BigInteger
        /**
         * The constant one as a BigInteger.
         *
         * @since 1.2
         */
        lateinit var ONE: BigInteger
        /**
         * The constant ten as a BigInteger.
         *
         * @since 1.5
         */
        lateinit var TEN: BigInteger

        /* Rounding modes: */
        private const val FLOOR = 1
        private const val CEILING = 2
        private const val TRUNCATE = 3
        private const val ROUND = 4
        /**
         * When checking the probability of primes, it is most efficient to
         * first check the factoring of small primes, so we'll use this array.
         */
        private val primes = intArrayOf(
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
            47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
            109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
            191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251
        )
        /**
         * HAC (Handbook of Applied Cryptography), Alfred Menezes & al. Table 4.4.
         */
        private val k =
            intArrayOf(100, 150, 200, 250, 300, 350, 400, 500, 600, 800, 1250, Int.MAX_VALUE)
        private val t = intArrayOf(27, 18, 15, 12, 9, 8, 7, 6, 5, 4, 3, 2)
        /**
         * Return a BigInteger that is bitLength bits long with a
         * probability < 2^-100 of being composite.
         *
         * @param bitLength length in bits of resulting number
         * @param rnd       random number generator to use
         * @throws ArithmeticException if bitLength < 2
         * @since 1.4
         */
        @JvmStatic
        fun probablePrime(bitLength: Int, rnd: Random): BigInteger {
            if (bitLength < 2) {
                throw ArithmeticException()
            }
            return BigInteger(bitLength, 100, rnd)
        }

        /**
         * Return a (possibly-shared) BigInteger with a given long value.
         */
        @JvmStatic
        fun valueOf(`val`: Long): BigInteger? {
            if (`val` >= minFixNum && `val` <= maxFixNum) {
                return smallFixNums[`val`.toInt() - minFixNum]
            }
            val i = `val`.toInt()
            if (i.toLong() == `val`) {
                return BigInteger(i)
            }
            val result = alloc(2)
            result.ival = 2
            result.words!![0] = i
            result.words!![1] = (`val` shr 32).toInt()
            return result
        }

        /**
         * Make a canonicalized BigInteger from an array of words.
         * The array may be reused (without copying).
         */
        private fun make(words: IntArray?, len: Int): BigInteger? {
            var length = len
            if (words == null) {
                return valueOf(length.toLong())
            }
            length = wordsNeeded(words, length)
            if (length <= 1) {
                return if (length == 0) ZERO else valueOf(
                    words[0].toLong()
                )
            }
            val num = BigInteger()
            num.words = words
            num.ival = length
            return num
        }

        /**
         * Convert a big-endian byte array to a little-endian array of words.
         */
        private fun byteArrayToIntArray(
            bytes: ByteArray,
            sign: Int
        ): IntArray { // Determine number of words needed.
            val words = IntArray(bytes.size / 4 + 1)
            var nwords = words.size
            // Create a int out of modulo 4 high order bytes.
            var bptr = 0
            var word = sign
            var i = bytes.size % 4
            while (i > 0) {
                word = word shl 8 or (bytes[bptr] and 0xff.toByte()).toInt()
                --i
                bptr++
            }
            words[--nwords] = word
            // Elements remaining in byte[] are a multiple of 4.
            while (nwords > 0) {
                words[--nwords] = bytes[bptr++].toInt() shl 24 or
                        ((bytes[bptr++] and 0xff.toByte()).toInt() shl 16) or
                        ((bytes[bptr++] and 0xff.toByte()).toInt() shl 8) or
                        (bytes[bptr++] and 0xff.toByte()).toInt()
            }
            return words
        }

        /**
         * Allocate a new non-shared BigInteger.
         *
         * @param nwords number of words to allocate
         */
        private fun alloc(nwords: Int): BigInteger {
            val result = BigInteger()
            if (nwords > 1) {
                result.words = IntArray(nwords)
            }
            return result
        }

        private fun compareTo(x: BigInteger?, y: BigInteger?): Int {
            if (x!!.words == null && y!!.words == null) {
                return if (x.ival < y.ival) -1 else if (x.ival > y.ival) 1 else 0
            }
            val x_negative = x.isNegative
            val y_negative = y!!.isNegative
            if (x_negative != y_negative) {
                return if (x_negative) -1 else 1
            }
            val x_len = if (x.words == null) 1 else x.ival
            val y_len = if (y.words == null) 1 else y.ival
            return if (x_len != y_len) {
                if (x_len > y_len != x_negative) 1 else -1
            } else MPN.cmp(x.words, y.words, x_len)
        }

        /**
         * Calculate how many words are significant in words[0:len-1].
         * Returns the least value x such that x>0 && words[0:x-1]==words[0:len-1],
         * when words is viewed as a 2's complement integer.
         */
        private fun wordsNeeded(words: IntArray?, len: Int): Int {
            var i = len
            if (i > 0) {
                var word = words!![--i]
                if (word == -1) {
                    while (i > 0 && words[i - 1].also { word = it } < 0) {
                        i--
                        if (word != -1) {
                            break
                        }
                    }
                } else {
                    while (word == 0 && i > 0 && words[i - 1].also { word = it } >= 0) {
                        i--
                    }
                }
            }
            return i + 1
        }

        /**
         * Add two ints, yielding a BigInteger.
         */
        private fun add(x: Int, y: Int): BigInteger? {
            return valueOf(x.toLong() + y.toLong())
        }

        /**
         * Add a BigInteger and an int, yielding a new BigInteger.
         */
        private fun add(x: BigInteger?, y: Int): BigInteger? {
            if (x!!.words == null) {
                return add(x.ival, y)
            }
            val result = BigInteger(0)
            result.setAdd(x, y)
            return result.canonicalize()
        }

        /**
         * Add two BigIntegers, yielding their sum as another BigInteger.
         */
        private fun add(
            x: BigInteger?,
            y: BigInteger?,
            k: Int
        ): BigInteger? {
            var x = x
            var y = y
            if (x!!.words == null && y!!.words == null) {
                return valueOf(k.toLong() * y.ival.toLong() + x.ival.toLong())
            }
            if (k != 1) {
                y = if (k == -1) {
                    neg(y)
                } else {
                    times(
                        y,
                        valueOf(k.toLong())
                    )
                }
            }
            if (x.words == null) {
                return add(y, x.ival)
            }
            if (y!!.words == null) {
                return add(x, y.ival)
            }
            // Both are big
            if (y.ival > x.ival) { // Swap so x is longer then y.
                val tmp = x
                x = y
                y = tmp
            }
            val result = alloc(x.ival + 1)
            var i = y.ival
            var carry = MPN.add_n(result.words, x.words, y.words, i).toLong()
            var y_ext = if (y.words!![i - 1] < 0) 0xffffffffL else 0
            while (i < x.ival) {
                carry += (x.words!![i].toLong() and 0xffffffffL) + y_ext
                result.words!![i] = carry.toInt()
                carry = carry ushr 32
                i++
            }
            if (x.words!![i - 1] < 0) {
                y_ext--
            }
            result.words!![i] = (carry + y_ext).toInt()
            result.ival = i + 1
            return result.canonicalize()
        }

        private fun times(x: BigInteger?, y: Int): BigInteger? {
            var y = y
            if (y == 0) {
                return ZERO
            }
            if (y == 1) {
                return x
            }
            var xwords = x!!.words
            val xlen = x.ival
            if (xwords == null) {
                return valueOf(xlen.toLong() * y.toLong())
            }
            var negative: Boolean
            val result = alloc(xlen + 1)
            if (xwords[xlen - 1] < 0) {
                negative = true
                negate(result.words, xwords, xlen)
                xwords = result.words
            } else {
                negative = false
            }
            if (y < 0) {
                negative = !negative
                y = -y
            }
            result.words!![xlen] = MPN.mul_1(result.words, xwords, xlen, y)
            result.ival = xlen + 1
            if (negative) {
                result.setNegative()
            }
            return result.canonicalize()
        }

        private fun times(
            x: BigInteger?,
            y: BigInteger?
        ): BigInteger? {
            if (y!!.words == null) {
                return times(x, y.ival)
            }
            if (x!!.words == null) {
                return times(y, x.ival)
            }
            var negative = false
            var xwords: IntArray?
            var ywords: IntArray?
            var xlen = x.ival
            var ylen = y.ival
            if (x.isNegative) {
                negative = true
                xwords = IntArray(xlen)
                negate(xwords, x.words, xlen)
            } else {
                negative = false
                xwords = x.words
            }
            if (y.isNegative) {
                negative = !negative
                ywords = IntArray(ylen)
                negate(ywords, y.words, ylen)
            } else {
                ywords = y.words
            }
            // Swap if x is shorter then y.
            if (xlen < ylen) {
                val twords = xwords
                xwords = ywords
                ywords = twords
                val tlen = xlen
                xlen = ylen
                ylen = tlen
            }
            val result = alloc(xlen + ylen)
            MPN.mul(result.words, xwords, xlen, ywords, ylen)
            result.ival = xlen + ylen
            if (negative) {
                result.setNegative()
            }
            return result.canonicalize()
        }

        private fun divide(
            x: Long, y: Long,
            quotient: BigInteger?, remainder: BigInteger?,
            rounding_mode: Int
        ) {
            var x = x
            var y = y
            var xNegative: Boolean
            val yNegative: Boolean
            if (x < 0) {
                xNegative = true
                if (x == Long.MIN_VALUE) {
                    divide(
                        valueOf(x),
                        valueOf(y),
                        quotient,
                        remainder,
                        rounding_mode
                    )
                    return
                }
                x = -x
            } else {
                xNegative = false
            }
            if (y < 0) {
                yNegative = true
                if (y == Long.MIN_VALUE) {
                    if (rounding_mode == TRUNCATE) { // x != Long.Min_VALUE implies abs(x) < abs(y)
                        quotient?.set(0)
                        remainder?.set(x)
                    } else {
                        divide(
                            valueOf(x),
                            valueOf(y),
                            quotient,
                            remainder,
                            rounding_mode
                        )
                    }
                    return
                }
                y = -y
            } else {
                yNegative = false
            }
            var q = x / y
            var r = x % y
            val qNegative = xNegative xor yNegative
            var add_one = false
            if (r != 0L) {
                when (rounding_mode) {
                    TRUNCATE -> {
                    }
                    CEILING, FLOOR -> if (qNegative == (rounding_mode == FLOOR)) {
                        add_one = true
                    }
                    ROUND -> add_one = r > y - (q and 1) shr 1
                }
            }
            if (quotient != null) {
                if (add_one) {
                    q++
                }
                if (qNegative) {
                    q = -q
                }
                quotient.set(q)
            }
            if (remainder != null) { // The remainder is by definition: X-Q*Y
                if (add_one) { // Subtract the remainder from Y.
                    r = y - r
                    // In this case, abs(Q*Y) > abs(X).
// So sign(remainder) = -sign(X).
                    xNegative = !xNegative
                } else { // If !add_one, then: abs(Q*Y) <= abs(X).
// So sign(remainder) = sign(X).
                }
                if (xNegative) {
                    r = -r
                }
                remainder.set(r)
            }
        }

        /**
         * Divide two integers, yielding quotient and remainder.
         *
         * @param x             the numerator in the division
         * @param y             the denominator in the division
         * @param quotient      is set to the quotient of the result (iff quotient!=null)
         * @param remainder     is set to the remainder of the result
         * (iff remainder!=null)
         * @param rounding_mode one of FLOOR, CEILING, TRUNCATE, or ROUND.
         */
        private fun divide(
            x: BigInteger?, y: BigInteger?,
            quotient: BigInteger?, remainder: BigInteger?,
            rounding_mode: Int
        ) {
            if ((x!!.words == null || x.ival <= 2)
                && (y!!.words == null || y.ival <= 2)
            ) {
                val x_l = x.toLong()
                val y_l = y.toLong()
                if (x_l != Long.MIN_VALUE && y_l != Long.MIN_VALUE) {
                    divide(x_l, y_l, quotient, remainder, rounding_mode)
                    return
                }
            }
            val xNegative = x.isNegative
            val yNegative = y!!.isNegative
            val qNegative = xNegative xor yNegative
            var ylen = if (y.words == null) 1 else y.ival
            var ywords = IntArray(ylen)
            y.getAbsolute(ywords)
            while (ylen > 1 && ywords[ylen - 1] == 0) {
                ylen--
            }
            var xlen = if (x.words == null) 1 else x.ival
            var xwords = IntArray(xlen + 2)
            x.getAbsolute(xwords)
            while (xlen > 1 && xwords[xlen - 1] == 0) {
                xlen--
            }
            var qlen: Int
            var rlen: Int
            val cmpval = MPN.cmp(xwords, xlen, ywords, ylen)
            if (cmpval < 0) // abs(x) < abs(y)
            { // quotient = 0;  remainder = num.
                val rwords = xwords
                xwords = ywords
                ywords = rwords
                rlen = xlen
                qlen = 1
                xwords[0] = 0
            } else if (cmpval == 0) // abs(x) == abs(y)
            {
                xwords[0] = 1
                qlen = 1 // quotient = 1
                ywords[0] = 0
                rlen = 1 // remainder = 0;
            } else if (ylen == 1) {
                qlen = xlen
                // Need to leave room for a word of leading zeros if dividing by 1
// and the dividend has the high bit set.  It might be safe to
// increment qlen in all cases, but it certainly is only necessary
// in the following case.
                if (ywords[0] == 1 && xwords[xlen - 1] < 0) {
                    qlen++
                }
                rlen = 1
                ywords[0] = MPN.divmod_1(xwords, xwords, xlen, ywords[0])
            } else  // abs(x) > abs(y)
            { // Normalize the denominator, i.e. make its most significant bit set by
// shifting it normalization_steps bits to the left.  Also shift the
// numerator the same number of steps (to keep the quotient the same!).
                val nshift = MPN.count_leading_zeros(ywords[ylen - 1])
                if (nshift != 0) { // Shift up the denominator setting the most significant bit of
// the most significant word.
                    MPN.lshift(ywords, 0, ywords, ylen, nshift)
                    // Shift up the numerator, possibly introducing a new most
// significant word.
                    val x_high = MPN.lshift(xwords, 0, xwords, xlen, nshift)
                    xwords[xlen++] = x_high
                }
                if (xlen == ylen) {
                    xwords[xlen++] = 0
                }
                MPN.divide(xwords, xlen, ywords, ylen)
                rlen = ylen
                MPN.rshift0(ywords, xwords, 0, rlen, nshift)
                qlen = xlen + 1 - ylen
                if (quotient != null) {
                    for (i in 0 until qlen) {
                        xwords[i] = xwords[i + ylen]
                    }
                }
            }
            if (ywords[rlen - 1] < 0) {
                ywords[rlen] = 0
                rlen++
            }
            // Now the quotient is in xwords, and the remainder is in ywords.
            var add_one = false
            if (rlen > 1 || ywords[0] != 0) { // Non-zero remainder i.e. in-exact quotient.
                when (rounding_mode) {
                    TRUNCATE -> {
                    }
                    CEILING, FLOOR -> if (qNegative == (rounding_mode == FLOOR)) {
                        add_one = true
                    }
                    ROUND -> {
                        // int cmp = compareTo(remainder<<1, abs(y));
                        var tmp: BigInteger? =
                            remainder ?: BigInteger()
                        tmp!![ywords] = rlen
                        tmp = shift(tmp, 1)
                        if (yNegative) {
                            tmp!!.setNegative()
                        }
                        var cmp = compareTo(tmp, y)
                        // Now cmp == compareTo(sign(y)*(remainder<<1), y)
                        if (yNegative) {
                            cmp = -cmp
                        }
                        add_one = cmp == 1 || cmp == 0 && xwords[0] and 1 != 0
                    }
                }
            }
            if (quotient != null) {
                quotient[xwords] = qlen
                if (qNegative) {
                    if (add_one) // -(quotient + 1) == ~(quotient)
                    {
                        quotient.setInvert()
                    } else {
                        quotient.setNegative()
                    }
                } else if (add_one) {
                    quotient.setAdd(1)
                }
            }
            if (remainder != null) { // The remainder is by definition: X-Q*Y
                remainder[ywords] = rlen
                if (add_one) { // Subtract the remainder from Y:
// abs(R) = abs(Y) - abs(orig_rem) = -(abs(orig_rem) - abs(Y)).
                    val tmp: BigInteger?
                    if (y.words == null) {
                        tmp = remainder
                        tmp.set(if (yNegative) (ywords[0] + y.ival).toLong() else (ywords[0] - y.ival).toLong())
                    } else {
                        tmp = add(remainder, y, if (yNegative) 1 else -1)
                    }
                    // Now tmp <= 0.
// In this case, abs(Q) = 1 + floor(abs(X)/abs(Y)).
// Hence, abs(Q*Y) > abs(X).
// So sign(remainder) = -sign(X).
                    if (xNegative) {
                        remainder.setNegative(tmp)
                    } else {
                        remainder.set(tmp)
                    }
                } else { // If !add_one, then: abs(Q*Y) <= abs(X).
                    // So sign(remainder) = sign(X).
                    if (xNegative) {
                        remainder.setNegative()
                    }
                }
            }

        }

        private fun euclidInv(a: Int, b: Int, prevDiv: Int): IntArray {
            var a = a
            if (b == 0) {
                throw ArithmeticException("not invertible")
            }
            if (b == 1) // Success:  values are indeed invertible!
// Bottom of the recursion reached; start unwinding.
            {
                return intArrayOf(-prevDiv, 1)
            }
            val xy =
                euclidInv(b, a % b, a / b) // Recursion happens here.
            a = xy[0] // use our local copy of 'a' as a work var
            xy[0] = a * -prevDiv + xy[1]
            xy[1] = a
            return xy
        }

        private fun euclidInv(
            a: BigInteger?, b: BigInteger,
            prevDiv: BigInteger, xy: Array<BigInteger?>
        ) {
            if (b.isZero) {
                throw ArithmeticException("not invertible")
            }
            if (b.isOne) { // Success:  values are indeed invertible!
// Bottom of the recursion reached; start unwinding.
                xy[0] = neg(prevDiv)
                xy[1] = ONE
                return
            }
            // Recursion happens in the following conditional!
// If a just contains an int, then use integer math for the rest.
            if (a!!.words == null) {
                val xyInt =
                    euclidInv(b.ival, a.ival % b.ival, a.ival / b.ival)
                xy[0] = BigInteger(xyInt[0])
                xy[1] = BigInteger(xyInt[1])
            } else {
                val rem = BigInteger()
                val quot = BigInteger()
                divide(
                    a,
                    b,
                    quot,
                    rem,
                    FLOOR
                )
                // quot and rem may not be in canonical form. ensure
                rem.canonicalize()
                quot.canonicalize()
                euclidInv(b, rem, quot, xy)
            }
            val t = xy[0]
            xy[0] = add(
                xy[1],
                times(t, prevDiv),
                -1
            )
            xy[1] = t
        }

        /**
         * Calculate Greatest Common Divisor for non-negative ints.
         */
        private fun gcd(a: Int, b: Int): Int { // Euclid's algorithm, copied from libg++.
            var a = a
            var b = b
            var tmp: Int
            if (b > a) {
                tmp = a
                a = b
                b = tmp
            }
            while (true) {
                if (b == 0) {
                    return a
                }
                if (b == 1) {
                    return b
                }
                tmp = b
                b = a % b
                a = tmp
            }
        }

        private fun shift(x: BigInteger?, count: Int): BigInteger? {
            if (x!!.words == null) {
                if (count <= 0) {
                    val l: Long = if (count > -32) (x.ival.toLong() shr -count) else if (x.ival < 0) -1 else 0
                    return valueOf(l)
                }
                if (count < 32) {
                    return valueOf(x.ival.toLong() shl count)
                }
            }
            if (count == 0) {
                return x
            }
            val result = BigInteger(0)
            result.setShift(x, count)
            return result.canonicalize()
        }

        /* Assumes x and y are both canonicalized. */
        private fun equals(x: BigInteger, y: BigInteger): Boolean {
            if (x.words == null && y.words == null) {
                return x.ival == y.ival
            }
            if (x.words == null || y.words == null || x.ival != y.ival) {
                return false
            }
            var i = x.ival
            while (--i >= 0) {
                if (x.words!![i] != y.words!![i]) {
                    return false
                }
            }
            return true
        }

        private fun valueOf(
            digits: ByteArray, byte_len: Int,
            negative: Boolean, radix: Int
        ): BigInteger? {
            val chars_per_word = MPN.chars_per_word(radix)
            val words = IntArray(byte_len / chars_per_word + 1)
            var size = MPN.set_str(words, digits, byte_len, radix)
            if (size == 0) {
                return ZERO
            }
            if (words[size - 1] < 0) {
                words[size++] = 0
            }
            if (negative) {
                negate(words, words, size)
            }
            return make(words, size)
        }

        /**
         * Set dest[0:len-1] to the negation of src[0:len-1].
         * Return true if overflow (i.e. if src is -2**(32*len-1)).
         * Ok for src==dest.
         */
        private fun negate(dest: IntArray?, src: IntArray?, len: Int): Boolean {
            var carry: Long = 1
            val negative = src!![len - 1] < 0
            for (i in 0 until len) {
                carry += src[i].inv().toLong() and 0xffffffffL
                dest!![i] = carry.toInt()
                carry = carry shr 32
            }
            return negative && dest!![len - 1] < 0
        }

        private fun abs(x: BigInteger): BigInteger? {
            return if (x.isNegative) neg(x) else x
        }

        private fun neg(x: BigInteger?): BigInteger? {
            if (x!!.words == null && x.ival != Int.MIN_VALUE) {
                return valueOf(-x.ival.toLong())
            }
            val result = BigInteger(0)
            result.setNegative(x)
            return result.canonicalize()
        }

        /**
         * Return the boolean opcode (for bitOp) for swapped operands.
         * I.e. bitOp(swappedOp(op), x, y) == bitOp(op, y, x).
         */
        private fun swappedOp(op: Int): Int {
            return "\u0000\u0001\u0004\u0005\u0002\u0003\u0006\u0007\u0008\u0009\u000c\u000d\u000a\u000b\u000e\u000f"[op].toInt()
        }

        /**
         * Do one the the 16 possible bit-wise operations of two BigIntegers.
         */
        private fun bitOp(
            op: Int,
            x: BigInteger,
            y: BigInteger?
        ): BigInteger? {
            when (op) {
                0 -> return ZERO
                1 -> return x.and(y)
                3 -> return x
                5 -> return y
                15 -> return valueOf(-1)
            }
            val result = BigInteger()
            setBitOp(result, op, x, y)
            return result.canonicalize()
        }

        /**
         * Do one the the 16 possible bit-wise operations of two BigIntegers.
         */
        private fun setBitOp(
            result: BigInteger, op: Int,
            x: BigInteger, y: BigInteger?
        ) {
            var op = op
            var x: BigInteger? = x
            var y = y
            if (y!!.words != null && (x!!.words == null || x.ival < y.ival)) {
                val temp = x
                x = y
                y = temp
                op = swappedOp(op)
            }
            var xi: Int
            var yi: Int
            val xlen: Int
            val ylen: Int
            if (y.words == null) {
                yi = y.ival
                ylen = 1
            } else {
                yi = y.words!![0]
                ylen = y.ival
            }
            if (x!!.words == null) {
                xi = x.ival
                xlen = 1
            } else {
                xi = x.words!![0]
                xlen = x.ival
            }
            if (xlen > 1) {
                result.realloc(xlen)
            }
            val w = result.words
            var i = 0
            // Code for how to handle the remainder of x.
// 0:  Truncate to length of y.
// 1:  Copy rest of x.
// 2:  Invert rest of x.
            var finish = 0
            var ni: Int
            when (op) {
                0 -> ni = 0
                1 -> {
                    while (true) {
                        ni = xi and yi
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi < 0) {
                        finish = 1
                    }
                }
                2 -> {
                    while (true) {
                        ni = xi and yi.inv()
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi >= 0) {
                        finish = 1
                    }
                }
                3 -> {
                    ni = xi
                    finish = 1 // Copy rest
                }
                4 -> {
                    while (true) {
                        ni = xi.inv() and yi
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi < 0) {
                        finish = 2
                    }
                }
                5 -> while (true) {
                    ni = yi
                    if (i + 1 >= ylen) {
                        break
                    }
                    w!![i++] = ni
                    xi = x.words!![i]
                    yi = y.words!![i]
                }
                6 -> {
                    while (true) {
                        ni = xi xor yi
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    finish = if (yi < 0) 2 else 1
                }
                7 -> {
                    while (true) {
                        ni = xi or yi
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi >= 0) {
                        finish = 1
                    }
                }
                8 -> {
                    while (true) {
                        ni = (xi or yi).inv()
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi >= 0) {
                        finish = 2
                    }
                }
                9 -> {
                    while (true) {
                        ni = (xi xor yi).inv()
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    finish = if (yi >= 0) 2 else 1
                }
                10 -> while (true) {
                    ni = yi.inv()
                    if (i + 1 >= ylen) {
                        break
                    }
                    w!![i++] = ni
                    xi = x.words!![i]
                    yi = y.words!![i]
                }
                11 -> {
                    while (true) {
                        ni = xi or yi.inv()
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi < 0) {
                        finish = 1
                    }
                }
                12 -> {
                    ni = xi.inv()
                    finish = 2
                }
                13 -> {
                    while (true) {
                        ni = xi.inv() or yi
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi >= 0) {
                        finish = 2
                    }
                }
                14 -> {
                    while (true) {
                        ni = (xi and yi).inv()
                        if (i + 1 >= ylen) {
                            break
                        }
                        w!![i++] = ni
                        xi = x.words!![i]
                        yi = y.words!![i]
                    }
                    if (yi < 0) {
                        finish = 2
                    }
                }
                15 -> ni = -1
                else -> ni = -1
            }
            // Here i==ylen-1; w[0]..w[i-1] have the correct result;
// and ni contains the correct result for w[i+1].
            if (i + 1 == xlen) {
                finish = 0
            }
            when (finish) {
                0 -> {
                    if (i == 0 && w == null) {
                        result.ival = ni
                        return
                    }
                    w!![i++] = ni
                }
                1 -> {
                    w!![i] = ni
                    while (++i < xlen) {
                        w[i] = x.words!![i]
                    }
                }
                2 -> {
                    w!![i] = ni
                    while (++i < xlen) {
                        w[i] = x.words!![i].inv()
                    }
                }
            }
            result.ival = i
        }

        /**
         * Return the logical (bit-wise) "and" of a BigInteger and an int.
         */
        private fun and(x: BigInteger?, y: Int): BigInteger? {
            if (x!!.words == null) {
                return valueOf((x.ival and y.toLong().toInt()).toLong())
            }
            if (y >= 0) {
                return valueOf((x.words!![0] and y.toLong().toInt()).toLong())
            }
            var len = x.ival
            val words = IntArray(len)
            words[0] = x.words!![0] and y
            while (--len > 0) {
                words[len] = x.words!![len]
            }
            return make(words, x.ival)
        }

        // bit4count[I] is number of '1' bits in I.
        private val bit4_count = byteArrayOf(
            0, 1, 1, 2, 1, 2, 2, 3,
            1, 2, 2, 3, 2, 3, 3, 4
        )

        private fun bitCount(i: Int): Int {
            var i = i
            var count = 0
            while (i != 0) {
                count += bit4_count[i and 15]
                i = i ushr 4
            }
            return count
        }

        private fun bitCount(x: IntArray, len: Int): Int {
            var len = len
            var count = 0
            while (--len >= 0) {
                count += bitCount(x[len])
            }
            return count
        }

        init {
            smallFixNums = arrayOfNulls(numFixNum)
            var i = numFixNum
            while (--i >= 0) {
                smallFixNums[i] = BigInteger(i + minFixNum)
            }
            ZERO = smallFixNums[-minFixNum]!!
            ONE = smallFixNums[1 - minFixNum]!!
            TEN = smallFixNums[10 - minFixNum]!!
        }
    }

    private constructor() : super() {}
    /* Create a new (non-shared) BigInteger, and initialize to an int. */
    private constructor(value: Int) : super() {
        ival = value
    }

    constructor(s: String, radix: Int) : this() {
        val len = s.length
        var i: Int
        var digit: Int
        val negative: Boolean
        val bytes: ByteArray
        var ch = s[0]
        if (ch == '-') {
            negative = true
            i = 1
            bytes = ByteArray(len - 1)
        } else {
            negative = false
            i = 0
            bytes = ByteArray(len)
        }
        var byte_len = 0
        while (i < len) {
            ch = s[i]
            digit = Character.digit(ch, radix)
            if (digit < 0) {
                throw NumberFormatException("Invalid character at position #$i")
            }
            bytes[byte_len++] = digit.toByte()
            i++
        }
        val result: BigInteger?
        // Testing (len < MPN.chars_per_word(radix)) would be more accurate,
// but slightly more expensive, for little practical gain.
        result = if (len <= 15 && radix <= 16) {
            valueOf(s.toLong(radix))
        } else {
            valueOf(bytes, byte_len, negative, radix)
        }
        ival = result!!.ival
        words = result.words
    }

    constructor(`val`: String) : this(`val`, 10) {}
    /* Create a new (non-shared) BigInteger, and initialize from a byte array. */
    constructor(`val`: ByteArray?) : this() {
        if (`val` == null || `val`.size < 1) {
            throw NumberFormatException()
        }
        words = byteArrayToIntArray(`val`, if (`val`[0] < 0) -1 else 0)
        val result = make(words, words!!.size)
        ival = result!!.ival
        words = result.words
    }

    constructor(signum: Int, magnitude: ByteArray?) : this() {
        if (magnitude == null || signum > 1 || signum < -1) {
            throw NumberFormatException()
        }
        if (signum == 0) {
            var i: Int
            i = magnitude.size - 1
            while (i >= 0 && magnitude[i].toInt() == 0) {
                --i
            }
            if (i >= 0) {
                throw NumberFormatException()
            }
            return
        }
        // Magnitude is always positive, so don't ever pass a sign of -1.
        words = byteArrayToIntArray(magnitude, 0)
        val result = make(words, words!!.size)
        ival = result!!.ival
        words = result.words
        if (signum < 0) {
            setNegative()
        }
    }

    constructor(numBits: Int, rnd: Random) : this() {
        require(numBits >= 0)
        init(numBits, rnd)
    }

    private fun init(numBits: Int, rnd: Random) {
        var highbits = numBits and 31
        // minimum number of bytes to store the above number of bits
        val highBitByteCount = (highbits + 7) / 8
        // number of bits to discard from the last byte
        var discardedBitCount = highbits % 8
        if (discardedBitCount != 0) {
            discardedBitCount = 8 - discardedBitCount
        }
        val highBitBytes = ByteArray(highBitByteCount)
        if (highbits > 0) {
            rnd.nextBytes(highBitBytes)
            highbits = (highBitBytes[highBitByteCount - 1] and 0xFF.toByte()).toInt() ushr discardedBitCount
            for (i in highBitByteCount - 2 downTo 0) {
                highbits = highbits shl 8 or (highBitBytes[i] and 0xFF.toByte()).toInt()
            }
        }
        var nwords = numBits / 32
        while (highbits == 0 && nwords > 0) {
            highbits = rnd.nextInt()
            --nwords
        }
        if (nwords == 0 && highbits >= 0) {
            ival = highbits
        } else {
            ival = if (highbits < 0) nwords + 2 else nwords + 1
            words = IntArray(ival)
            words!![nwords] = highbits
            while (--nwords >= 0) {
                words!![nwords] = rnd.nextInt()
            }
        }
    }

    constructor(bitLength: Int, certainty: Int, rnd: Random) : this() {
        var result: BigInteger? = BigInteger()
        while (true) {
            result!!.init(bitLength, rnd)
            result = result.setBit(bitLength - 1)
            if (result!!.isProbablePrime(certainty)) {
                break
            }
        }
        ival = result!!.ival
        words = result.words
    }

    public fun getLowestSetBit(): Int {
        if (isZero) {
            return -1
        }
        return if (words == null) {
            MPN.findLowestBit(ival)
        } else {
            MPN.findLowestBit(words)
        }
    }


    /**
     * Change words.length to nwords.
     * We allow words.length to be upto nwords+2 without reallocating.
     */
    private fun realloc(nwords: Int) {
        if (nwords == 0) {
            if (words != null) {
                if (ival > 0) {
                    ival = words!![0]
                }
                words = null
            }
        } else if (words == null || words!!.size < nwords || words!!.size > nwords + 2
        ) {
            val new_words = IntArray(nwords)
            if (words == null) {
                new_words[0] = ival
                ival = 1
            } else {
                if (nwords < ival) {
                    ival = nwords
                }
                System.arraycopy(words, 0, new_words, 0, ival)
            }
            words = new_words
        }
    }

    private val isNegative: Boolean
        private get() = (if (words == null) ival else words!![ival - 1]) < 0

    fun signum(): Int {
        if (ival == 0 && words == null) {
            return 0
        }
        val top = if (words == null) ival else words!![ival - 1]
        return if (top < 0) -1 else 1
    }

    /**
     * @since 1.2
     */
    override fun compareTo(`val`: BigInteger?): Int {
        return compareTo(this, `val`)
    }

    fun min(`val`: BigInteger?): BigInteger {
        return if (compareTo(this, `val`) < 0) this else `val`!!
    }

    fun max(`val`: BigInteger?): BigInteger {
        return if (compareTo(this, `val`) > 0) this else `val`!!
    }

    private val isZero: Boolean
        private get() = words == null && ival == 0

    private val isOne: Boolean
        private get() = words == null && ival == 1

    private fun canonicalize(): BigInteger? {
        if (words != null
            && wordsNeeded(words, ival).also { ival = it } <= 1
        ) {
            if (ival == 1) {
                ival = words!![0]
            }
            words = null
        }
        return if (words == null && ival >= minFixNum && ival <= maxFixNum) {
            smallFixNums[ival - minFixNum]
        } else this
    }

    /**
     * Set this to the sum of x and y.
     * OK if x==this.
     */
    private fun setAdd(x: BigInteger?, y: Int) {
        if (x!!.words == null) {
            set(x.ival.toLong() + y.toLong())
            return
        }
        val len = x.ival
        realloc(len + 1)
        var carry = y.toLong()
        for (i in 0 until len) {
            carry += x.words!![i].toLong() and 0xffffffffL
            words!![i] = carry.toInt()
            carry = carry shr 32
        }
        if (x.words!![len - 1] < 0) {
            carry--
        }
        words!![len] = carry.toInt()
        ival = wordsNeeded(words, len + 1)
    }

    /**
     * Destructively add an int to this.
     */
    private fun setAdd(y: Int) {
        setAdd(this, y)
    }

    /**
     * Destructively set the value of this to a long.
     */
    private fun set(y: Long) {
        val i = y.toInt()
        if (i.toLong() == y) {
            ival = i
            words = null
        } else {
            realloc(2)
            words!![0] = i
            words!![1] = (y shr 32).toInt()
            ival = 2
        }
    }

    /**
     * Destructively set the value of this to the given words.
     * The words array is reused, not copied.
     */
    private operator fun set(words: IntArray, length: Int) {
        ival = length
        this.words = words
    }

    /**
     * Destructively set the value of this to that of y.
     */
    private fun set(y: BigInteger?) {
        if (y!!.words == null) {
            set(y.ival.toLong())
        } else if (this !== y) {
            realloc(y.ival)
            System.arraycopy(y.words, 0, words, 0, y.ival)
            ival = y.ival
        }
    }

    fun add(`val`: BigInteger?): BigInteger? {
        return add(this, `val`, 1)
    }

    fun subtract(`val`: BigInteger?): BigInteger? {
        return add(this, `val`, -1)
    }

    fun multiply(y: BigInteger?): BigInteger? {
        return times(this, y)
    }

    fun divide(`val`: BigInteger?): BigInteger? {
        if (`val`!!.isZero) {
            throw ArithmeticException("divisor is zero")
        }
        val quot = BigInteger()
        divide(
            this,
            `val`,
            quot,
            null,
            TRUNCATE
        )
        return quot.canonicalize()
    }

    fun remainder(`val`: BigInteger): BigInteger? {
        if (`val`.isZero) {
            throw ArithmeticException("divisor is zero")
        }
        val rem = BigInteger()
        divide(
            this,
            `val`,
            null,
            rem,
            TRUNCATE
        )
        return rem.canonicalize()
    }

    fun divideAndRemainder(`val`: BigInteger): Array<BigInteger?> {
        if (`val`.isZero) {
            throw ArithmeticException("divisor is zero")
        }
        val result = arrayOfNulls<BigInteger>(2)
        result[0] = BigInteger()
        result[1] = BigInteger()
        divide(
            this,
            `val`,
            result[0],
            result[1],
            TRUNCATE
        )
        result[0]!!.canonicalize()
        result[1]!!.canonicalize()
        return result
    }

    fun mod(m: BigInteger?): BigInteger? {
        if (m!!.isNegative || m.isZero) {
            throw ArithmeticException("non-positive modulus")
        }
        val rem = BigInteger()
        divide(this, m, null, rem, FLOOR)
        return rem.canonicalize()
    }

    /**
     * Calculate the integral power of a BigInteger.
     *
     * @param exponent the exponent (must be non-negative)
     */
    fun pow(exponent: Int): BigInteger? {
        var exponent1 = exponent
        if (exponent1 <= 0) {
            if (exponent1 == 0) {
                return ONE
            }
            throw ArithmeticException("negative exponent")
        }
        if (isZero) {
            return this
        }
        var plen = if (words == null) 1 else ival // Length of pow2.
        val blen = (bitLength() * exponent1 shr 5) + 2 * plen
        val negative = isNegative && exponent1 and 1 != 0
        var pow2 = IntArray(blen)
        var rwords = IntArray(blen)
        var work = IntArray(blen)
        getAbsolute(pow2) // pow2 = abs(this);
        var rlen = 1
        rwords[0] = 1 // rwords = 1;
        while (true) {
            // pow2 == this**(2**i)
// prod = this**(sum(j=0..i-1, (exponent>>j)&1))
            if (exponent1 and 1 != 0) { // r *= pow2
                MPN.mul(work, pow2, plen, rwords, rlen)
                val temp = work
                work = rwords
                rwords = temp
                rlen += plen
                while (rwords[rlen - 1] == 0) {
                    rlen--
                }
            }
            exponent1 = exponent1 shr 1
            if (exponent1 == 0) {
                break
            }
            // pow2 *= pow2;
            MPN.mul(work, pow2, plen, pow2, plen)
            val temp = work
            work = pow2
            pow2 = temp // swap to avoid a copy
            plen *= 2
            while (pow2[plen - 1] == 0) {
                plen--
            }
        }
        if (rwords[rlen - 1] < 0) {
            rlen++
        }
        if (negative) {
            negate(rwords, rwords, rlen)
        }
        return make(rwords, rlen)
    }

    fun modInverse(y: BigInteger?): BigInteger? {
        var y = y
        if (y!!.isNegative || y.isZero) {
            throw ArithmeticException("non-positive modulo")
        }
        // Degenerate cases.
        if (y.isOne) {
            return ZERO
        }
        if (isOne) {
            return ONE
        }
        // Use Euclid's algorithm as in gcd() but do this recursively
        // rather than in a loop so we can use the intermediate results as we
        // unwind from the recursion.
        // Used http://www.math.nmsu.edu/~crypto/EuclideanAlgo.html as reference.
        var result: BigInteger? = BigInteger()
        var swapped = false
        if (y.words == null) { // The result is guaranteed to be less than the modulus, y (which is
            // an int), so simplify this by working with the int result of this
            // modulo y.  Also, if this is negative, make it positive via modulo
            // math.  Note that BigInteger.mod() must be used even if this is
            // already an int as the % operator would provide a negative result if
            // this is negative, BigInteger.mod() never returns negative values.
            var xval = if (words != null || isNegative) mod(y)!!.ival else ival
            var yval = y.ival
            // Swap values so x > y.
            if (yval > xval) {
                val tmp = xval
                xval = yval
                yval = tmp
                swapped = true
            }
            // Normally, the result is in the 2nd element of the array, but
// if originally x < y, then x and y were swapped and the result
// is in the 1st element of the array.
            result!!.ival = euclidInv(yval, xval % yval, xval / yval)[if (swapped) 0 else 1]
            // Result can't be negative, so make it positive by adding the
// original modulus, y.ival (not the possibly "swapped" yval).
            if (result.ival < 0) {
                result.ival += y.ival
            }
        } else { // As above, force this to be a positive value via modulo math.
            var x = if (isNegative) this.mod(y) else this
            // Swap values so x > y.
            if (x!!.compareTo(y) < 0) {
                result = x
                x = y
                y = result // use 'result' as a work var
                swapped = true
            }
            // As above (for ints), result will be in the 2nd element unless
// the original x and y were swapped.
            val rem = BigInteger()
            val quot = BigInteger()
            divide(x, y, quot, rem, FLOOR)
            // quot and rem may not be in canonical form. ensure
            rem.canonicalize()
            quot.canonicalize()
            val xy = arrayOfNulls<BigInteger>(2)
            euclidInv(y, rem, quot, xy)
            result = if (swapped) xy[0] else xy[1]
            // Result can't be negative, so make it positive by adding the
// original modulus, y (which is now x if they were swapped).
            if (result!!.isNegative) {
                result = add(result, if (swapped) x else y, 1)
            }
        }
        return result
    }

    fun modPow(
        exponent: BigInteger?,
        m: BigInteger
    ): BigInteger? {
        if (m.isNegative || m.isZero) {
            throw ArithmeticException("non-positive modulo")
        }
        if (exponent!!.isNegative) {
            return modInverse(m)!!.modPow(exponent.negate(), m)
        }
        if (exponent.isOne) {
            return mod(m)
        }
        // To do this naively by first raising this to the power of exponent
        // and then performing modulo m would be extremely expensive, especially
        // for very large numbers.  The solution is found in Number Theory
        // where a combination of partial powers and moduli can be done easily.
        //
        // We'll use the algorithm for Additive Chaining which can be found on
        // p. 244 of "Applied Cryptography, Second Edition" by Bruce Schneier.
        var s: BigInteger? = ONE
        var t: BigInteger? = this
        var u = exponent
        while (!u!!.isZero) {
            if (u.and(ONE)!!.isOne) {
                s = times(s, t)!!.mod(m)
            }
            u = u.shiftRight(1)
            t = times(t, t)!!.mod(m)
        }
        return s
    }

    fun gcd(y: BigInteger): BigInteger? {
        var xval = ival
        var yval = y.ival
        if (words == null) {
            if (xval == 0) {
                return abs(y)
            }
            if (y.words == null && xval != Int.MIN_VALUE && yval != Int.MIN_VALUE
            ) {
                if (xval < 0) {
                    xval = -xval
                }
                if (yval < 0) {
                    yval = -yval
                }
                return valueOf(
                    gcd(
                        xval,
                        yval
                    ).toLong()
                )
            }
            xval = 1
        }
        if (y.words == null) {
            if (yval == 0) {
                return abs(this)
            }
            yval = 1
        }
        var len = (if (xval > yval) xval else yval) + 1
        val xwords = IntArray(len)
        val ywords = IntArray(len)
        getAbsolute(xwords)
        y.getAbsolute(ywords)
        len = MPN.gcd(xwords, ywords, len)
        val result = BigInteger(0)
        result.ival = len
        result.words = xwords
        return result.canonicalize()
    }

    /**
     *
     * Returns `true` if this BigInteger is probably prime,
     * `false` if it's definitely composite. If `certainty`
     * is `<= 0`, `true` is returned.
     *
     * @param certainty a measure of the uncertainty that the caller is willing
     * to tolerate: if the call returns `true` the probability that
     * this BigInteger is prime exceeds `(1 - 1/2<sup>certainty</sup>)`.
     * The execution time of this method is proportional to the value of this
     * parameter.
     * @return `true` if this BigInteger is probably prime,
     * `false` if it's definitely composite.
     */
    fun isProbablePrime(certainty: Int): Boolean {
        if (certainty < 1) {
            return true
        }
        /** We'll use the Rabin-Miller algorithm for doing a probabilistic
         * primality test.  It is fast, easy and has faster decreasing odds of a
         * composite passing than with other tests.  This means that this
         * method will actually have a probability much greater than the
         * 1 - .5^certainty specified in the JCL (p. 117), but I don't think
         * anyone will complain about better performance with greater certainty.
         *
         * The Rabin-Miller algorithm can be found on pp. 259-261 of "Applied
         * Cryptography, Second Edition" by Bruce Schneier.
         */
        // First rule out small prime factors
        val rem = BigInteger()
        var i = 0
        while (i < primes.size) {
            if (words == null && ival == primes[i]) {
                return true
            }
            divide(this, smallFixNums[primes[i] - minFixNum], null, rem, TRUNCATE)
            if (rem.canonicalize()!!.isZero) {
                return false
            }
            i++
        }
        // Now perform the Rabin-Miller test.
        // Set b to the number of times 2 evenly divides (this - 1).
        // I.e. 2^b is the largest power of 2 that divides (this - 1).
        val pMinus1 = add(this, -1)
        val b = pMinus1!!.getLowestSetBit()
        // Set m such that this = 1 + 2^b * m.
        val m = pMinus1.divide(valueOf(2L)!!.pow(b))
        // The HAC (Handbook of Applied Cryptography), Alfred Menezes & al. Note
        // 4.49 (controlling the error probability) gives the number of trials
        // for an error probability of 1/2**80, given the number of bits in the
        // number to test.  we shall use these numbers as is if/when 'certainty'
        // is less or equal to 80, and twice as much if it's greater.
        val bits = bitLength()
        i = 0
        while (i < k.size) {
            if (bits <= k[i]) {
                break
            }
            i++
        }
        var trials = t[i]
        if (certainty > 80) {
            trials *= 2
        }
        var z: BigInteger?
        for (t in 0 until trials) { // The HAC (Handbook of Applied Cryptography), Alfred Menezes & al.
            // Remark 4.28 states: "...A strategy that is sometimes employed
            // is to fix the bases a to be the first few primes instead of
            // choosing them at random.
            z = smallFixNums[primes[t] - minFixNum]!!.modPow(m, this)
            if (z!!.isOne || z == pMinus1) {
                continue  // Passes the test; may be prime.
            }
            i = 0
            while (i < b) {
                if (z!!.isOne) {
                    return false
                }
                i++
                if (z == pMinus1) {
                    break // Passes the test; may be prime.
                }
                z = z.modPow(valueOf(2), this)
            }
            if (i == b && z != pMinus1) {
                return false
            }
        }
        return true
    }

    private fun setInvert() {
        if (words == null) {
            ival = ival.inv()
        } else {
            var i = ival
            while (--i >= 0) {
                words!![i] = words!![i].inv()
            }
        }
    }

    private fun setShiftLeft(x: BigInteger, cnt: Int) {
        var count = cnt
        val xwords: IntArray?
        val xlen: Int
        if (x.words == null) {
            if (count < 32) {
                set(x.ival.toLong() shl count);
                return;
            }
            xwords = IntArray(1);
            xwords[0] = x.ival;
            xlen = 1;
        } else {
            xwords = x.words;
            xlen = x.ival;
        }
        val word_count: Int = count shr 5
        count = count and 31;
        var new_len: Int = xlen + word_count;
        if (count == 0) {
            realloc(new_len);
            var i = xlen
            while (--i >= 0) {
                words!![i + word_count] = xwords!![i]
            }
        } else {
            new_len++;
            realloc(new_len);
            val shift_out: Int = MPN.lshift(words, word_count, xwords, xlen, count);
            count = 32 - count;
            words!![new_len - 1] = (shift_out shl count) shr count  // sign-extend.
        }
        ival = new_len;
        var i = word_count
        while (--i >= 0) {
            words!![i] = 0;
        }
    }

    private fun setShiftRight(x: BigInteger?, cnt: Int) {
        var count = cnt
        if (x!!.words == null) {
            val l: Long = if (count < 32) (x.ival.toLong() shr count) else if (x.ival < 0) -1L else 0L
            set(l)
        } else if (count == 0) {
            set(x)
        } else {
            val neg = x.isNegative
            val word_count = count shr 5
            count = count and 31
            val d_len = x.ival - word_count
            if (d_len <= 0) {
                set(if (neg) -1L else 0L)
            } else {
                if (words == null || words!!.size < d_len) {
                    realloc(d_len)
                }
                MPN.rshift0(words, x.words, word_count, d_len, count)
                ival = d_len
                if (neg) {
                    words!![d_len - 1] = words!![d_len - 1] or (-2 shl (31 - count))
                }
            }
        }
    }

    private fun setShift(x: BigInteger?, count: Int) {
        if (count > 0) {
            setShiftLeft(x!!, count)
        } else {
            setShiftRight(x, -count)
        }
    }

    fun shiftLeft(n: Int): BigInteger? {
        return if (n == 0) {
            this
        } else shift(this, n)
    }

    fun shiftRight(n: Int): BigInteger? {
        return if (n == 0) {
            this
        } else shift(this, -n)
    }

    private fun format(radix: Int, buffer: StringBuilder) {
        if (words == null) {
            buffer.append(ival.toString(radix))
        } else if (ival <= 2) {
            buffer.append(toLong().toString(radix))
        } else {
            val neg = isNegative
            val work: IntArray
            if (neg || radix != 16) {
                work = IntArray(ival)
                getAbsolute(work)
            } else {
                work = words!!
            }
            var len = ival
            if (radix == 16) {
                if (neg) {
                    buffer.append('-')
                }
                val buf_start = buffer.length
                var i = len
                while (--i >= 0) {
                    val word = work[i]
                    var j = 8
                    while (--j >= 0) {
                        val hex_digit = word shr 4 * j and 0xF
                        // Suppress leading zeros:
                        if (hex_digit > 0 || buffer.length > buf_start) {
                            buffer.append(Character.forDigit(hex_digit, 16))
                        }
                    }
                }
            } else {
                var i = buffer.length
                while (true) {
                    val digit = MPN.divmod_1(work, work, len, radix)
                    buffer.append(Character.forDigit(digit, radix))
                    while (len > 0 && work[len - 1] == 0) {
                        len--
                    }
                    if (len == 0) {
                        break
                    }
                }
                if (neg) {
                    buffer.append('-')
                }
                /* Reverse buffer. */
                var j = buffer.length - 1
                while (i < j) {
                    val tmp = buffer[i]
                    buffer.setCharAt(i, buffer[j])
                    buffer.setCharAt(j, tmp)
                    i++
                    j--
                }
            }
        }
    }

    override fun toString(): String {
        return toString(10)
    }

    fun toString(radix: Int): String {
        if (words == null) {
            return ival.toString(radix)
        }
        if (ival <= 2) {
            return toLong().toString(radix)
        }
        val buf_size = ival * (MPN.chars_per_word(radix) + 1)
        val buffer = StringBuilder(buf_size)
        format(radix, buffer)
        return buffer.toString()
    }

    override fun toInt(): Int {
        return if (words == null) {
            ival
        } else words!![0]
    }

    override fun toLong(): Long {
        if (words == null) {
            return ival.toLong()
        }
        return if (ival == 1) {
            words!![0].toLong()
        } else (words!![1].toLong() shl 32) + (words!![0].toLong() and 0xffffffffL)
    }

    override fun toShort(): Short = toInt().toShort()

    override fun toByte(): Byte = toInt().toByte()

    override fun toChar(): Char = toInt().toChar()

    override fun hashCode(): Int { // FIXME: May not match hashcode of JDK.
        return if (words == null) ival else words!![0] + words!![ival - 1]
    }

    /* Assumes this and obj are both canonicalized. */
    override fun equals(obj: Any?): Boolean {
        return if (obj !is BigInteger) {
            false
        } else equals(this, obj)
    }

    override fun toDouble(): Double {
        if (words == null) {
            return ival.toDouble()
        }
        if (ival <= 2) {
            return toLong().toDouble()
        }
        return if (isNegative) {
            neg(this)!!.roundToDouble(0, true, false)
        } else roundToDouble(0, false, false)
    }

    override fun toFloat(): Float {
        return toDouble().toFloat()
    }

    /**
     * Return true if any of the lowest n bits are one.
     * (false if n is negative).
     */
    private fun checkBits(n: Int): Boolean {
        if (n <= 0) {
            return false
        }
        if (words == null) {
            return n > 31 || ival and (1 shl n) - 1 != 0
        }
        var i: Int
        i = 0
        while (i < n shr 5) {
            if (words!![i] != 0) {
                return true
            }
            i++
        }
        return n and 31 != 0 && words!![i] and (1 shl (n and 31)) - 1 != 0
    }

    /**
     * Convert a semi-processed BigInteger to double.
     * Number must be non-negative.  Multiplies by a power of two, applies sign,
     * and converts to double, with the usual java rounding.
     *
     * @param exp       power of two, positive or negative, by which to multiply
     * @param neg       true if negative
     * @param remainder true if the BigInteger is the result of a truncating
     * division that had non-zero remainder.  To ensure proper rounding in
     * this case, the BigInteger must have at least 54 bits.
     */
    private fun roundToDouble(exp: Int, neg: Boolean, remainder: Boolean): Double { // Compute length.
        var exp = exp
        val il = bitLength()
        // Exponent when normalized to have decimal point directly after
// leading one.  This is stored excess 1023 in the exponent bit field.
        exp += il - 1
        // Gross underflow.  If exp == -1075, we let the rounding
// computation determine whether it is minval or 0 (which are just
// 0x0000 0000 0000 0001 and 0x0000 0000 0000 0000 as bit
// patterns).
        if (exp < -1075) {
            return if (neg) -0.0 else 0.0
        }
        // gross overflow
        if (exp > 1023) {
            return if (neg) Double.NEGATIVE_INFINITY else Double.POSITIVE_INFINITY
        }
        // number of bits in mantissa, including the leading one.
// 53 unless it's denormalized
        val ml = if (exp >= -1022) 53 else 53 + exp + 1022
        // Get top ml + 1 bits.  The extra one is for rounding.
        var m: Long
        val excess_bits = il - (ml + 1)
        m = if (excess_bits > 0) {
            if (words == null) (ival shr excess_bits).toLong() else MPN.rshift_long(words, ival, excess_bits)
        } else {
            toLong() shl -excess_bits
        }
        // Special rounding for maxval.  If the number exceeds maxval by
// any amount, even if it's less than half a step, it overflows.
        if (exp == 1023 && m shr 1 == (1L shl 53) - 1) {
            return if (remainder || checkBits(il - ml)) {
                if (neg) Double.NEGATIVE_INFINITY else Double.POSITIVE_INFINITY
            } else {
                if (neg) -Double.MAX_VALUE else Double.MAX_VALUE
            }
        }
        // Normal round-to-even rule: round up if the bit dropped is a one, and
// the bit above it or any of the bits below it is a one.
        if (m and 1 == 1L && (m and 2 == 2L || remainder || checkBits(excess_bits))) {
            m += 2
            // Check if we overflowed the mantissa
            if (m and (1L shl 54) != 0L) {
                exp++
                // renormalize
                m = m shr 1
            } else if (ml == 52 && m and (1L shl 53) != 0L) {
                exp++
            }
        }
        // Discard the rounding bit
        m = m shr 1
        val bits_sign = if (neg) 1L shl 63 else 0
        exp += 1023
        val bits_exp = if (exp <= 0) 0 else exp.toLong() shl 52
        val bits_mant = m and (1L shl 52).inv()
        return java.lang.Double.longBitsToDouble(bits_sign or bits_exp or bits_mant)
    }

    /**
     * Copy the abolute value of this into an array of words.
     * Assumes words.length >= (this.words == null ? 1 : this.ival).
     * Result is zero-extended, but need not be a valid 2's complement number.
     */
    private fun getAbsolute(words: IntArray) {
        val len: Int
        if (this.words == null) {
            len = 1
            words[0] = ival
        } else {
            len = ival
            var i = len
            while (--i >= 0) {
                words[i] = this.words!![i]
            }
        }
        if (words[len - 1] < 0) {
            negate(words, words, len)
        }
        var i = words.size
        while (--i > len) {
            words[i] = 0
        }
    }

    /**
     * Destructively set this to the negative of x.
     * It is OK if x==this.
     */
    private fun setNegative(x: BigInteger?) {
        var len = x!!.ival
        if (x.words == null) {
            if (len == Int.MIN_VALUE) {
                set((-len).toLong())
            } else {
                set(-len.toLong())
            }
            return
        }
        realloc(len + 1)
        if (negate(words, x.words, len)) {
            words!![len++] = 0
        }
        ival = len
    }

    /**
     * Destructively negate this.
     */
    private fun setNegative() {
        setNegative(this)
    }

    fun abs(): BigInteger? {
        return abs(this)
    }

    fun negate(): BigInteger? {
        return neg(this)
    }

    /**
     * Calculates ceiling(log2(this < 0 ? -this : this+1))
     * See Common Lisp: the Language, 2nd ed, p. 361.
     */
    fun bitLength(): Int {
        return if (words == null) {
            MPN.intLength(ival)
        } else MPN.intLength(words, ival)
    }

    fun toByteArray(): ByteArray {
        if (signum() == 0) {
            return ByteArray(1)
        }
        // Determine number of bytes needed.  The method bitlength returns
// the size without the sign bit, so add one bit for that and then
// add 7 more to emulate the ceil function using integer math.
        val bytes = ByteArray((bitLength() + 1 + 7) / 8)
        var nbytes = bytes.size
        var wptr = 0
        var word: Int
        // Deal with words array until one word or less is left to process.
// If BigInteger is an int, then it is in ival and nbytes will be <= 4.
        while (nbytes > 4) {
            word = words!![wptr++]
            var i = 4
            while (i > 0) {
                bytes[--nbytes] = word.toByte()
                --i
                word = word shr 8
            }
        }
        // Deal with the last few bytes.  If BigInteger is an int, use ival.
        word = if (words == null) ival else words!![wptr]
        while (nbytes > 0) {
            bytes[--nbytes] = word.toByte()
            word = word shr 8
        }
        return bytes
    }

    /**
     * Return the logical (bit-wise) "and" of two BigIntegers.
     */
    fun and(y: BigInteger?): BigInteger? {
        var y = y
        if (y!!.words == null) {
            return and(this, y.ival)
        } else if (words == null) {
            return and(y, ival)
        }
        var x: BigInteger? = this
        if (ival < y.ival) {
            val temp = this
            x = y
            y = temp
        }
        var i: Int
        val len = if (y.isNegative) x!!.ival else y.ival
        val words = IntArray(len)
        i = 0
        while (i < y.ival) {
            words[i] = x!!.words!![i] and y.words!![i]
            i++
        }
        while (i < len) {
            words[i] = x!!.words!![i]
            i++
        }
        return make(words, len)
    }

    /**
     * Return the logical (bit-wise) "(inclusive) or" of two BigIntegers.
     */
    fun or(y: BigInteger?): BigInteger? {
        return bitOp(7, this, y)
    }

    /**
     * Return the logical (bit-wise) "exclusive or" of two BigIntegers.
     */
    fun xor(y: BigInteger?): BigInteger? {
        return bitOp(6, this, y)
    }

    /**
     * Return the logical (bit-wise) negation of a BigInteger.
     */
    operator fun not(): BigInteger? {
        return bitOp(12, this, ZERO)
    }

    fun andNot(`val`: BigInteger): BigInteger? {
        return and(`val`.not())
    }

    fun clearBit(n: Int): BigInteger? {
        if (n < 0) {
            throw ArithmeticException()
        }
        return and(ONE!!.shiftLeft(n)!!.not())
    }

    fun setBit(n: Int): BigInteger? {
        if (n < 0) {
            throw ArithmeticException()
        }
        return or(ONE!!.shiftLeft(n))
    }

    fun testBit(n: Int): Boolean {
        if (n < 0) {
            throw ArithmeticException()
        }
        return !and(ONE!!.shiftLeft(n))!!.isZero
    }

    fun flipBit(n: Int): BigInteger? {
        if (n < 0) {
            throw ArithmeticException()
        }
        return xor(ONE!!.shiftLeft(n))
    }

    /**
     * Count one bits in a BigInteger.
     * If argument is negative, count zero bits instead.
     */
    fun bitCount(): Int {
        val i: Int
        val x_len: Int
        val x_words = words
        if (x_words == null) {
            x_len = 1
            i = bitCount(ival)
        } else {
            x_len = ival
            i = bitCount(x_words, x_len)
        }
        return if (isNegative) x_len * 32 - i else i
    } //    private void readObject(final ObjectInputStream s)
//            throws IOException, ClassNotFoundException {
//        s.defaultReadObject();
//        if (magnitude.length == 0 || signum == 0) {
//            this.ival = 0;
//            this.words = null;
//        } else {
//            words = byteArrayToIntArray(magnitude, signum < 0 ? -1 : 0);
//            final BigInteger result = make(words, words.length);
//            this.ival = result.ival;
//            this.words = result.words;
//        }
//    }
//
//    private void writeObject(final ObjectOutputStream s)
//            throws IOException, ClassNotFoundException {
//        signum = signum();
//        magnitude = signum == 0 ? new byte[0] : toByteArray();
//        s.defaultWriteObject();
//        magnitude = null; // not needed anymore
//    }
// inner class(es) ..........................................................
}