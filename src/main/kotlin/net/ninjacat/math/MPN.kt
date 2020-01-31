/* gnu.java.math.MPN
   Copyright (C) 1999, 2000, 2001, 2004  Free Software Foundation, Inc.

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
// Included from Kawa 1.6.62 with permission of the author,
// Per Bothner <per@bothner.com>.
package net.ninjacat.math

/**
 * This contains various low-level routines for unsigned bigints.
 * The interfaces match the mpn interfaces in gmp,
 * so it should be easy to replace them with fast native functions
 * that are trivial wrappers around the mpn_ functions in gmp
 * (at least on platforms that use 32-bit "limbs").
 *
 * Converted to Kotlin to use with different target platforms
 *
 * @author Oleksiy Voronin (me@ovoronin.info)
 * @date January 30, 2020
 * @status Passes Jdk 14 unit tests (most of them at least)
 */
object MPN {
    /**
     * Add x[0:size-1] and y, and write the size least
     * significant words of the result to dest.
     * Return carry, either 0 or 1.
     * All values are unsigned.
     * This is basically the same as gmp's mpn_add_1.
     */
    fun add_1(dest: IntArray, x: IntArray, size: Int, y: Int): Int {
        var carry = y.toLong() and 0xffffffffL
        for (i in 0 until size) {
            carry += x[i].toLong() and 0xffffffffL
            dest[i] = carry.toInt()
            carry = carry shr 32
        }
        return carry.toInt()
    }

    /**
     * Add x[0:len-1] and y[0:len-1] and write the len least
     * significant words of the result to dest[0:len-1].
     * All words are treated as unsigned.
     *
     * @return the carry, either 0 or 1
     * This function is basically the same as gmp's mpn_add_n.
     */
    fun add_n(dest: IntArray, x: IntArray, y: IntArray, len: Int): Int {
        var carry: Long = 0
        for (i in 0 until len) {
            carry += ((x[i].toLong() and 0xffffffffL)
                    + (y[i].toLong() and 0xffffffffL))
            dest[i] = carry.toInt()
            carry = carry ushr 32
        }
        return carry.toInt()
    }

    /**
     * Subtract Y[0:size-1] from X[0:size-1], and write
     * the size least significant words of the result to dest[0:size-1].
     * Return borrow, either 0 or 1.
     * This is basically the same as gmp's mpn_sub_n function.
     */
    fun sub_n(dest: IntArray, X: IntArray, Y: IntArray, size: Int): Int {
        var cy = 0
        for (i in 0 until size) {
            var y = Y[i]
            val x = X[i]
            y += cy /* add previous carry to subtrahend */
            // Invert the high-order bit, because: (unsigned) X > (unsigned) Y
// iff: (int) (X^0x80000000) > (int) (Y^0x80000000).
            cy = if (y xor -0x80000000 < cy xor -0x80000000) 1 else 0
            y = x - y
            cy += if (y xor -0x80000000 > x xor -0x80000000) 1 else 0
            dest[i] = y
        }
        return cy
    }

    /**
     * Multiply x[0:len-1] by y, and write the len least
     * significant words of the product to dest[0:len-1].
     * Return the most significant word of the product.
     * All values are treated as if they were unsigned
     * (i.e. masked with 0xffffffffL).
     * OK if dest==x (not sure if this is guaranteed for mpn_mul_1).
     * This function is basically the same as gmp's mpn_mul_1.
     */
    fun mul_1(dest: IntArray, x: IntArray, len: Int, y: Int): Int {
        val yword = y.toLong() and 0xffffffffL
        var carry: Long = 0
        for (j in 0 until len) {
            carry += (x[j].toLong() and 0xffffffffL) * yword
            dest[j] = carry.toInt()
            carry = carry ushr 32
        }
        return carry.toInt()
    }

    /**
     * Multiply x[0:xlen-1] and y[0:ylen-1], and
     * write the result to dest[0:xlen+ylen-1].
     * The destination has to have space for xlen+ylen words,
     * even if the result might be one limb smaller.
     * This function requires that xlen >= ylen.
     * The destination must be distinct from either input operands.
     * All operands are unsigned.
     * This function is basically the same gmp's mpn_mul.
     */
    fun mul(dest: IntArray, x: IntArray, xlen: Int, y: IntArray, ylen: Int) {
        dest[xlen] = mul_1(dest, x, xlen, y[0])
        for (i in 1 until ylen) {
            val yword = y[i].toLong() and 0xffffffffL
            var carry: Long = 0
            for (j in 0 until xlen) {
                carry += ((x[j].toLong() and 0xffffffffL) * yword
                        + (dest[i + j].toLong() and 0xffffffffL))
                dest[i + j] = carry.toInt()
                carry = carry ushr 32
            }
            dest[i + xlen] = carry.toInt()
        }
    }

    /* Divide (unsigned long) N by (unsigned int) D.
    * Returns (remainder << 32)+(unsigned int)(quotient).
    * Assumes (unsigned int)(N>>32) < (unsigned int)D.
    * Code transcribed from gmp-2.0's mpn_udiv_w_sdiv function.
    */
    fun udiv_qrnnd(N: Long, D: Int): Long {
        var q: Long
        var r: Long
        val a1 = N ushr 32
        val a0 = N and 0xffffffffL
        if (D >= 0) {
            if (a1 < (D - a1 - (a0 ushr 31)) and 0xffffffffL) {
                /* dividend, divisor, and quotient are nonnegative */
                q = N / D
                r = N % D
            } else {
                /* Compute c1*2^32 + c0 = a1*2^32 + a0 - 2^31*d */
                val c = N - (D.toLong() shl 31)
                /* Divide (c1*2^32 + c0) by d */
                q = c / D
                r = c % D
                /* Add 2^31 to quotient */
                q += 1L shl 31
            }
        } else {
            val b1: Long = (D ushr 1).toLong()  /* d/2, between 2^30 and 2^31 - 1 */
            //long c1 = (a1 >> 1); /* A/2 */
            //int c0 = (a1 << 31) + (a0 >> 1);
            var c: Long = N ushr 1
            if (a1 < b1 || (a1 shr 1) < b1) {
                if (a1 < b1) {
                    q = c / b1
                    r = c % b1
                } else  /* c1 < b1, so 2^31 <= (A/2)/b1 < 2^32 */ {
                    c = (c - (b1 shl 32)).inv()
                    q = c / b1 /* (A/2) / (d/2) */
                    r = c % b1
                    q = q.inv() and 0xffffffffL /* (A/2)/b1 */
                    r = b1 - 1 - r /* r < b1 => new r >= 0 */
                }
                r = 2 * r + (a0 and 1)
                if ((D and 1) != 0) {
                    if (r >= q) {
                        r = r - q
                    } else if (q - r <= (D.toLong() and 0xffffffffL)) {
                        r = r - q + D
                        q -= 1
                    } else {
                        r = r - q + D + D
                        q -= 2
                    }
                }
            } else  /* Implies c1 = b1 */ { /* Hence a1 = d - 1 = 2*b1 - 1 */
                if (a0 >= (-D).toLong() and 0xffffffffL) {
                    q = -1
                    r = a0 + D
                } else {
                    q = -2
                    r = a0 + D + D
                }
            }
        }
        return (r shl 32) or (q and 0xFFFFFFFFL)
    }

    /**
     * Divide divident[0:len-1] by (unsigned int)divisor.
     * Write result into quotient[0:len-1.
     * Return the one-word (unsigned) remainder.
     * OK for quotient==dividend.
     */
    fun divmod_1(quotient: IntArray, dividend: IntArray, len: Int, divisor: Int): Int {
        var i = len - 1
        var r = dividend[i].toLong()
        if (r and 0xffffffffL >= divisor.toLong() and 0xffffffffL) {
            r = 0
        } else {
            quotient[i--] = 0
            r = r shl 32
        }
        while (i >= 0) {
            val n0 = dividend[i]
            r = (r and 0xffffffffL.inv()) or (n0.toLong() and 0xffffffffL)
            r = udiv_qrnnd(r, divisor)
            quotient[i] = r.toInt()
            i--
        }
        return (r shr 32).toInt()
    }

    /* Subtract x[0:len-1]*y from dest[offset:offset+len-1].
   * All values are treated as if unsigned.
   * @return the most significant word of
   * the product, minus borrow-out from the subtraction.
   */
    fun submul_1(dest: IntArray, offset: Int, x: IntArray, len: Int, y: Int): Int {
        val yl = y.toLong() and 0xffffffffL
        var carry = 0
        var j = 0
        do {
            val prod = (x[j].toLong() and 0xffffffffL) * yl
            var prod_low = prod.toInt()
            val prod_high = (prod shr 32).toInt()
            prod_low += carry
            // Invert the high-order bit, because: (unsigned) X > (unsigned) Y
            // iff: (int) (X^0x80000000) > (int) (Y^0x80000000).
            carry = ((if (prod_low xor -0x80000000 < carry xor -0x80000000) 1 else 0) + prod_high)
            val xJ = dest[offset + j]
            prod_low = xJ - prod_low
            if (prod_low xor -0x80000000 > xJ xor -0x80000000) {
                carry++
            }
            dest[offset + j] = prod_low
        } while (++j < len)
        return carry
    }

    /**
     * Divide zds[0:nx] by y[0:ny-1].
     * The remainder ends up in zds[0:ny-1].
     * The quotient ends up in zds[ny:nx].
     * Assumes:  nx>ny.
     * (int)y[ny-1] < 0  (i.e. most significant bit set)
     */
    fun divide(zds: IntArray, nx: Int, y: IntArray, ny: Int) {
        // This is basically Knuth's formulation of the classical algorithm,
        // but translated from in scm_divbigbig in Jaffar's SCM implementation.
        // Correspondance with Knuth's notation:
        // Knuth's u[0:m+n] == zds[nx:0].
        // Knuth's v[1:n] == y[ny-1:0]
        // Knuth's n == ny.
        // Knuth's m == nx-ny.
        // Our nx == Knuth's m+n.
        // Could be re-implemented using gmp's mpn_divrem:
        // zds[nx] = mpn_divrem (&zds[ny], 0, zds, nx, y, ny).
        var j = nx
        do { // loop over digits of quotient
            // Knuth's j == our nx-j.
            // Knuth's u[j:j+n] == our zds[j:j-ny].

            // treated as unsigned
            var qhat: Int = if (zds[j] == y[ny - 1]) {
                -1 // 0xffffffff
            } else {
                val w = (zds[j].toLong() shl 32) + (zds[j - 1].toLong() and 0xffffffffL)
                udiv_qrnnd(w, y[ny - 1]).toInt()
            }
            if (qhat != 0) {
                val borrow = submul_1(zds, j - ny, y, ny, qhat)
                val save = zds[j]
                var num = (save.toLong() and 0xffffffffL) - (borrow.toLong() and 0xffffffffL)
                while (num != 0L) {
                    qhat--
                    var carry: Long = 0
                    for (i in 0 until ny) {
                        carry += ((zds[j - ny + i].toLong() and 0xffffffffL)
                                + (y[i].toLong() and 0xffffffffL))
                        zds[j - ny + i] = carry.toInt()
                        carry = carry ushr 32
                    }
                    zds[j] += carry.toInt()
                    num = carry - 1
                }
            }
            zds[j] = qhat
        } while (--j >= ny)
    }

    /**
     * Number of digits in the conversion base that always fits in a word.
     * For example, for base 10 this is 9, since 10**9 is the
     * largest number that fits into a words (assuming 32-bit words).
     * This is the same as gmp's __mp_bases[radix].chars_per_limb.
     *
     * @param radix the base
     * @return number of digits
     */
    fun chars_per_word(radix: Int): Int {
        return if (radix < 10) {
            if (radix < 8) {
                if (radix <= 2) {
                    32
                } else if (radix == 3) {
                    20
                } else if (radix == 4) {
                    16
                } else {
                    18 - radix
                }
            } else {
                10
            }
        } else if (radix < 12) {
            9
        } else if (radix <= 16) {
            8
        } else if (radix <= 23) {
            7
        } else if (radix <= 40) {
            6
        } else if (radix <= 256) {
            4
        } else {
            1
        }
    }

    /**
     * Count the number of leading zero bits in an int.
     */
    fun count_leading_zeros(i: Int): Int {
        var i1 = i
        if (i1 == 0) {
            return 32
        }
        var count = 0
        var k = 16
        while (k > 0) {
            val j = i1 ushr k
            if (j == 0) {
                count += k
            } else {
                i1 = j
            }
            k = k shr 1
        }
        return count
    }

    fun set_str(dest: IntArray, str: ByteArray, str_len: Int, base: Int): Int {
        var size = 0
        if (base and (base - 1) == 0) {
            // The base is a power of 2.  Read the input string from
            // least to most significant character/digit.  */
            var next_bitpos = 0
            var bits_per_indigit = 0

            var i1 = base
            while (1.let { i1 = i1 shr it; i1 } != 0) {
                bits_per_indigit++
            }

            var res_digit = 0
            var i = str_len
            while (--i >= 0) {
                val inp_digit = str[i].toInt()
                res_digit = (res_digit or inp_digit) shl next_bitpos
                next_bitpos += bits_per_indigit
                if (next_bitpos >= 32) {
                    dest[size++] = res_digit
                    next_bitpos -= 32
                    res_digit = inp_digit shr bits_per_indigit - next_bitpos
                }
            }
            if (res_digit != 0) {
                dest[size++] = res_digit
            }
        } else { // General case.  The base is not a power of 2.
            val indigits_per_limb = chars_per_word(base)
            var str_pos = 0
            while (str_pos < str_len) {
                var chunk = str_len - str_pos
                if (chunk > indigits_per_limb) {
                    chunk = indigits_per_limb
                }
                var res_digit = str[str_pos++].toInt()
                var big_base = base
                while (--chunk > 0) {
                    res_digit = res_digit * base + str[str_pos++]
                    big_base *= base
                }
                var cy_limb: Int
                if (size == 0) {
                    cy_limb = res_digit
                } else {
                    cy_limb = mul_1(dest, dest, size, big_base)
                    cy_limb += add_1(dest, dest, size, res_digit)
                }
                if (cy_limb != 0) {
                    dest[size++] = cy_limb
                }
            }
        }
        return size
    }

    /**
     * Compare x[0:size-1] with y[0:size-1], treating them as unsigned integers.
     *
     * @result -1, 0, or 1 depending on if x&lt;y, x==y, or x&gt;y.
     * This is basically the same as gmp's mpn_cmp function.
     */
    fun cmp(x: IntArray, y: IntArray, size: Int): Int {
        var size1 = size
        while (--size1 >= 0) {
            val x_word = x[size1]
            val y_word = y[size1]
            if (x_word != y_word) {
                // Invert the high-order bit, because:
                // (unsigned) X > (unsigned) Y iff
                // (int) (X^0x80000000) > (int) (Y^0x80000000).
                return if (x_word xor -0x80000000 > y_word xor -0x80000000) 1 else -1
            }
        }
        return 0
    }

    /**
     * Compare x[0:xlen-1] with y[0:ylen-1], treating them as unsigned integers.
     *
     * @return -1, 0, or 1 depending on if x&lt;y, x==y, or x&gt;y.
     */
    fun cmp(x: IntArray, xlen: Int, y: IntArray, ylen: Int): Int {
        return if (xlen > ylen) 1 else if (xlen < ylen) -1 else cmp(x, y, xlen)
    }

    /**
     * Shift x[x_start:x_start+len-1] count bits to the "right"
     * (i.e. divide by 2**count).
     * Store the len least significant words of the result at dest.
     * The bits shifted out to the right are returned.
     * OK if dest==x.
     * Assumes: 0 &lt; count &lt; 32
     */
    fun rshift(dest: IntArray, x: IntArray, x_start: Int, len: Int, count: Int): Int {
        val count_2 = 32 - count
        var low_word = x[x_start]
        val retval = low_word shl count_2
        var i = 1
        while (i < len) {
            val high_word = x[x_start + i]
            dest[i - 1] = (low_word ushr count) or (high_word shl count_2)
            low_word = high_word
            i++
        }
        dest[i - 1] = low_word ushr count
        return retval
    }

    /**
     * Shift x[x_start:x_start+len-1] count bits to the "right"
     * (i.e. divide by 2**count).
     * Store the len least significant words of the result at dest.
     * OK if dest==x.
     * Assumes: 0 &lt;= count &lt; 32
     * Same as rshift, but handles count==0 (and has no return value).
     */
    fun rshift0(
        dest: IntArray, x: IntArray, x_start: Int,
        len: Int, count: Int
    ) {
        if (count > 0) {
            rshift(dest, x, x_start, len, count)
        } else {
            for (i in 0 until len) {
                dest[i] = x[i + x_start]
            }
        }
    }

    /**
     * Return the long-truncated value of right shifting.
     *
     * @param x     a two's-complement "bignum"
     * @param len   the number of significant words in x
     * @param count the shift count
     * @return (long)(x[0..len - 1] & gt ; & gt ; count).
     */
    fun rshift_long(x: IntArray, len: Int, count: Int): Long {
        var count1 = count
        var wordno = count1 shr 5
        count1 = count1 and 31
        val sign = if (x[len - 1] < 0) -1 else 0
        var w0 = if (wordno >= len) sign else x[wordno]
        wordno++
        var w1 = if (wordno >= len) sign else x[wordno]
        if (count1 != 0) {
            wordno++
            val w2 = if (wordno >= len) sign else x[wordno]
            w0 = (w0 ushr count1) or (w1 shl 32 - count1)
            w1 = (w1 ushr count1) or (w2 shl 32 - count1)
        }
        return (w1.toLong() shl 32) or (w0.toLong() and 0xffffffffL)
    }

    /* Shift x[0:len-1] left by count bits, and store the len least
   * significant words of the result in dest[d_offset:d_offset+len-1].
   * Return the bits shifted out from the most significant digit.
   * Assumes 0 &lt; count &lt; 32.
   * OK if dest==x.
   */
    fun lshift(dest: IntArray, d_offset: Int, x: IntArray, len: Int, count: Int): Int {
        var dOffset = d_offset
        val count2 = 32 - count
        var i = len - 1
        var highWord = x[i]
        val retVal = highWord ushr count2
        dOffset++
        while (--i >= 0) {
            val lowWord = x[i]
            dest[dOffset + i] = (highWord shl count) or (lowWord ushr count2)
            highWord = lowWord
        }
        dest[dOffset + i] = highWord shl count
        return retVal
    }

    /**
     * Return least i such that word &amp; (1&lt;&lt;i). Assumes word!=0.
     */
    fun findLowestBit(word: Int): Int {
        var word1 = word
        var i = 0
        while (word1 and 0xF == 0) {
            word1 = word1 shr 4
            i += 4
        }
        if (word1 and 3 == 0) {
            word1 = word1 shr 2
            i += 2
        }
        if (word1 and 1 == 0) {
            i += 1
        }
        return i
    }

    /**
     * Return least i such that words &amp; (1&lt;&lt;i). Assumes there is such an i.
     */
    fun findLowestBit(words: IntArray): Int {
        var i = 0
        while (true) {
            if (words[i] != 0) {
                return 32 * i + findLowestBit(words[i])
            }
            i++
        }
    }

    /**
     * Calculate Greatest Common Divisior of x[0:len-1] and y[0:len-1].
     * Assumes both arguments are non-zero.
     * Leaves result in x, and returns len of result.
     * Also destroys y (actually sets it to a copy of the result).
     */
    fun gcd(x: IntArray, y: IntArray, len: Int): Int {
        var len1 = len
        var i: Int
        var word: Int
        // Find sh such that both x and y are divisible by 2**sh.
        i = 0
        while (true) {
            word = x[i] or y[i]
            if (word != 0) { // Must terminate, since x and y are non-zero.
                break
            }
            i++
        }
        val initShiftWords = i
        val initShiftBits = findLowestBit(word)
        // Logically: sh = initShiftWords * 32 + initShiftBits
// Temporarily devide both x and y by 2**sh.
        len1 -= initShiftWords
        rshift0(x, x, initShiftWords, len1, initShiftBits)
        rshift0(y, y, initShiftWords, len1, initShiftBits)
        var odd_arg: IntArray /* One of x or y which is odd. */
        var other_arg: IntArray /* The other one can be even or odd. */
        if (x[0] and 1 != 0) {
            odd_arg = x
            other_arg = y
        } else {
            odd_arg = y
            other_arg = x
        }
        while (true) {
            // Shift other_arg until it is odd; this doesn't
// affect the gcd, since we divide by 2**k, which does not
// divide odd_arg.
            i = 0
            while (other_arg[i] == 0) {
                i++
            }
            if (i > 0) {
                var j: Int
                j = 0
                while (j < len1 - i) {
                    other_arg[j] = other_arg[j + i]
                    j++
                }
                while (j < len1) {
                    other_arg[j] = 0
                    j++
                }
            }
            i = findLowestBit(other_arg[0])
            if (i > 0) {
                rshift(other_arg, other_arg, 0, len1, i)
            }
            // Now both odd_arg and other_arg are odd.
// Subtract the smaller from the larger.
// This does not change the result, since gcd(a-b,b)==gcd(a,b).
            i = cmp(odd_arg, other_arg, len1)
            if (i == 0) {
                break
            }
            if (i > 0) { // odd_arg > other_arg
                sub_n(odd_arg, odd_arg, other_arg, len1)
                // Now odd_arg is even, so swap with other_arg;
                val tmp = odd_arg
                odd_arg = other_arg
                other_arg = tmp
            } else { // other_arg > odd_arg
                sub_n(other_arg, other_arg, odd_arg, len1)
            }
            while (odd_arg[len1 - 1] == 0 && other_arg[len1 - 1] == 0) {
                len1--
            }
        }
        if (initShiftWords + initShiftBits > 0) {
            if (initShiftBits > 0) {
                val sh_out = lshift(x, initShiftWords, x, len1, initShiftBits)
                if (sh_out != 0) {
                    x[len1++ + initShiftWords] = sh_out
                }
            } else {
                i = len1
                while (--i >= 0) {
                    x[i + initShiftWords] = x[i]
                }
            }
            i = initShiftWords
            while (--i >= 0) {
                x[i] = 0
            }
            len1 += initShiftWords
        }
        return len1
    }

    fun intLength(i: Int): Int {
        return 32 - count_leading_zeros(if (i < 0) i.inv() else i)
    }

    /**
     * Calcaulte the Common Lisp "integer-length" function.
     * Assumes input is canonicalized:  len==BigInteger.wordsNeeded(words,len)
     */
    fun intLength(words: IntArray, len: Int): Int {
        var len1 = len
        len1--
        return intLength(words[len1]) + 32 * len1
    }

    /* DEBUGGING:
      public static void dprint (BigInteger x)
      {
        if (x.words == null)
          System.err.print(Long.toString((long) x.ival & 0xffffffffL, 16));
        else
          dprint (System.err, x.words, x.ival);
      }
      public static void dprint (int[] x) { dprint (System.err, x, x.length); }
      public static void dprint (int[] x, int len) { dprint (System.err, x, len); }
      public static void dprint (java.io.PrintStream ps, int[] x, int len)
      {
        ps.print('(');
        for (int i = 0;  i < len; i++)
          {
            if (i > 0)
              ps.print (' ');
            ps.print ("#x" + Long.toString ((long) x[i] & 0xffffffffL, 16));
          }
        ps.print(')');
      }
      */
}