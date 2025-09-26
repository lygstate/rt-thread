#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>

/* Function to count leading zeros for an uint32_t */
static int32_t u32_count_leading_zeros(uint32_t n)
{
    if (n == 0)
    {
        return 32;
    }
#ifdef __GNUC__
#if LONG_MAX == UINT16_MAX
    return __builtin_clzl(n);
#else
    return __builtin_clz(n);
#endif
#else
    int32_t count = 0;
    uint32_t mask =
        1ULL << (sizeof(uint32_t) * 8 - 1); // Most significant bit

    while ((n & mask) == 0)
    {
        count++;
        mask >>= 1;
    }
    return count;
#endif
}

/* Function to count leading zeros for an uint64_t */
static int32_t u64_count_leading_zeros(uint64_t n)
{
    if (n == 0)
    {
        return 64;
    }
#ifdef __GNUC__
    return __builtin_clzll(n);
#else
    int32_t count = 0;
    uint64_t mask =
        1ULL << (sizeof(uint64_t) * 8 - 1); // Most significant bit

    while ((n & mask) == 0)
    {
        count++;
        mask >>= 1;
    }
    return count;
#endif
}

/**
 * https://ridiculousfish.com/blog/posts/labor-of-division-episode-v.html
 * Perform a narrowing division: 128 / 64 -> 64, and 64 / 32 -> 32.
 * The dividend's low and high words are given by \p numhi and \p numlo,
 * respectively. The divisor is given by \p den.
 * \return the quotient, and the remainder by reference in \p r, if not null.
 * If the quotient would require more than 64 bits, or if denom is 0, then
 * return the max value for both quotient and remainder.
 *
 * These functions are released into the public domain, where applicable, or the
 * CC0 license.
 */
static uint64_t u128_div_u64_u64(uint64_t numhi, uint64_t numlo, uint64_t den,
                                 uint64_t *r)
{
    /*
     * We work in base 2**32.
     * A uint32 holds a single digit. A uint64 holds two digits.
     * Our numerator is conceptually [num3, num2, num1, num0].
     * Our denominator is [den1, den0].
     */
    const uint64_t b = (1ull << 32);

    /* The high and low digits of our computed quotient. */
    uint32_t q1;
    uint32_t q0;

    /* The normalization shift factor. */
    int32_t shift;

    /*
     * The high and low digits of our denominator (after normalizing).
     * Also the low 2 digits of our numerator (after normalizing).
     */
    uint32_t den1;
    uint32_t den0;
    uint32_t num1;
    uint32_t num0;

    /* A partial remainder. */
    uint64_t rem;

    /* The estimated quotient, and its corresponding remainder (unrelated to true remainder). */
    uint64_t qhat;
    uint64_t rhat;

    /* Variables used to correct the estimated quotient. */
    uint64_t c1;
    uint64_t c2;

    /* Check for overflow and divide by 0. */
    numhi = numhi % den;

    /*
     * Determine the normalization factor. We multiply den by this, so that its leading digit is at
     * least half b. In binary this means just shifting left by the number of leading zeros, so that
     * there's a 1 in the MSB.
     * We also shift numer by the same amount. This cannot overflow because numhi < den.
     * The expression (-shift & 63) is the same as (64 - shift), except it avoids the UB of shifting
     * by 64. The funny bitwise 'and' ensures that numlo does not get shifted into numhi if shift is 0.
     * clang 11 has an x86 codegen bug here: see LLVM bug 50118. The sequence below avoids it.
     */
    shift = u64_count_leading_zeros(den);
    den <<= shift;
    numhi <<= shift;
    numhi |= (numlo >> (-shift & 63)) & (-(int64_t)shift >> 63);
    numlo <<= shift;

    /* Extract the low digits of the numerator and both digits of the denominator. */
    num1 = (uint32_t)(numlo >> 32);
    num0 = (uint32_t)(numlo & 0xFFFFFFFFu);
    den1 = (uint32_t)(den >> 32);
    den0 = (uint32_t)(den & 0xFFFFFFFFu);

    /*
     * We wish to compute q1 = [n3 n2 n1] / [d1 d0].
     * Estimate q1 as [n3 n2] / [d1], and then correct it.
     * Note while qhat may be 2 digits, q1 is always 1 digit.
     */
    qhat = numhi / den1;
    rhat = numhi % den1;
    c1 = qhat * den0;
    c2 = rhat * b + num1;
    if (c1 > c2)
        qhat -= (c1 - c2 > den) ? 2 : 1;
    q1 = (uint32_t)qhat;

    /* Compute the true (partial) remainder. */
    rem = numhi * b + num1 - q1 * den;

    /*
     * We wish to compute q0 = [rem1 rem0 n0] / [d1 d0].
     * Estimate q0 as [rem1 rem0] / [d1] and correct it.
     */
    qhat = rem / den1;
    rhat = rem % den1;
    c1 = qhat * den0;
    c2 = rhat * b + num0;
    if (c1 > c2)
        qhat -= (c1 - c2 > den) ? 2 : 1;
    q0 = (uint32_t)qhat;

    /* Return remainder if requested. */
    if (r != NULL)
        *r = (rem * b + num0 - q0 * den) >> shift;
    return ((uint64_t)q1 << 32) | q0;
}

uint64_t rt_muldiv_u64(uint64_t a, uint64_t b, uint64_t c, uint64_t *r)
{
    uint64_t remainder = 0;
    uint64_t ret = 0;
    if (c != 0) /* Handle division by zero. */
    {
        uint64_t a_lo = a & 0xFFFFFFFF;
        uint64_t a_hi = a >> 32;
        uint64_t b_lo = b & 0xFFFFFFFF;
        uint64_t b_hi = b >> 32;

        /* Perform partial products */
        uint64_t p0 = a_lo * b_lo;
        uint64_t p1 = a_lo * b_hi;
        uint64_t p2 = a_hi * b_lo;
        uint64_t p3 = a_hi * b_hi;

        uint64_t carry = (p0 >> 32) + (p1 & 0xFFFFFFFFULL) + (p2 & 0xFFFFFFFFULL);

        uint64_t lo = (p0 & 0xFFFFFFFFULL) + ((carry & 0xFFFFFFFFULL) << 32);
        uint64_t hi = p3 + (p1 >> 32) + (p2 >> 32) + (carry >> 32);
        ret = u128_div_u64_u64(hi, lo, c, &remainder);
    }
    if (r)
        *r = remainder;
    return ret;
}

/* Long division, unsigned (64/32 ==> 32).
   This procedure performs unsigned "long division" i.e., division of a
64-bit unsigned dividend by a 32-bit unsigned divisor, producing a
32-bit quotient.  In the overflow cases (divide by 0, or quotient
exceeds 32 bits), it returns a remainder of 0xFFFFFFFF (an impossible
value).
   The dividend is u1 and u0, with u1 being the most significant word.
The divisor is parameter v. The value returned is the quotient.
   [...] Several of the variables below could be
"short," but having them fullwords gives better code on gcc/Intel.
[...]
This is the version that's in the hacker book. */

uint32_t u64_div_u32_u32(uint32_t u1, uint32_t u0, uint32_t v,
                         uint32_t *r)
{
    const uint32_t b = 65536; // Number base (16 bits).
    uint32_t un1, un0,        // Norm. dividend LSD's.
        vn1, vn0,        // Norm. divisor digits.
        q1, q0,          // Quotient digits.
        un32, un21, un10,// Dividend digit pairs.
        rhat;            // A remainder.
    int32_t s;                    // Shift amount for norm.

    u1 = u1 % v; // If overflow, set rem.

    s = u32_count_leading_zeros(v);               // 0 <= s <= 31.
    v = v << s;               // Normalize divisor.
    vn1 = v >> 16;            // Break divisor up into
    vn0 = v & 0xFFFF;         // two 16-bit digits.
#ifdef HACKERS_DELIGHT
    un32 = (u1 << s) | (u0 >> 32 - s) & (-s >> 31);
#else
    un32 = (u1 << s) | (u0 >> (31 & -s)) & (-s >> 31);
#endif
    un10 = u0 << s;           // Shift dividend left.

    un1 = un10 >> 16;         // Break right half of
    un0 = un10 & 0xFFFF;      // dividend into two digits.

    q1 = un32 / vn1;            // Compute the first
#ifdef HACKERS_DELIGHT
    rhat = un32 - q1 * vn1;     // quotient digit, q1.
#else
    rhat = un32 % vn1;          // quotient digit, q1.
#endif
again1:
    if (q1 >= b || q1 * vn0 > b * rhat + un1)
    {
        q1 = q1 - 1;
        rhat = rhat + vn1;
        if (rhat < b)
            goto again1;
    }

    un21 = un32 * b + un1 - q1 * v;  // Multiply and subtract.

    q0 = un21 / vn1;            // Compute the second
#ifdef HACKERS_DELIGHT
    rhat = un21 - q0 * vn1;     // quotient digit, q0.
#else
    rhat = un21 % vn1;          // quotient digit, q0.
#endif
again2:
    if (q0 >= b || q0 * vn0 > b * rhat + un0)
    {
        q0 = q0 - 1;
        rhat = rhat + vn1;
        if (rhat < b)
            goto again2;
    }

    if (r != NULL)            // If remainder is wanted,
        *r = (un21 * b + un0 - q0 * v) >> s;     // return it.
    return q1 * b + q0;
}

// https://skanthak.hier-im-netz.de/division.html
// Copyleft C 2011-2025, Stefan Kanthak <‍stefan‍.‍kanthak‍@‍nexgo‍.‍de‍>

// Divide an unsigned 128-bit integer dividend, supplied as a pair of
// unsigned 64-bit integers in u0 and u1, by an unsigned 64-bit integer
// divisor, supplied in v; return the unsigned 64-bit quotient and
// optionally the unsigned 64-bit remainder in *r.

uint64_t u128_div_u64_u32(uint64_t u1, uint64_t u0,
                          uint64_t v, uint64_t *r)
{
    uint64_t const b = 4294967296; // Number base (2**32).
    uint64_t un21;                 // Dividend digit pair.
    uint32_t un3, un2, un1, un0,             // Norm. dividend digits.
        vn1, vn0,                       // Norm. divisor digits.
        q1, q0,                         // Quotient digits.
        rhat,                           // A remainder.
        tmp;
    int32_t s;                              // Shift amount for norm.

    u1 = u1 % v; // If overflow, set rem.

    s = u64_count_leading_zeros(v);          // 0 <= s <= 63.
    v <<= s;                                 // Normalize divisor.
    vn1 = v >> 32;                           // Break divisor up into
    vn0 = v & ~0U;                           // two 32-bit digits.

    u1 <<= s;                                // Shift dividend left.
    u1 |= (u0 >> (0U - s & 63U)) & (0LL - s >> 63);
    u0 <<= s;
    un3 = u1 >> 32;                          // Break both halves of
    un2 = u1 & ~0U;                          // dividend into digits.
    un1 = u0 >> 32;
    un0 = u0 & ~0U;
                                            // Compute the first
                                            // quotient digit, q1, via
    tmp = un3 >= vn1;                        // narrowing division.
    q1 = u64_div_u32_u32(un3 - vn1 * tmp, un2, vn1, &rhat);

    while (tmp != 0U || (b * tmp + q1) * vn0 > b * rhat + un1)
    {
        tmp -= q1 == 0U;
        q1 -= 1U;
        rhat += vn1;
        if (rhat < vn1)
            break;
    }
    un21 = un2 * b + un1 - q1 * v;           // Multiply and subtract.
    un2 = un21 >> 32;                        // Break remainder up into
    un1 = un21 & ~0U;                        // two 32-bit digits.
                                            // Compute the second
                                            // quotient digit, q0, via
    tmp = un2 >= vn1;                        // narrowing division.
    q0 = u64_div_u32_u32(un2 - vn1 * tmp, un1, vn1, &rhat);

    while (tmp != 0U || (b * tmp + q0) * vn0 > b * rhat + un0)
    {
        tmp -= q0 == 0U;
        q0 -= 1U;
        rhat += vn1;
        if (rhat < vn1)
            break;
    }
    if (r != NULL)                           // If remainder is wanted,
        *r = (un1 * b + un0 - q0 * v) >> s;   // return it.
    return q1 * b + q0;
}

static uint64_t u128_div_u64_u128(uint64_t numhi, uint64_t numlo, uint64_t den,
                                  uint64_t *r)
{
    unsigned __int128 mul128 = numhi;
    uint64_t ret;
    mul128 <<= 64;
    mul128 |= numlo;
    ret = (uint64_t)(mul128 / den);
    if (r)
    {
        *r = mul128 % den;
    }
    return ret;
}

uint64_t muldiv_u64_by_u128(uint64_t a, uint64_t b, uint64_t c, uint64_t *r)
{
    unsigned __int128 a128;
    unsigned __int128 b128;
    unsigned __int128 mul128;
    if (c == 0)
    {
        return 0;
    }
    a128 = a;
    b128 = b;
    mul128 = a128 * b128;
    if (r)
    {
        *r = mul128 % c;
    }
    return mul128 / c;
}

int main()
{
    uint64_t remainder;
    uint64_t a = 0xFFFFFULL;
    uint64_t b = 0xFFFFFFFFFFFFFFFFULL;
    uint64_t c = 321525;
    unsigned __int128 mul128 = (unsigned __int128)a * b;
    uint64_t hi = (uint64_t)(mul128 >> 64);
    uint64_t lo = (uint64_t)(mul128 & UINT64_MAX);

    printf("a:%llu b:%llu c:%llu hilo:0x%llx%016llx u64_count_leading_zeros(c):%d\n",
           a, b, c, hi, lo, u64_count_leading_zeros(c));

    uint64_t ret = u128_div_u64_u128(hi, lo, c, &remainder);
    printf("u128_div_u64_u128 ret: %llu, remainder:%llu\n", ret, remainder);
    ret = u128_div_u64_u64(hi, lo, c, &remainder);
    printf("u128_div_u64_u64 ret: %llu, remainder:%llu\n", ret, remainder);
    ret = u128_div_u64_u32(hi, lo, c, &remainder);
    printf("u128_div_u64_u32 ret: %llu, remainder:%llu\n", ret, remainder);

    ret = rt_muldiv_u64(a, b, c, &remainder);
    printf("rt_muldiv_u64 ret: %llu, remainder:%llu\n", ret, remainder);
    // 0xfffffffffffffffefffffffe00000001
    return 0;
}
