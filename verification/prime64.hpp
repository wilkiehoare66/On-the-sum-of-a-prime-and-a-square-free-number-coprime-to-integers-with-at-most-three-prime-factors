#ifndef PRIME64_HPP
#define PRIME64_HPP

#include <array>
#include <bit>
#include <cmath>
#include <cstdlib>
#include <cstdint>
#include <limits>
#include <numeric>

namespace prime64 {

using u64 = std::uint64_t;
using u128 = unsigned __int128;

inline u64 mod_signed(std::int64_t a, u64 n) {
    if (a >= 0) {
        return static_cast<u64>(a) % n;
    }
    u64 r = static_cast<u64>(-a) % n;
    return (r == 0) ? 0 : (n - r);
}

inline u64 isqrt_u64(u64 n) {
    if (n < 2) return n;
    long double approx = std::sqrt(static_cast<long double>(n));
    u64 x = static_cast<u64>(approx);
    while (static_cast<u128>(x) * x > n) --x;
    while (static_cast<u128>(x + 1) * (x + 1) <= n) ++x;
    return x;
}

inline bool is_square(u64 n) {
    u64 r = isqrt_u64(n);
    return static_cast<u128>(r) * r == n;
}

inline int jacobi(std::int64_t a_in, u64 n_in) {
    if (n_in == 0 || (n_in & 1ULL) == 0) return 0;
    if (a_in == 0) return n_in == 1 ? 1 : 0;

    int sign = 1;
    std::int64_t a_signed = a_in;
    u64 n = n_in;

    if (a_signed < 0) {
        a_signed = -a_signed;
        if ((n & 3ULL) == 3ULL) sign = -sign;
    }

    u64 a = static_cast<u64>(a_signed) % n;
    while (a != 0) {
        unsigned tz = std::countr_zero(a);
        a >>= tz;
        if (tz & 1U) {
            u64 n_mod_8 = n & 7ULL;
            if (n_mod_8 == 3ULL || n_mod_8 == 5ULL) sign = -sign;
        }
        if ((a & 3ULL) == 3ULL && (n & 3ULL) == 3ULL) sign = -sign;
        u64 t = a;
        a = n % t;
        n = t;
    }
    return (n == 1) ? sign : 0;
}

class Montgomery {
public:
    explicit Montgomery(u64 mod) : n_(mod), n_inv_(compute_n_inv(mod)), one_(to_mont(1)), minus_one_(to_mont(mod - 1)) {}

    u64 modulus() const { return n_; }
    u64 one() const { return one_; }
    u64 minus_one() const { return minus_one_; }

    u64 to_mont(u64 a) const {
        return static_cast<u64>((static_cast<u128>(a % n_) << 64) % n_);
    }

    u64 from_mont(u64 a) const {
        return reduce(a);
    }

    u64 mul(u64 a, u64 b) const {
        return reduce(static_cast<u128>(a) * b);
    }

    u64 add(u64 a, u64 b) const {
        u64 s = a + b;
        if (s < a || s >= n_) s -= n_;
        return s;
    }

    u64 sub(u64 a, u64 b) const {
        return (a >= b) ? (a - b) : (n_ - (b - a));
    }

    u64 div2(u64 a) const {
        return (a & 1ULL) ? ((a + n_) >> 1) : (a >> 1);
    }

    u64 pow(u64 base, u64 exp) const {
        u64 x = to_mont(base % n_);
        u64 result = one_;
        while (exp > 0) {
            if (exp & 1ULL) result = mul(result, x);
            x = mul(x, x);
            exp >>= 1;
        }
        return result;
    }

private:
    static u64 compute_n_inv(u64 n) {
        u64 inv = 1;
        for (int i = 0; i < 6; ++i) inv *= 2 - n * inv;
        return ~inv + 1;
    }

    u64 reduce(u128 t) const {
        u64 m = static_cast<u64>(t) * n_inv_;
        u64 u = static_cast<u64>((t + static_cast<u128>(m) * n_) >> 64);
        return (u >= n_) ? (u - n_) : u;
    }

    u64 n_;
    u64 n_inv_;
    u64 one_;
    u64 minus_one_;
};

inline bool strong_sprp_base2(u64 n) {
    u64 d = n - 1;
    unsigned s = std::countr_zero(d);
    d >>= s;

    Montgomery mont(n);
    u64 x = mont.one();
    u64 base = mont.to_mont(2 % n);

    u64 e = d;
    while (e > 0) {
        if (e & 1ULL) x = mont.mul(x, base);
        base = mont.mul(base, base);
        e >>= 1;
    }

    if (x == mont.one() || x == mont.minus_one()) return true;
    for (unsigned r = 1; r < s; ++r) {
        x = mont.mul(x, x);
        if (x == mont.minus_one()) return true;
    }
    return false;
}

inline bool strong_lucas_selfridge(u64 n) {
    if (is_square(n)) return false;

    std::int64_t D = 5;
    while (true) {
        int j = jacobi(D, n);
        if (j == -1) break;
        if (j == 0) return n == static_cast<u64>(std::llabs(D));
        D = (D > 0) ? -(D + 2) : -(D - 2);
    }

    std::int64_t P = 1;
    std::int64_t Q = (1 - D) / 4;
    if (D == 5) {
        P = 5;
        Q = 5;
    }

    u128 delta = static_cast<u128>(n) + 1;
    unsigned s = 0;
    while ((delta & 1U) == 0) {
        delta >>= 1;
        ++s;
    }
    u64 d = static_cast<u64>(delta);

    Montgomery mont(n);
    const u64 Pm = mont.to_mont(mod_signed(P, n));
    const u64 Dm = mont.to_mont(mod_signed(D, n));
    const u64 Qm = mont.to_mont(mod_signed(Q, n));

    u64 U = mont.one();
    u64 V = Pm;
    u64 Qk = Qm;

    int msb = 63 - std::countl_zero(d);
    for (int bit = msb - 1; bit >= 0; --bit) {
        u64 U2 = mont.mul(U, V);
        u64 V2 = mont.sub(mont.mul(V, V), mont.add(Qk, Qk));
        u64 Q2 = mont.mul(Qk, Qk);
        U = U2;
        V = V2;
        Qk = Q2;

        if ((d >> bit) & 1ULL) {
            u64 nextU = mont.div2(mont.add(mont.mul(Pm, U), V));
            u64 nextV = mont.div2(mont.add(mont.mul(Dm, U), mont.mul(Pm, V)));
            U = nextU;
            V = nextV;
            Qk = mont.mul(Qk, Qm);
        }
    }

    if (mont.from_mont(U) == 0 || mont.from_mont(V) == 0) return true;

    for (unsigned r = 1; r < s; ++r) {
        V = mont.sub(mont.mul(V, V), mont.add(Qk, Qk));
        Qk = mont.mul(Qk, Qk);
        if (mont.from_mont(V) == 0) return true;
    }
    return false;
}

inline bool is_prime(u64 n) {
    if (n < 2) return false;

    static constexpr std::array<u64, 25> small_primes = {
        2ULL, 3ULL, 5ULL, 7ULL, 11ULL, 13ULL, 17ULL, 19ULL, 23ULL, 29ULL,
        31ULL, 37ULL, 41ULL, 43ULL, 47ULL, 53ULL, 59ULL, 61ULL, 67ULL, 71ULL,
        73ULL, 79ULL, 83ULL, 89ULL, 97ULL
    };

    for (u64 p : small_primes) {
        if (n == p) return true;
        if (n % p == 0) return false;
    }

    if ((n & 1ULL) == 0) return false;
    if (is_square(n)) return false;
    if (!strong_sprp_base2(n)) return false;
    return strong_lucas_selfridge(n);
}

inline u64 next_prime(u64 n) {
    if (n < 2) return 2;
    if (n < 3) return 3;
    n += 1;
    if ((n & 1ULL) == 0) ++n;
    while (!is_prime(n)) n += 2;
    return n;
}

inline u64 prev_prime(u64 n) {
    if (n <= 2) return 0;
    if (n <= 3) return 2;
    n -= 1;
    if ((n & 1ULL) == 0) --n;
    while (n >= 3 && !is_prime(n)) n -= 2;
    return (n >= 2) ? n : 0;
}

} // namespace prime64

#endif
