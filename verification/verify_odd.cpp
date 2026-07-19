// ============================================================================
// verify_odd.cpp
//
// Finite verification, for odd n in [RANGE_START, RANGE_END], that every odd n
// in range admits four square-free summands ell with n - ell prime and with
// pairwise disjoint odd prime supports. Four such witnesses are pairwise
// coprime in their odd parts, so at most three can be divided by the prime
// factors of a modulus k with omega(k) <= 3, leaving at least one summand
// n - ell coprime to k -- i.e. a representation n = p + s with s square-free
// and coprime to k. (For odd n and odd k the common factor 2 is irrelevant,
// so only the odd prime supports need be disjoint.)
//
// Method. Two tiers, both certifying the same object -- square-free summands
// with n - ell prime and pairwise disjoint odd supports:
//
//   Fast path.  ell = 2r for an odd prime r is automatically square-free with
//   singleton odd support {r}. Four distinct such r for which n - 2r is prime
//   are, by construction, four pairwise-disjoint witnesses, so no
//   factorisation is needed. Primality of the n - 2r candidates is answered
//   from a segmented composite/prime bitmap built once per batch of chunks
//   (extended below the batch start by the largest pool witness), so each
//   query is a single array read.
//
//   Fallback.  For any odd n the fast path does not clear, an exhaustive
//   search over primes pr < n forms ell = n - pr, tests square-freeness
//   completely (trial division to B > NMAX^(1/3) followed by a residual
//   perfect-square check), encodes the odd support canonically, and greedily
//   collects four pairwise-disjoint witnesses. This tier uses the
//   deterministic primality routine directly.
//
// Primality backend, selected at compile time:
//
//   default          -- inline deterministic Miller-Rabin with the twelve
//                        Sorenson-Webster bases, valid unconditionally for
//                        every n < 3.317 * 10^24.
//     g++ -O2 -std=c++17 -fopenmp verify_odd.cpp -o verify_odd
//
//   -DUSE_BPSW       -- Baillie-PSW with Montgomery multiplication from
//                        prime64.hpp (faster, conjectural). Needs C++20.
//     g++ -O2 -std=c++20 -fopenmp -DUSE_BPSW verify_odd.cpp -o verify_odd_bpsw
//
//   Sanitized self-test build (run before any exhaustive run):
//     g++ -O0 -g -std=c++17 -fopenmp -fsanitize=address,undefined
//         verify_odd.cpp -o verify_odd_san   (then: ./verify_odd_san --selftest)
// ============================================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <set>
#include <map>
#include <cstdint>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <random>
#include <omp.h>

using namespace std;
using i64 = int64_t;
using u64 = uint64_t;

// ============================================================================
// Configuration
// ============================================================================

const i64 RANGE_START = 4810000001LL;    // Start after previously verified range
const i64 RANGE_END   = 2000000000000LL; // 2 * 10^12
const i64 CHUNK_SIZE  = 1000000LL;       // 10^6

const string RESULTS_FILE    = "lemma64_results.csv";
const string CHECKPOINT_FILE = "lemma64_checkpoint.csv";

const int NUM_THREADS = 6;

// Certified range for the square-free test / witness search.
constexpr i64 NMAX = 2'000'000'000'000LL;                // 2e12, must be >= RANGE_END
constexpr i64 SQFREE_TRIAL_BOUND = 12'700;                // B; B^3 > NMAX required

// Size of the sound fast-path witness pool {2r : r prime, 3 <= r <= POOL_PMAX}.
// Density of hits is ~1/ln(n) per pool element, so a pool of this size gives
// a very large safety margin for finding 4 hits at n up to 2e12 (ln(2e12)~28).
constexpr i64 POOL_PMAX = 2'000'000;

// ============================================================================
// Primality testing
//
// Two interchangeable backends, selected at compile time:
//
//   default          -- inline deterministic Miller-Rabin with the twelve
//                        Sorenson-Webster bases, valid unconditionally for
//                        every n < 3.317 * 10^24, comfortably beyond NMAX.
//                        This is the backend of record for the paper's
//                        reported constants.
//
//   -DUSE_BPSW       -- Baillie-PSW with Montgomery multiplication from
//                        prime64.hpp (faster, but exhaustive only
//                        conjecturally). Requires prime64.hpp on the include
//                        path and a C++20 compiler.
//
// Everything below this block is identical for both backends, so the two
// build variants share a single verification path.
// ============================================================================

#ifdef USE_BPSW

#include "prime64.hpp"
using prime64::is_prime;

#else

u64 mod_pow(u64 base, u64 exp, u64 mod) {
    u64 result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) result = (__uint128_t)result * base % mod;
        exp >>= 1;
        base = (__uint128_t)base * base % mod;
    }
    return result;
}

bool miller_rabin_witness(u64 n, u64 a) {
    if (n % a == 0) return n == a;

    u64 d = n - 1;
    int r = 0;
    while ((d & 1) == 0) { d >>= 1; r++; }

    u64 x = mod_pow(a, d, n);
    if (x == 1 || x == n - 1) return true;

    for (int i = 0; i < r - 1; i++) {
        x = (__uint128_t)x * x % n;
        if (x == n - 1) return true;
    }
    return false;
}

bool is_prime(u64 n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;

    static const u64 witnesses[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 a : witnesses) {
        if (n == a) return true;
        if (!miller_rabin_witness(n, a)) return false;
    }
    return true;
}

#endif  // USE_BPSW

// ============================================================================
// Complete square-free test on [1, NMAX]
//
// Since SQFREE_TRIAL_BOUND^3 > NMAX, trial division by every prime <= B
// followed by a perfect-square check on the residual is a COMPLETE test: any
// surviving non-square-free residual r*s with r repeated and r,s > B would
// force r^2*s > B^3 > NMAX, which is impossible. So the only way a residual
// can hide a repeated factor is if the residual itself is a perfect square.
// ============================================================================

vector<i64> SQFREE_TRIAL_PRIMES;   // all primes <= SQFREE_TRIAL_BOUND

void generate_sqfree_trial_primes() {
    i64 limit = SQFREE_TRIAL_BOUND;
    vector<bool> sieve(limit + 1, true);
    sieve[0] = sieve[1] = false;
    for (i64 i = 2; i * i <= limit; i++)
        if (sieve[i])
            for (i64 j = i * i; j <= limit; j += i) sieve[j] = false;
    for (i64 i = 2; i <= limit; i++)
        if (sieve[i]) SQFREE_TRIAL_PRIMES.push_back(i);
}

i64 isqrt_i64(i64 n) {
    if (n < 2) return n;
    i64 x = (i64)sqrtl((long double)n);
    while (x > 0 && x > n / x) x--;
    while ((x + 1) <= n / (x + 1)) x++;
    return x;
}

bool squarefree_complete(i64 n) {
    // Caller-side invariant: 1 <= n <= NMAX.
    i64 m = n;
    for (i64 p : SQFREE_TRIAL_PRIMES) {
        if (p > m / p) break;   // p*p > m, avoids overflow for large m
        if (m % p == 0) {
            m /= p;
            if (m % p == 0) return false;
        }
    }
    if (m > 1) {
        i64 s = isqrt_i64(m);
        if (s * s == m) return false;
    }
    return true;
}

// ============================================================================
// Canonical odd-support encoding + disjointness
// ============================================================================

struct OddSupport {
    set<i64> small;  // every odd prime divisor <= SQFREE_TRIAL_BOUND
    i64 large = 1;    // remaining cofactor, all of whose prime divisors are > B
};

// Precondition: squarefree_complete(n) is true.
OddSupport odd_support(i64 n) {
    OddSupport res;
    i64 m = n;
    if (m % 2 == 0) m /= 2;

    for (i64 p : SQFREE_TRIAL_PRIMES) {
        if (p == 2) continue;
        if (p > m / p) break;
        if (m % p == 0) {
            res.small.insert(p);
            m /= p;
        }
    }

    if (m == 1) {
        res.large = 1;
    } else if (m <= SQFREE_TRIAL_BOUND) {
        // Canonical invariant: keep every prime <= B in the explicit set.
        res.small.insert(m);
        res.large = 1;
    } else {
        res.large = m;
    }
    return res;
}

i64 gcd_i64(i64 a, i64 b) { while (b) { i64 t = a % b; a = b; b = t; } return a < 0 ? -a : a; }

bool disjoint_supports(const OddSupport& a, const OddSupport& b) {
    for (i64 p : a.small) if (b.small.count(p)) return false;
    return gcd_i64(a.large, b.large) == 1;
}

// ============================================================================
// Fallback: exhaustive four-witness search
// ============================================================================

vector<i64> FALLBACK_PRIMES;   // primes up to 10^7

void generate_fallback_primes() {
    i64 limit = 10'000'000;
    vector<bool> sieve(limit + 1, true);
    sieve[0] = sieve[1] = false;
    for (i64 i = 2; i * i <= limit; i++)
        if (sieve[i])
            for (i64 j = i * i; j <= limit; j += i) sieve[j] = false;
    for (i64 i = 2; i <= limit; i++)
        if (sieve[i]) FALLBACK_PRIMES.push_back(i);
}

bool check4(i64 w) {
    vector<OddSupport> reps;
    reps.reserve(4);

    for (i64 pr : FALLBACK_PRIMES) {
        if (pr >= w) break;
        i64 ell = w - pr;
        if (ell <= 0 || ell > NMAX) continue;
        if (!squarefree_complete(ell)) continue;

        OddSupport sup = odd_support(ell);
        bool ok = true;
        for (const auto& prev : reps) {
            if (!disjoint_supports(sup, prev)) { ok = false; break; }
        }
        if (ok) {
            reps.push_back(sup);
            if (reps.size() == 4) return true;
        }
    }
    return false;
}

// ============================================================================
// Fast path
//
// ell = 2r for odd prime r is automatically square-free with singleton odd
// support {r}. Four distinct r for which w - 2r is prime are therefore, by
// construction, four pairwise-disjoint witnesses -- no factorisation of
// w - 2r is needed at all.
// ============================================================================

vector<i64> WITNESS_POOL;   // {2r : r odd prime <= POOL_PMAX}, ascending

void generate_witness_pool() {
    i64 limit = POOL_PMAX;
    vector<bool> sieve(limit + 1, true);
    sieve[0] = sieve[1] = false;
    for (i64 i = 2; i * i <= limit; i++)
        if (sieve[i])
            for (i64 j = i * i; j <= limit; j += i) sieve[j] = false;
    for (i64 p = 3; p <= limit; p += 2)
        if (sieve[p]) WITNESS_POOL.push_back(2 * p);
    // WITNESS_POOL is ascending by construction (primes generated ascending).
}

bool fast_witnesses(i64 w) {
    // Retained for --selftest / --test convenience where no batch sieve
    // window exists yet. Not used on the hot exhaustive-verification path
    // (see fast_witnesses_sieved below).
    int count = 0;
    for (i64 ell : WITNESS_POOL) {
        if (ell >= w) break;
        if (is_prime((u64)(w - ell))) {
            count++;
            if (count >= 4) return true;
        }
    }
    return false;
}

// ============================================================================
// Sieve-batched fast path
//
// Builds a segmented composite/prime bitmap once per batch of chunks,
// covering [window_start, window_end] where window_start is extended below
// the batch's first value by the largest element of WITNESS_POOL. Every
// witness lookup n - ell for n in the batch and ell in WITNESS_POOL then
// falls inside the bitmap by construction, so it costs one array read
// instead of one Miller-Rabin call.
// ============================================================================

vector<i64> SIEVE_BASE_PRIMES;   // all primes <= sqrt(NMAX) + margin

void generate_sieve_base_primes() {
    i64 limit = (i64)ceill(sqrtl((long double)NMAX)) + 1000;
    vector<bool> sieve(limit + 1, true);
    sieve[0] = sieve[1] = false;
    for (i64 i = 2; i * i <= limit; i++)
        if (sieve[i])
            for (i64 j = i * i; j <= limit; j += i) sieve[j] = false;
    for (i64 i = 2; i <= limit; i++)
        if (sieve[i]) SIEVE_BASE_PRIMES.push_back(i);
}

struct SieveWindow {
    i64 window_start;
    i64 window_end;
    vector<bool> composite;   // composite[i] set  <=>  window_start+i is NOT prime
};

// Builds the composite/prime bitmap for [lo, hi], extended below lo by
// WITNESS_POOL.back() so every witness lookup needed while processing
// n in [lo, hi] lands inside the window.
SieveWindow build_sieve_window(i64 lo, i64 hi) {
    SieveWindow sw;
    i64 max_ell = WITNESS_POOL.empty() ? 0 : WITNESS_POOL.back();
    sw.window_start = max((i64)2, lo - max_ell);
    sw.window_end = hi;
    i64 size = sw.window_end - sw.window_start + 1;
    sw.composite.assign(size, false);

    for (i64 p : SIEVE_BASE_PRIMES) {
        if (p > sw.window_end / p) break;   // p*p > window_end, avoids overflow
        i64 start = max(p * p, ((sw.window_start + p - 1) / p) * p);
        for (i64 j = start; j <= sw.window_end; j += p) sw.composite[j - sw.window_start] = true;
    }
    return sw;
}

inline bool sieve_is_prime(const SieveWindow& sw, i64 x) {
    if (x < 2) return false;
    i64 idx = x - sw.window_start;
    if (idx < 0 || idx >= (i64)sw.composite.size()) return false;  // out of window: never queried by construction, safe default
    return !sw.composite[idx];
}

bool fast_witnesses_sieved(i64 w, const SieveWindow& sw) {
    int count = 0;
    for (i64 ell : WITNESS_POOL) {
        if (ell >= w) break;
        if (sieve_is_prime(sw, w - ell)) {
            count++;
            if (count >= 4) return true;
        }
    }
    return false;
}

// ============================================================================
// Regression tests (run before any exhaustive run)
// ============================================================================

void run_self_tests() {
    cout << "Running regression tests..." << endl;

    // 1. Reject the known false-square-free example.
    {
        i64 bad = 2LL * 1009 * 1009 * 5003;
        bool sf = squarefree_complete(bad);
        cout << "  [1] squarefree_complete(2*1009^2*5003) == false: "
             << (sf == false ? "PASS" : "FAIL") << endl;
        if (sf) { cerr << "REGRESSION FAILURE: test 1\n"; exit(1); }
    }

    // 2. Declare the supports of 65 and 30 non-disjoint.
    {
        bool sf65 = squarefree_complete(65), sf30 = squarefree_complete(30);
        bool disj = (sf65 && sf30) ? disjoint_supports(odd_support(65), odd_support(30)) : true;
        cout << "  [2] disjoint_supports(65,30) == false: "
             << (!disj ? "PASS" : "FAIL") << endl;
        if (disj) { cerr << "REGRESSION FAILURE: test 2\n"; exit(1); }
    }

    // 3. Compare against an independent trial-division factorisation on a
    //    random + adversarial test set.
    {
        mt19937_64 rng(12345);
        bool all_ok = true;

        auto independent_squarefree = [](i64 n) {
            i64 m = n;
            for (i64 p = 2; p * p <= m; p++) {
                int e = 0;
                while (m % p == 0) { m /= p; e++; }
                if (e > 1) return false;
            }
            return true;
        };

        vector<i64> sample;
        for (int i = 0; i < 200000; i++) sample.push_back(1 + (i64)(rng() % 2'000'000));
        // Adversarial: small-prime products and their close neighbours.
        vector<i64> small_primes_adv = {3,5,7,11,13,17,19,23,29,31,37,41,43,47};
        for (i64 p : small_primes_adv)
            for (i64 q : small_primes_adv)
                if (p != q) { sample.push_back(p * q); sample.push_back(p * p * q); }

        for (i64 n : sample) {
            if (n < 1 || n > 2'000'000) continue;
            bool a = squarefree_complete(n);
            bool b = independent_squarefree(n);
            if (a != b) {
                cerr << "  MISMATCH at n=" << n << ": squarefree_complete=" << a
                     << " independent=" << b << endl;
                all_ok = false;
            }
        }
        cout << "  [3] squarefree_complete matches independent factorisation on "
             << sample.size() << " samples: " << (all_ok ? "PASS" : "FAIL") << endl;
        if (!all_ok) { cerr << "REGRESSION FAILURE: test 3\n"; exit(1); }
    }

    // 4. Disjointness correctly rejects a pairing that shares an odd prime.
    {
        // 65 = 5*13 and 30 = 2*3*5 share the prime 5, so their odd supports
        // are not disjoint. A naive pair-of-sets encoding that split 65 as
        // ({}, 65) and 30 as ({3,5}, 1) could miss this; confirm the canonical
        // encoding and disjointness test catch it.
        bool d = disjoint_supports(odd_support(65), odd_support(30));
        cout << "  [4] supports of 65 and 30 correctly non-disjoint: "
             << (!d ? "PASS" : "FAIL") << endl;
        if (d) { cerr << "REGRESSION FAILURE: test 4\n"; exit(1); }
    }

    // 5. Duplicate-counting / pool sanity: WITNESS_POOL strictly ascending,
    //    each element square-free with a singleton support.
    {
        bool ascending = true;
        for (size_t i = 1; i < WITNESS_POOL.size(); i++)
            if (WITNESS_POOL[i] <= WITNESS_POOL[i-1]) { ascending = false; break; }
        bool shapes_ok = true;
        for (int i = 0; i < 20; i++) {
            i64 ell = WITNESS_POOL[i];
            if (!squarefree_complete(ell)) { shapes_ok = false; break; }
            OddSupport s = odd_support(ell);
            if (s.small.size() != 1 || s.large != 1) { shapes_ok = false; break; }
        }
        cout << "  [5] WITNESS_POOL ascending and singleton-support: "
             << ((ascending && shapes_ok) ? "PASS" : "FAIL") << endl;
        if (!ascending || !shapes_ok) { cerr << "REGRESSION FAILURE: test 5\n"; exit(1); }
    }

    // 6. Primality routine spot-check against known primes/composites near
    //    the top of the certified range.
    {
        // Cross-check is_prime against trial division near the top of the
        // verified range.
        auto trial_is_prime = [](i64 n) {
            if (n < 2) return false;
            for (i64 p = 2; p * p <= n; p++) if (n % p == 0) return false;
            return true;
        };
        bool all_match = true;
        for (i64 n = 1'999'999'000'000LL; n < 1'999'999'000'000LL + 2000; n++) {
            if (is_prime((u64)n) != trial_is_prime(n)) { all_match = false; break; }
        }
        cout << "  [6] is_prime matches trial division near 2e12: "
             << (all_match ? "PASS" : "FAIL") << endl;
        if (!all_match) { cerr << "REGRESSION FAILURE: test 6\n"; exit(1); }
    }

    // 7. Sieve-batched fast path agrees with the direct Miller-Rabin fast
    //    path (hand-written sieve marking loop is the newest code here, so
    //    this is the check that actually exercises it against ground truth).
    {
        i64 lo = 4'810'000'001LL, hi = lo + 200'000 - 1;   // 100,000 odd values
        SieveWindow sw = build_sieve_window(lo, hi);
        bool all_match = true;
        i64 mismatches = 0;
        for (i64 w = lo; w <= hi; w += 2) {
            bool a = fast_witnesses(w);
            bool b = fast_witnesses_sieved(w, sw);
            if (a != b) { all_match = false; mismatches++; }
        }
        cout << "  [7] sieve fast path matches direct Miller-Rabin fast path on "
             << ((hi - lo) / 2 + 1) << " values: "
             << (all_match ? "PASS" : ("FAIL (" + to_string(mismatches) + " mismatches)")) << endl;
        if (!all_match) { cerr << "REGRESSION FAILURE: test 7\n"; exit(1); }
    }

    cout << "All regression tests passed." << endl;
}

// ============================================================================
// Chunk processing
// ============================================================================

struct ChunkResult {
    i64 chunk_start;
    i64 chunk_end;
    vector<i64> exceptions;
    i64 checked_count = 0;
    double elapsed_seconds = 0;
};

ChunkResult verify_chunk(i64 from_me, i64 to_me, const SieveWindow& sw) {
    ChunkResult result;
    result.chunk_start = from_me;
    result.chunk_end = to_me;

    auto t_start = chrono::high_resolution_clock::now();

    i64 w = from_me;
    if (w % 2 == 0) w++;

    while (w <= to_me) {
        result.checked_count++;

        if (!fast_witnesses_sieved(w, sw)) {
            if (!check4(w)) {
                result.exceptions.push_back(w);
            }
        }
        w += 2;
    }

    auto t_end = chrono::high_resolution_clock::now();
    result.elapsed_seconds = chrono::duration<double>(t_end - t_start).count();
    return result;
}

// ============================================================================
// Output and checkpoint functions
// ============================================================================

string get_timestamp() {
    auto now = chrono::system_clock::now();
    time_t now_time = chrono::system_clock::to_time_t(now);
    tm* ltm = localtime(&now_time);
    ostringstream oss;
    oss << put_time(ltm, "%Y-%m-%d %H:%M:%S");
    return oss.str();
}

string format_number(i64 n) {
    if (n >= 1000000000) return to_string(n / 1000000000.0).substr(0, 5) + "B";
    if (n >= 1000000) return to_string(n / 1000000.0).substr(0, 5) + "M";
    return to_string(n);
}

void write_result(ofstream& results_file, const ChunkResult& result) {
    string status = result.exceptions.empty() ? "OK" : "EXCEPTIONS";
    results_file << get_timestamp() << "," << result.chunk_start << "," << result.chunk_end
                 << "," << status << ",";
    if (result.exceptions.empty()) {
        results_file << "none";
    } else {
        for (size_t i = 0; i < result.exceptions.size(); i++) {
            if (i > 0) results_file << ";";
            results_file << result.exceptions[i];
        }
    }
    results_file << "," << result.checked_count << ","
                 << fixed << setprecision(2) << result.elapsed_seconds << endl;
    results_file.flush();
}

void write_checkpoint(i64 last_completed_chunk_end) {
    ofstream checkpoint(CHECKPOINT_FILE);
    checkpoint << last_completed_chunk_end << endl;
}

i64 read_checkpoint() {
    ifstream checkpoint(CHECKPOINT_FILE);
    if (!checkpoint.good()) return RANGE_START - 1;
    i64 last_end;
    checkpoint >> last_end;
    return last_end;
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char* argv[]) {
    static_assert(SQFREE_TRIAL_BOUND > 0, "sanity");
    if ((__int128)SQFREE_TRIAL_BOUND * SQFREE_TRIAL_BOUND * SQFREE_TRIAL_BOUND <= NMAX) {
        cerr << "FATAL: SQFREE_TRIAL_BOUND^3 must exceed NMAX for a complete square-free test.\n";
        return 1;
    }
    if (RANGE_END > NMAX) {
        cerr << "FATAL: RANGE_END exceeds the certified range NMAX.\n";
        return 1;
    }

    bool resume_mode = false, test_mode = false, selftest_mode = false;
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--resume") resume_mode = true;
        if (arg == "--test") test_mode = true;
        if (arg == "--selftest") selftest_mode = true;
    }

    cout << "============================================================" << endl;
    cout << "Lemma 6.4 Verification -- odd n" << endl;
    cout << "============================================================" << endl;
    cout << "Range: " << format_number(RANGE_START) << " to " << format_number(RANGE_END) << endl;
    cout << "Chunk size: " << format_number(CHUNK_SIZE) << endl;
    cout << "Threads: " << NUM_THREADS << endl;
    cout << "Square-free trial bound B: " << SQFREE_TRIAL_BOUND << endl;
    cout << "Witness pool size: (generated below)" << endl;
    cout << "============================================================" << endl;

    cout << "Generating square-free trial primes (<= " << SQFREE_TRIAL_BOUND << ")..." << flush;
    generate_sqfree_trial_primes();
    cout << " done (" << SQFREE_TRIAL_PRIMES.size() << " primes)" << endl;

    cout << "Generating fallback primes (<= 1e7)..." << flush;
    generate_fallback_primes();
    cout << " done (" << FALLBACK_PRIMES.size() << " primes)" << endl;

    cout << "Generating witness pool (2r, r <= " << POOL_PMAX << ")..." << flush;
    generate_witness_pool();
    cout << " done (" << WITNESS_POOL.size() << " witnesses)" << endl;

    cout << "Generating sieve base primes (<= sqrt(NMAX))..." << flush;
    generate_sieve_base_primes();
    cout << " done (" << SIEVE_BASE_PRIMES.size() << " primes)" << endl;

    if (selftest_mode) {
        run_self_tests();
        return 0;
    }

    if (test_mode) {
        cout << "\n=== TEST MODE ===" << endl;
        cout << "Testing check4(100001)..." << endl;
        cout << "  Result: " << (check4(100001) ? "True" : "False") << endl;

        cout << "\nRunning single chunk: " << RANGE_START << " to " << (RANGE_START + CHUNK_SIZE - 1) << endl;
        SieveWindow sw = build_sieve_window(RANGE_START, RANGE_START + CHUNK_SIZE - 1);
        auto chunk_result = verify_chunk(RANGE_START, RANGE_START + CHUNK_SIZE - 1, sw);
        cout << "Time: " << chunk_result.elapsed_seconds << "s" << endl;
        cout << "Odd integers checked: " << chunk_result.checked_count << endl;
        cout << "Exceptions: ";
        if (chunk_result.exceptions.empty()) cout << "none" << endl;
        else { for (i64 e : chunk_result.exceptions) cout << e << " "; cout << endl; }

        i64 total_chunks = (RANGE_END - RANGE_START) / CHUNK_SIZE + 1;
        double estimated_hours = (chunk_result.elapsed_seconds * total_chunks) / 3600.0 / NUM_THREADS;
        cout << "\nEstimated total time with " << NUM_THREADS << " threads: "
             << fixed << setprecision(1) << estimated_hours << " hours" << endl;
        return 0;
    }

    i64 start_from = RANGE_START;
    if (resume_mode) {
        i64 checkpoint = read_checkpoint();
        if (checkpoint >= RANGE_START) {
            start_from = checkpoint + 1;
            cout << "Resuming from checkpoint: " << format_number(start_from) << endl;
        }
    }

    i64 total_chunks = (RANGE_END - RANGE_START) / CHUNK_SIZE + 1;
    i64 start_chunk = (start_from - RANGE_START) / CHUNK_SIZE;
    i64 remaining_chunks = total_chunks - start_chunk;

    cout << "Total chunks: " << total_chunks << endl;
    cout << "Remaining: " << remaining_chunks << " chunks" << endl;
    cout << "Starting verification..." << endl;
    cout << "------------------------------------------------------------" << endl;

    ofstream results_file;
    if (resume_mode && start_chunk > 0) {
        results_file.open(RESULTS_FILE, ios::app);
    } else {
        results_file.open(RESULTS_FILE);
        results_file << "timestamp,chunk_start,chunk_end,status,exceptions,checked_count,elapsed_seconds" << endl;
    }

    omp_set_num_threads(NUM_THREADS);
    auto total_start = chrono::high_resolution_clock::now();

    const i64 BATCH_SIZE = NUM_THREADS * 4;
    i64 global_chunks_completed = 0;
    double global_total_time = 0;

    for (i64 batch_start = start_chunk; batch_start < total_chunks; batch_start += BATCH_SIZE) {
        i64 batch_end = min(batch_start + BATCH_SIZE, total_chunks);
        i64 batch_count = batch_end - batch_start;

        // One sieve window covers the whole batch's value range; every
        // thread below reads it but none writes it, so it's safe to share.
        i64 batch_value_start = RANGE_START + batch_start * CHUNK_SIZE;
        i64 batch_value_end = min(RANGE_START + batch_end * CHUNK_SIZE - 1, RANGE_END);
        SieveWindow sw = build_sieve_window(batch_value_start, batch_value_end);

        vector<ChunkResult> batch_results(batch_count);

        #pragma omp parallel for schedule(dynamic)
        for (i64 i = 0; i < batch_count; i++) {
            i64 chunk_idx = batch_start + i;
            i64 chunk_start_v = RANGE_START + chunk_idx * CHUNK_SIZE;
            i64 chunk_end_v = min(chunk_start_v + CHUNK_SIZE - 1, RANGE_END);
            if (chunk_start_v % 2 == 0) chunk_start_v++;
            batch_results[i] = verify_chunk(chunk_start_v, chunk_end_v, sw);
        }

        for (i64 i = 0; i < batch_count; i++) {
            i64 chunk_idx = batch_start + i;
            auto& result = batch_results[i];

            global_chunks_completed++;
            global_total_time += result.elapsed_seconds;
            double avg_time = global_total_time / global_chunks_completed;
            double eta_hours = (avg_time * (total_chunks - chunk_idx - 1)) / 3600.0 / NUM_THREADS;

            cout << "[" << (chunk_idx + 1) << "/" << total_chunks << "] "
                 << format_number(result.chunk_start) << "-" << format_number(result.chunk_end) << ": ";
            if (result.exceptions.empty()) {
                cout << "OK";
            } else {
                cout << "EXCEPTIONS: ";
                for (i64 e : result.exceptions) cout << e << " ";
            }
            cout << " [" << result.checked_count << " checked, "
                 << fixed << setprecision(1) << result.elapsed_seconds << "s]"
                 << " ETA: " << (int)eta_hours << "h " << (int)((eta_hours - (int)eta_hours) * 60) << "m"
                 << endl;

            write_result(results_file, result);
        }
        write_checkpoint(batch_results.back().chunk_end);
    }

    results_file.close();

    auto total_end = chrono::high_resolution_clock::now();
    double total_time = chrono::duration<double>(total_end - total_start).count();

    cout << "------------------------------------------------------------" << endl;
    cout << "Verification complete!" << endl;
    cout << "Total time: " << fixed << setprecision(2) << (total_time / 3600.0) << " hours" << endl;
    return 0;
}
