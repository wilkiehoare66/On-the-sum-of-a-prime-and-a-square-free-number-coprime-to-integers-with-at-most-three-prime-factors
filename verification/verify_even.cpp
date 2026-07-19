// ============================================================================
// verify_even.cpp
//
// Finite verification, for even n in (RANGE_START, RANGE_END], of the even
// branch of the finite computation: every even n in range admits two DISTINCT
// Goldbach splits n = p1 + p2 = p3 + p4. Four distinct primes are pairwise
// coprime, so at most three of them can divide any modulus k with omega(k)<=3,
// leaving at least one split n = p + (n-p) in which the square-free summand
// n - p is coprime to k. (An even n needs an odd prime summand; both split
// primes are odd here since n is even and > 4, so this is automatic.)
//
// The search proceeds in three tiers of increasing cost, all of which count
// the SAME object -- distinct-prime Goldbach splits -- so no square-free test
// is needed anywhere:
//
//   1. Quick sieve: count splits n = sp + q with sp a small prime (< 500) and
//      q obtained from a segmented sieve of the chunk. Two hits clear n.
//   2. Intermediate fallback: for numbers with fewer than two small-prime
//      splits, count splits n = q + (n-q) over all pre-sieved primes q.
//   3. Exhaustive fallback: for the few numbers still unresolved, test
//      n = q + (n-q) directly with the deterministic primality routine until
//      two distinct splits are found. A number reaching this tier and still
//      failing is recorded as a genuine exception.
//
// Primality backend, selected at compile time:
//
//   default          -- inline deterministic Miller-Rabin with the twelve
//                        Sorenson-Webster bases, valid unconditionally for
//                        every n < 3.317 * 10^24.
//     g++ -O2 -std=c++17 -fopenmp verify_even.cpp -o verify_even
//
//   -DUSE_BPSW       -- Baillie-PSW with Montgomery multiplication from
//                        prime64.hpp (faster, conjectural). Needs C++20.
//     g++ -O2 -std=c++20 -fopenmp -DUSE_BPSW verify_even.cpp -o verify_even_bpsw
//
//   Sanitized self-test build (run before any exhaustive run):
//     g++ -O0 -g -std=c++17 -fopenmp -fsanitize=address,undefined
//         verify_even.cpp -o verify_even_san   (then: ./verify_even_san --selftest)
// ============================================================================

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <set>
#include <cstdint>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <omp.h>

using namespace std;
using i64 = int64_t;
using u64 = uint64_t;

// ============================================================================
// Configuration
// ============================================================================

const i64 RANGE_START = 4810000000LL;       // 4.81 * 10^9 (verified up to here)
const i64 RANGE_END   = 2000000000000LL;    // 2 * 10^12
const i64 CHUNK_SIZE  = 10000000LL;         // 10^7
const i64 SMALL_PRIME_LIMIT = 500;          // Small primes < 500 for the quick filter

const string RESULTS_FILE    = "lemma63_results.csv";
const string CHECKPOINT_FILE = "lemma63_checkpoint.csv";

const int NUM_THREADS = 6;

// ============================================================================
// Primality testing
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
// Prime sieves
// ============================================================================

vector<i64> sieve_small_primes(i64 limit) {
    vector<bool> is_prime_arr(limit + 1, true);
    is_prime_arr[0] = is_prime_arr[1] = false;
    for (i64 i = 2; i * i <= limit; i++) {
        if (is_prime_arr[i]) {
            for (i64 j = i * i; j <= limit; j += i) is_prime_arr[j] = false;
        }
    }
    vector<i64> primes;
    for (i64 i = 2; i <= limit; i++)
        if (is_prime_arr[i]) primes.push_back(i);
    return primes;
}

vector<i64> segmented_sieve(i64 from, i64 to, const vector<i64>& small_primes) {
    if (from < 2) from = 2;
    i64 size = to - from + 1;
    vector<bool> is_prime_seg(size, true);

    for (i64 p : small_primes) {
        if (p * p > to) break;
        i64 start = ((from + p - 1) / p) * p;
        if (start == p) start += p;
        for (i64 j = start; j <= to; j += p) is_prime_seg[j - from] = false;
    }

    vector<i64> primes;
    for (i64 i = 0; i < size; i++)
        if (is_prime_seg[i]) primes.push_back(from + i);
    return primes;
}

// ============================================================================
// Global prime lists
// ============================================================================

vector<i64> SMALL_PRIMES;     // primes < 500 for the quick filter
vector<i64> SIEVE_PRIMES;     // primes up to sqrt(RANGE_END) for the segmented sieve
vector<i64> FALLBACK_PRIMES;  // primes up to 10^7 for the intermediate fallback

void generate_primes() {
    SMALL_PRIMES = sieve_small_primes(SMALL_PRIME_LIMIT);

    i64 sieve_limit = (i64)sqrt((double)RANGE_END) + 1000;
    SIEVE_PRIMES = sieve_small_primes(sieve_limit);

    FALLBACK_PRIMES = sieve_small_primes(10000000);
}

// ============================================================================
// Exhaustive two-split check
//
// Returns up to two distinct primes q with n - q also prime (the split
// witnesses q and its partner n-q); a result of size >= 2 certifies n. Used
// only as the final tier, so its per-call cost is irrelevant to overall
// throughput. Uses the deterministic primality routine directly, so it does
// not depend on any pre-sieved prime set.
// ============================================================================

vector<i64> two_distinct_splits(i64 n) {
    vector<i64> found;
    for (i64 q = 2; 2 * q <= n; q++) {
        if (is_prime((u64)q) && is_prime((u64)(n - q))) {
            found.push_back(q);
            if (found.size() == 2) return found;
        }
    }
    return found;
}

// ============================================================================
// Chunk processing
// ============================================================================

struct ChunkResult {
    i64 chunk_start;
    i64 chunk_end;
    vector<i64> true_exceptions;                  // even n with fewer than two distinct splits
    vector<pair<i64, vector<i64>>> deep_checks;   // n resolved only by the exhaustive tier (n, split primes)
    i64 quick_exception_count;                    // count flagged by the quick filter
    i64 checked_count;
    double elapsed_seconds;
};

ChunkResult verify_chunk(i64 from_me, i64 to_me) {
    ChunkResult result;
    result.chunk_start = from_me;
    result.chunk_end = to_me;
    result.checked_count = 0;
    result.quick_exception_count = 0;

    auto t_start = chrono::high_resolution_clock::now();

    // Primes in [from-500, to] via segmented sieve, plus a fast-lookup set.
    i64 prime_start = from_me - SMALL_PRIME_LIMIT;
    if (prime_start < 2) prime_start = 2;
    vector<i64> pc_primes = segmented_sieve(prime_start, to_me, SIEVE_PRIMES);
    unordered_set<i64> pc_prime_set(pc_primes.begin(), pc_primes.end());

    // Tier 1 quick sieve: count splits n = sp + q, sp < 500 prime, q sieved.
    unordered_map<i64, int> num_representations;
    num_representations.reserve(CHUNK_SIZE + 1000);

    for (i64 q : pc_primes) {
        for (i64 sp : SMALL_PRIMES) {
            i64 m = sp + q;
            if (m >= from_me && m <= to_me && m % 2 == 0) num_representations[m]++;
        }
    }

    i64 m = from_me;
    if (m % 2 != 0) m++;

    while (m <= to_me) {
        result.checked_count++;

        auto it = num_representations.find(m);
        int sieve_reps = (it != num_representations.end()) ? it->second : 0;

        if (sieve_reps < 2) {
            result.quick_exception_count++;

            // Tier 2 intermediate fallback: count splits n = q + (n-q) over all
            // pre-sieved primes q (distinct primes, so distinct splits).
            int fallback_reps = 0;
            for (i64 q : FALLBACK_PRIMES) {
                if (2 * q >= m) break;
                if (pc_prime_set.count(m - q)) {
                    fallback_reps++;
                    if (fallback_reps >= 2) break;
                }
            }

            if (fallback_reps < 2) {
                // Tier 3 exhaustive fallback: rigorous two-split search.
                vector<i64> splits = two_distinct_splits(m);
                if (splits.size() < 2) {
                    result.true_exceptions.push_back(m);
                } else {
                    result.deep_checks.push_back({m, splits});
                }
            }
        }
        m += 2;
    }

    auto t_end = chrono::high_resolution_clock::now();
    result.elapsed_seconds = chrono::duration<double>(t_end - t_start).count();
    return result;
}

// ============================================================================
// Output functions
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

void init_results_file() {
    ifstream check(RESULTS_FILE);
    if (!check.good()) {
        ofstream f(RESULTS_FILE);
        f << "timestamp,chunk_start,chunk_end,status,true_exceptions,deep_check_count,quick_filter_count,checked_count,elapsed_seconds" << endl;
        f.close();
    }
}

// Diagnostic log of numbers that needed the exhaustive tier, with the two
// distinct split primes that cleared each (not required for the proof, but
// useful for auditing which inputs stressed the fast tiers).
const string DEEP_CHECKS_FILE = "lemma63_deep_checks.csv";

void init_deep_checks_file() {
    ifstream check(DEEP_CHECKS_FILE);
    if (!check.good()) {
        ofstream f(DEEP_CHECKS_FILE);
        f << "n,split_primes" << endl;
        f.close();
    }
}

void write_result(const ChunkResult& r) {
    ofstream f(RESULTS_FILE, ios::app);
    string status = r.true_exceptions.empty() ? "OK" : "EXCEPTION";

    f << get_timestamp() << ","
      << r.chunk_start << ","
      << r.chunk_end << ","
      << status << ",";

    if (r.true_exceptions.empty()) {
        f << "none";
    } else {
        for (size_t i = 0; i < r.true_exceptions.size(); i++) {
            if (i > 0) f << ";";
            f << r.true_exceptions[i];
        }
    }
    f << ","
      << r.deep_checks.size() << ","
      << r.quick_exception_count << ","
      << r.checked_count << ","
      << fixed << setprecision(2) << r.elapsed_seconds << endl;
    f.close();

    if (!r.deep_checks.empty()) {
        ofstream dc(DEEP_CHECKS_FILE, ios::app);
        for (auto& [n, splits] : r.deep_checks) {
            dc << n << ",\"[";
            for (size_t i = 0; i < splits.size(); i++) {
                if (i > 0) dc << ";";
                dc << splits[i];
            }
            dc << "]\"" << endl;
        }
        dc.close();
    }
}

void write_checkpoint(i64 last_completed) {
    ofstream f(CHECKPOINT_FILE);
    f << last_completed << endl;
    f.close();
}

i64 read_checkpoint() {
    ifstream f(CHECKPOINT_FILE);
    if (!f.good()) return RANGE_START - 1;
    i64 last;
    f >> last;
    return last;
}

set<pair<i64,i64>> load_completed_chunks() {
    set<pair<i64,i64>> completed;
    ifstream f(RESULTS_FILE);
    if (!f.good()) return completed;

    string line;
    getline(f, line);  // skip header

    while (getline(f, line)) {
        stringstream ss(line);
        string timestamp, start_str, end_str;
        getline(ss, timestamp, ',');
        getline(ss, start_str, ',');
        getline(ss, end_str, ',');
        try {
            i64 start = stoll(start_str);
            i64 end = stoll(end_str);
            completed.insert({start, end});
        } catch (...) {}
    }
    return completed;
}

// ============================================================================
// Regression tests
// ============================================================================

void run_self_tests() {
    cout << "Running regression tests..." << endl;

    // 1. Primality routine matches trial division on a low window.
    {
        auto trial = [](i64 n) {
            if (n < 2) return false;
            for (i64 p = 2; p * p <= n; p++) if (n % p == 0) return false;
            return true;
        };
        bool ok = true;
        for (i64 n = 2; n < 200000; n++)
            if (is_prime((u64)n) != trial(n)) { ok = false; break; }
        cout << "  [1] is_prime matches trial division on [2,2e5): "
             << (ok ? "PASS" : "FAIL") << endl;
        if (!ok) { cerr << "REGRESSION FAILURE: test 1\n"; exit(1); }
    }

    // 2. Primality routine matches trial division near the top of the range.
    {
        auto trial = [](i64 n) {
            if (n < 2) return false;
            for (i64 p = 2; p * p <= n; p++) if (n % p == 0) return false;
            return true;
        };
        bool ok = true;
        for (i64 n = 1999999000000LL; n < 1999999000000LL + 2000; n++)
            if (is_prime((u64)n) != trial(n)) { ok = false; break; }
        cout << "  [2] is_prime matches trial division near 2e12: "
             << (ok ? "PASS" : "FAIL") << endl;
        if (!ok) { cerr << "REGRESSION FAILURE: test 2\n"; exit(1); }
    }

    // 3. two_distinct_splits returns two genuine, distinct splits when they
    //    exist, and each reported q gives a prime partner n-q.
    {
        i64 n = 4810000000LL;
        auto s = two_distinct_splits(n);
        bool ok = s.size() == 2 && s[0] != s[1];
        for (i64 q : s) ok = ok && is_prime((u64)q) && is_prime((u64)(n - q));
        cout << "  [3] two_distinct_splits gives two valid distinct splits: "
             << (ok ? "PASS" : "FAIL") << endl;
        if (!ok) { cerr << "REGRESSION FAILURE: test 3\n"; exit(1); }
    }

    // 4. The value the literature flags as sporadic, n = 7,740,000,088, is
    //    cleared by the two-split search (it has many distinct-prime splits;
    //    it only looks hard under a small-prime-only search).
    {
        i64 n = 7740000088LL;
        auto s = two_distinct_splits(n);
        bool ok = s.size() == 2;
        cout << "  [4] n=7740000088 cleared by two-split search: "
             << (ok ? "PASS" : "FAIL") << endl;
        if (!ok) { cerr << "REGRESSION FAILURE: test 4\n"; exit(1); }
    }

    // 5. A full chunk at the low end of the range produces no true exceptions.
    {
        auto r = verify_chunk(RANGE_START, RANGE_START + 2000000 - 1);
        bool ok = r.true_exceptions.empty();
        cout << "  [5] sample chunk has no true exceptions ("
             << r.checked_count << " checked, " << r.quick_exception_count
             << " quick-flagged, " << r.deep_checks.size() << " deep-checked): "
             << (ok ? "PASS" : "FAIL") << endl;
        if (!ok) { cerr << "REGRESSION FAILURE: test 5\n"; exit(1); }
    }

    cout << "All regression tests passed." << endl;
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char* argv[]) {
    if (RANGE_END > 3'300'000'000'000'000'000LL) {
        cerr << "FATAL: RANGE_END exceeds the primality routine's certified range.\n";
        return 1;
    }

    bool resume = false, test_mode = false, selftest_mode = false;
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--resume") resume = true;
        if (arg == "--test") test_mode = true;
        if (arg == "--selftest") selftest_mode = true;
    }

    omp_set_num_threads(NUM_THREADS);

    cout << "============================================================" << endl;
    cout << "Lemma 6.3 Verification -- even n" << endl;
    cout << "============================================================" << endl;
    cout << "Range: " << format_number(RANGE_START) << " to " << format_number(RANGE_END) << endl;
    cout << "Chunk size: " << format_number(CHUNK_SIZE) << endl;
    cout << "Threads: " << NUM_THREADS << endl;
    cout << "Results file: " << RESULTS_FILE << endl;
    cout << "============================================================" << endl;

    cout << "Generating primes..." << flush;
    generate_primes();
    cout << " done" << endl;
    cout << "  Small primes (< 500): " << SMALL_PRIMES.size() << endl;
    cout << "  Sieve primes: " << SIEVE_PRIMES.size() << endl;
    cout << "  Fallback primes: " << FALLBACK_PRIMES.size() << endl;

    if (selftest_mode) {
        run_self_tests();
        return 0;
    }

    if (test_mode) {
        cout << "\n=== TEST MODE ===" << endl;

        cout << "two_distinct_splits(740000138): ";
        auto s1 = two_distinct_splits(740000138);
        for (i64 q : s1) cout << q << "(" << (740000138 - q) << ") ";
        cout << (s1.size() >= 2 ? " -> OK" : " -> INSUFFICIENT") << endl;

        cout << "two_distinct_splits(7740000088): ";
        auto s2 = two_distinct_splits(7740000088LL);
        for (i64 q : s2) cout << q << "(" << (7740000088LL - q) << ") ";
        cout << (s2.size() >= 2 ? " -> OK" : " -> INSUFFICIENT") << endl;

        cout << "\nRunning single chunk: " << RANGE_START << " to " << (RANGE_START + CHUNK_SIZE - 1) << endl;
        auto r = verify_chunk(RANGE_START, RANGE_START + CHUNK_SIZE - 1);

        cout << "Time: " << r.elapsed_seconds << "s" << endl;
        cout << "Even integers checked: " << r.checked_count << endl;
        cout << "Quick filter exceptions: " << r.quick_exception_count << endl;
        cout << "Deep-checked (exhaustive tier): " << r.deep_checks.size() << endl;
        cout << "True exceptions: " << (r.true_exceptions.empty() ? "none" : to_string(r.true_exceptions.size())) << endl;

        if (!r.true_exceptions.empty()) {
            cout << "  True exception values: ";
            for (i64 e : r.true_exceptions) cout << e << " ";
            cout << endl;
        }

        i64 total_chunks = (RANGE_END - RANGE_START + CHUNK_SIZE - 1) / CHUNK_SIZE;
        double est_hours = (total_chunks * r.elapsed_seconds) / 3600.0 / NUM_THREADS;
        cout << "\nEstimated total time with " << NUM_THREADS << " threads: "
             << fixed << setprecision(1) << est_hours << " hours" << endl;

        return 0;
    }

    vector<pair<i64, i64>> all_chunks;
    for (i64 cs = RANGE_START; cs < RANGE_END; cs += CHUNK_SIZE) {
        i64 ce = min(cs + CHUNK_SIZE - 1, RANGE_END);
        all_chunks.push_back({cs, ce});
    }

    i64 total_chunks = all_chunks.size();
    cout << "Total chunks: " << total_chunks << endl;

    set<pair<i64,i64>> completed;
    if (resume) {
        completed = load_completed_chunks();
        cout << "Resuming: " << completed.size() << " chunks already completed" << endl;
    }

    vector<pair<i64, i64>> chunks;
    for (auto& c : all_chunks)
        if (completed.find(c) == completed.end()) chunks.push_back(c);

    i64 remaining_chunks = chunks.size();
    cout << "Remaining: " << remaining_chunks << " chunks" << endl;

    if (remaining_chunks == 0) {
        cout << "\nAll chunks already verified!" << endl;
        return 0;
    }

    init_results_file();
    init_deep_checks_file();

    cout << "\nStarting verification..." << endl;
    cout << "------------------------------------------------------------" << endl;

    i64 completed_count = 0;
    double total_time = 0;
    vector<i64> all_true_exceptions;
    i64 total_deep_checks = 0;
    auto global_start = chrono::high_resolution_clock::now();

    const size_t BATCH_SIZE = NUM_THREADS * 4;

    for (size_t batch_start = 0; batch_start < chunks.size(); batch_start += BATCH_SIZE) {
        size_t batch_end = min(batch_start + BATCH_SIZE, chunks.size());
        size_t batch_count = batch_end - batch_start;

        vector<ChunkResult> batch_results(batch_count);

        #pragma omp parallel for schedule(dynamic)
        for (size_t i = 0; i < batch_count; i++) {
            size_t idx = batch_start + i;
            i64 cs = chunks[idx].first;
            i64 ce = chunks[idx].second;
            batch_results[i] = verify_chunk(cs, ce);
        }

        for (size_t i = 0; i < batch_count; i++) {
            auto& r = batch_results[i];

            completed_count++;
            total_time += r.elapsed_seconds;
            total_deep_checks += r.deep_checks.size();
            double avg_time = total_time / completed_count;
            double eta_hours = avg_time * (remaining_chunks - completed_count) / 3600.0 / NUM_THREADS;

            cout << "[" << completed_count << "/" << remaining_chunks << "] "
                 << format_number(r.chunk_start) << "-" << format_number(r.chunk_end) << ": ";

            if (r.true_exceptions.empty()) {
                cout << "OK";
            } else {
                cout << "EXCEPTIONS(" << r.true_exceptions.size() << "): ";
                for (i64 e : r.true_exceptions) {
                    cout << e << " ";
                    all_true_exceptions.push_back(e);
                }
            }

            cout << " [dc:" << r.deep_checks.size()
                 << ", qf:" << r.quick_exception_count
                 << ", " << fixed << setprecision(1) << r.elapsed_seconds << "s]"
                 << " ETA: " << (int)eta_hours << "h " << (int)((eta_hours - (int)eta_hours) * 60) << "m"
                 << endl;

            write_result(r);
        }

        write_checkpoint(batch_results.back().chunk_end);
    }

    auto global_end = chrono::high_resolution_clock::now();
    double global_time = chrono::duration<double>(global_end - global_start).count();

    cout << "------------------------------------------------------------" << endl;
    cout << "Verification complete!" << endl;
    cout << "Total time: " << fixed << setprecision(2) << (global_time / 3600.0) << " hours" << endl;
    cout << "Total true exceptions: " << all_true_exceptions.size() << endl;
    cout << "Total deep-checked (in " << DEEP_CHECKS_FILE << "): " << total_deep_checks << endl;

    if (!all_true_exceptions.empty()) {
        cout << "True exception values: ";
        for (i64 e : all_true_exceptions) cout << e << " ";
        cout << endl;
    }

    return 0;
}
