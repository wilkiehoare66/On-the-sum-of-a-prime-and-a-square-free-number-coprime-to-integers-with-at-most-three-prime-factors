#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <tuple>
#include <cstdint>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <omp.h>
#include "prime64.hpp"
#include <numeric>

using namespace std;
using i64 = int64_t;
using u64 = uint64_t;

// ============================================================
// Configuration
// ============================================================

const i64 RANGE_START = 4810000001LL;    // Start after previously verified range
const i64 RANGE_END = 2000000000000LL;   // 2 * 10^12
const i64 CHUNK_SIZE = 1000000LL;        // 10^6 (same as original)

const string RESULTS_FILE = "lemma64_results.csv";
const string CHECKPOINT_FILE = "lemma64_checkpoint.csv";

const int NUM_THREADS = 6;

// Primality Testing
using prime64::is_prime;
using prime64::next_prime;
using prime64::prev_prime;

// Small primes for factorization
vector<i64> SMALL_PRIMES_FOR_FACTOR;
const i64 FACTOR_PRIME_LIMIT = 100000;  // Primes up to 10^5 for trial division

void generate_factor_primes() {
    vector<bool> sieve(FACTOR_PRIME_LIMIT + 1, true);
    sieve[0] = sieve[1] = false;
    for (i64 i = 2; i * i <= FACTOR_PRIME_LIMIT; i++) {
        if (sieve[i]) {
            for (i64 j = i * i; j <= FACTOR_PRIME_LIMIT; j += i) {
                sieve[j] = false;
            }
        }
    }
    for (i64 i = 2; i <= FACTOR_PRIME_LIMIT; i++) {
        if (sieve[i]) SMALL_PRIMES_FOR_FACTOR.push_back(i);
    }
}

// Factorization and Square-free checks

// Get prime factorization as map: prime -> exponent
map<i64, int> factorint(i64 n) {
    map<i64, int> factors;
    if (n <= 1) return factors;
    
    for (i64 p : SMALL_PRIMES_FOR_FACTOR) {
        if (p * p > n) break;
        while (n % p == 0) {
            factors[p]++;
            n /= p;
        }
    }
    if (n > 1) {
        factors[n]++;
    }
    return factors;
}

// Square-free ignoring powers of 2 (for precomputation)
bool squarefree_odds(i64 a) {
    auto factors = factorint(a);
    for (auto& [p, e] : factors) {
        if (p > 2 && e > 1) return false;
    }
    return true;
}

// Fully square-free (optimized: early exit, no map allocation)
bool squarefree(i64 n) {
    for (i64 p : SMALL_PRIMES_FOR_FACTOR) {
        if (p * p > n) break;
        if (n % p == 0) {
            n /= p;
            if (n % p == 0) return false;  // p^2 divides original
        }
    }
    return true;  // Remaining factor (if any) appears once
}

// Get odd prime factors (for coprimality checking)
set<i64> get_odd_factors(i64 n) {
    set<i64> factors;
    while (n % 2 == 0) n /= 2;
    for (i64 p : SMALL_PRIMES_FOR_FACTOR) {
        if (p == 2) continue;
        if (p * p > n) break;
        if (n % p == 0) {
            factors.insert(p);
            while (n % p == 0) n /= p;
        }
    }
    if (n > 1) factors.insert(n);
    return factors;
}

// Almost-coprime: gcd has no odd prime factors
// Used in precomputation (less performance critical)
bool coprime_weaker(i64 a, i64 b) {
    auto fa = factorint(a);
    auto fb = factorint(b);
    for (auto& [p, e] : fa) {
        if (p > 2 && fb.count(p)) return false;
    }
    return true;
}

// Optimized Factorization for check() function
// Uses small trial division + perfect square check + GCD for coprimality

// Trial division primes (up to 1000 only - much faster than 100K)
vector<i64> TRIAL_PRIMES;

void generate_trial_primes() {
    for (i64 p : SMALL_PRIMES_FOR_FACTOR) {
        if (p > 2 && p <= 1000) TRIAL_PRIMES.push_back(p);
    }
}

// Fast integer square root
i64 isqrt(i64 n) {
    if (n < 2) return n;
    i64 x = sqrt((double)n);
    while (x * x > n) x--;
    while ((x + 1) * (x + 1) <= n) x++;
    return x;
}

// Result of factorization: small factors + remaining cofactor
struct FactorResult {
    vector<i64> small_factors;  // odd primes found by trial division
    i64 cofactor;               // remaining unfactored part (1, prime, or semiprime)
    bool is_squarefree;
};

// Optimized: small trial division + perfect square check
FactorResult squarefree_get_factors_fast(i64 n) {
    FactorResult res;
    res.cofactor = 1;
    res.is_squarefree = true;
    
    // Handle factor of 2
    if (n % 2 == 0) {
        n /= 2;
        if (n % 2 == 0) { res.is_squarefree = false; return res; }
    }
    
    // Trial division by small odd primes (up to 1000)
    for (i64 p : TRIAL_PRIMES) {
        if (p * p > n) break;
        if (n % p == 0) {
            res.small_factors.push_back(p);
            n /= p;
            if (n % p == 0) { res.is_squarefree = false; return res; }
        }
    }
    
    // Check if remaining n is a perfect square (would mean p^2 for large prime p)
    if (n > 1) {
        i64 s = isqrt(n);
        if (s * s == n) {
            res.is_squarefree = false;
            return res;
        }
        res.cofactor = n;
    }
    
    return res;
}

// Check if two FactorResults are almost-coprime (share no odd prime factor)
bool are_almost_coprime_fast(const FactorResult& a, const FactorResult& b) {
    // Check small factors don't overlap
    for (i64 p : a.small_factors) {
        for (i64 q : b.small_factors) {
            if (p == q) return false;
        }
    }
    
    // Check cofactors share no odd prime (using GCD)
    if (a.cofactor > 1 && b.cofactor > 1) {
        i64 g = gcd(a.cofactor, b.cofactor);
        // Remove any factor of 2 from gcd (we only care about odd primes)
        while (g % 2 == 0) g /= 2;
        if (g > 1) return false;
    }
    
    // Check if a's cofactor is divisible by any of b's small primes
    if (a.cofactor > 1) {
        for (i64 p : b.small_factors) {
            if (a.cofactor % p == 0) return false;
        }
    }
    
    // Check if b's cofactor is divisible by any of a's small primes
    if (b.cofactor > 1) {
        for (i64 p : a.small_factors) {
            if (b.cofactor % p == 0) return false;
        }
    }
    
    return true;
}

// Combined: check squarefree AND get odd factors in one pass
// Returns empty set if not squarefree, otherwise returns odd prime factors
set<i64> squarefree_get_odd_factors(i64 n) {
    set<i64> factors;
    
    // Handle factor of 2
    if (n % 2 == 0) {
        n /= 2;
        if (n % 2 == 0) return {};  // Not squarefree (4 | original)
    }
    
    // Check odd primes
    for (i64 p : SMALL_PRIMES_FOR_FACTOR) {
        if (p == 2) continue;
        if (p * p > n) break;
        if (n % p == 0) {
            factors.insert(p);
            n /= p;
            if (n % p == 0) return {};  // Not squarefree (p^2 | original)
        }
    }
    
    // Remaining factor (if > 1) is a prime that appears once
    if (n > 1) factors.insert(n);
    
    return factors;
}

// Check if two sets of odd factors are disjoint (for check() function)
bool factors_disjoint(const set<i64>& fa, const set<i64>& fb) {
    for (i64 f : fa) {
        if (fb.count(f)) return false;
    }
    return true;
}

// Precomputation: three_progressions
struct Preload {
    i64 p, q, c;  // c = p + q
};

vector<Preload> PRELOADS;

void generate_preloads() {
    set<tuple<i64, i64, i64>> options;
    vector<i64> c_values;  // Track c values for coprimality check
    
    i64 p = 3;
    while (p < 5000) {
        i64 q = next_prime(p);
        while (q < p + 500) {
            i64 c = p + q;
            if (squarefree_odds(c)) {
                // Check coprime_weaker with all existing c values
                bool all_coprime = true;
                for (i64 existing_c : c_values) {
                    if (!coprime_weaker(c, existing_c)) {
                        all_coprime = false;
                        break;
                    }
                }
                if (all_coprime) {
                    options.insert({p, q, c});
                    c_values.push_back(c);
                }
            }
            q = next_prime(q);
        }
        p = next_prime(p);
    }
    
    for (auto& [p, q, c] : options) {
        PRELOADS.push_back({p, q, c});
    }
}

// Segmented Sieve for Prime Generation
vector<i64> sieve_small_primes(i64 limit) {
    vector<bool> is_prime_arr(limit + 1, true);
    is_prime_arr[0] = is_prime_arr[1] = false;
    for (i64 i = 2; i * i <= limit; i++) {
        if (is_prime_arr[i]) {
            for (i64 j = i * i; j <= limit; j += i) {
                is_prime_arr[j] = false;
            }
        }
    }
    vector<i64> primes;
    for (i64 i = 2; i <= limit; i++) {
        if (is_prime_arr[i]) primes.push_back(i);
    }
    return primes;
}

vector<i64> SIEVE_PRIMES;

void generate_sieve_primes() {
    i64 limit = (i64)sqrt((double)RANGE_END) + 1000;
    SIEVE_PRIMES = sieve_small_primes(limit);
}

vector<i64> segmented_sieve(i64 from, i64 to, const vector<i64>& small_primes) {
    if (from < 2) from = 2;
    i64 size = to - from + 1;
    vector<bool> is_prime_seg(size, true);
    
    for (i64 p : small_primes) {
        if (p * p > to) break;
        i64 start = ((from + p - 1) / p) * p;
        if (start == p) start += p;
        for (i64 j = start; j <= to; j += p) {
            is_prime_seg[j - from] = false;
        }
    }
    
    vector<i64> primes;
    for (i64 i = 0; i < size; i++) {
        if (is_prime_seg[i]) primes.push_back(from + i);
    }
    return primes;
}

// Fallback primes for check() function
vector<i64> FALLBACK_PRIMES;

void generate_fallback_primes() {
    FALLBACK_PRIMES = sieve_small_primes(10000000);  // Primes up to 10^7
}

// check(w): Find 3 pairwise almost-coprime square-free representations
// Optimized: small trial division + perfect square check + GCD coprimality
bool check(i64 w) {
    vector<FactorResult> reps;
    
    for (i64 pr : FALLBACK_PRIMES) {
        if (pr >= w) break;
        
        i64 residue = w - pr;
        if (residue <= 0) continue;
        
        auto fr = squarefree_get_factors_fast(residue);
        
        if (fr.is_squarefree) {
            // Check almost-coprime with all existing reps
            bool all_coprime = true;
            for (auto& r : reps) {
                if (!are_almost_coprime_fast(fr, r)) {
                    all_coprime = false;
                    break;
                }
            }
            if (all_coprime) {
                reps.push_back(fr);
                if (reps.size() == 3) return true;
            }
        }
    }
    return false;
}

// Chunk Processing
struct ChunkResult {
    i64 chunk_start;
    i64 chunk_end;
    vector<i64> exceptions;
    i64 checked_count;
    double elapsed_seconds;
};

ChunkResult verify_chunk(i64 from_me, i64 to_me) {
    ChunkResult result;
    result.chunk_start = from_me;
    result.chunk_end = to_me;
    result.checked_count = 0;
    
    auto t_start = chrono::high_resolution_clock::now();
    
    // Build representations using geometric progressions
    unordered_map<i64, int> representations;
    representations.reserve(CHUNK_SIZE + 10000);
    
    // Generate ALL primes in the extended range using segmented sieve
    // Then stride through them (every ~500 gap) instead of calling next_prime repeatedly
    i64 prime_start = from_me - 1000;
    if (prime_start < 2) prime_start = 2;
    i64 prime_end = to_me + 1000;
    
    vector<i64> chunk_primes = segmented_sieve(prime_start, prime_end, SIEVE_PRIMES);
    
    // Iterate through primes with ~500 stride (mimics original next_prime(prime + 500))
    i64 last_used_prime = 0;
    for (i64 prime : chunk_primes) {
        // Skip if we haven't moved at least 500 from last used prime
        if (prime < last_used_prime + 500 && last_used_prime > 0) continue;
        last_used_prime = prime;
        
        if (prime >= to_me) break;
        
        for (const auto& pl : PRELOADS) {
            i64 c_times_2e = pl.c;  // c * 2^0
            i64 m = prime + c_times_2e;
            
            while (m <= to_me + CHUNK_SIZE) {
                if (m >= from_me && m <= to_me && m % 2 == 1) {
                    representations[m]++;
                }
                c_times_2e *= 2;
                m = prime + c_times_2e;
                if (c_times_2e > 2 * to_me) break;  // Overflow protection
            }
        }
    }
    
    // Check all odd numbers in range
    i64 w = from_me;
    if (w % 2 == 0) w++;
    
    while (w <= to_me) {
        result.checked_count++;
        
        auto it = representations.find(w);
        if (it == representations.end() || it->second < 3) {
            // Fallback: thorough check
            if (!check(w)) {
                result.exceptions.push_back(w);
            }
        }
        w += 2;
    }
    
    auto t_end = chrono::high_resolution_clock::now();
    result.elapsed_seconds = chrono::duration<double>(t_end - t_start).count();
    
    return result;
}

// Output and Checkpoint Functions
string get_timestamp() {
    auto now = chrono::system_clock::now();
    time_t now_time = chrono::system_clock::to_time_t(now);
    tm* ltm = localtime(&now_time);
    
    ostringstream oss;
    oss << put_time(ltm, "%Y-%m-%d %H:%M:%S");
    return oss.str();
}

string format_number(i64 n) {
    if (n >= 1000000000) {
        return to_string(n / 1000000000.0).substr(0, 5) + "B";
    } else if (n >= 1000000) {
        return to_string(n / 1000000.0).substr(0, 5) + "M";
    }
    return to_string(n);
}

void write_result(ofstream& results_file, const ChunkResult& result, int chunk_num, int total_chunks) {
    string status = result.exceptions.empty() ? "OK" : "EXCEPTIONS";
    
    results_file << get_timestamp() << ","
                 << result.chunk_start << ","
                 << result.chunk_end << ","
                 << status << ",";
    
    if (result.exceptions.empty()) {
        results_file << "none";
    } else {
        for (size_t i = 0; i < result.exceptions.size(); i++) {
            if (i > 0) results_file << ";";
            results_file << result.exceptions[i];
        }
    }
    
    results_file << "," << result.checked_count
                 << "," << fixed << setprecision(2) << result.elapsed_seconds
                 << endl;
    results_file.flush();
}

void write_checkpoint(i64 last_completed_chunk_end) {
    ofstream checkpoint(CHECKPOINT_FILE);
    checkpoint << last_completed_chunk_end << endl;
    checkpoint.close();
}

i64 read_checkpoint() {
    ifstream checkpoint(CHECKPOINT_FILE);
    if (!checkpoint.good()) return RANGE_START - 1;
    
    i64 last_end;
    checkpoint >> last_end;
    return last_end;
}

// Main
int main(int argc, char* argv[]) {
    bool resume_mode = false;
    bool test_mode = false;
    
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--resume") resume_mode = true;
        if (arg == "--test") test_mode = true;
    }
    
    cout << "============================================================" << endl;
    cout << "Lemma 6.4 Verification (C++ with OpenMP)" << endl;
    cout << "============================================================" << endl;
    cout << "Range: " << format_number(RANGE_START) << " to " << format_number(RANGE_END) << endl;
    cout << "Chunk size: " << format_number(CHUNK_SIZE) << endl;
    cout << "Threads: " << NUM_THREADS << endl;
    cout << "Results file: " << RESULTS_FILE << endl;
    cout << "============================================================" << endl;
    
    // Generate factorization primes
    cout << "Generating factorization primes..." << flush;
    generate_factor_primes();
    cout << " done (" << SMALL_PRIMES_FOR_FACTOR.size() << " primes)" << endl;
    
    // Generate trial primes for fast check() function
    cout << "Generating trial primes (up to 1000)..." << flush;
    generate_trial_primes();
    cout << " done (" << TRIAL_PRIMES.size() << " primes)" << endl;
    
    // Generate preloads
    cout << "Generating preload tuples..." << flush;
    generate_preloads();
    cout << " done (" << PRELOADS.size() << " tuples)" << endl;
    
    // Generate sieve primes
    cout << "Generating sieve primes..." << flush;
    generate_sieve_primes();
    cout << " done (" << SIEVE_PRIMES.size() << " primes)" << endl;
    
    // Generate fallback primes
    cout << "Generating fallback primes..." << flush;
    generate_fallback_primes();
    cout << " done (" << FALLBACK_PRIMES.size() << " primes)" << endl;
    
    if (test_mode) {
        cout << "\n=== TEST MODE ===" << endl;
        
        // Test check() function with a known value
        cout << "Testing check(100001)..." << endl;
        bool result = check(100001);
        cout << "  Result: " << (result ? "True" : "False") << endl;
        
        // Run single chunk
        cout << "\nRunning single chunk: " << RANGE_START << " to " << (RANGE_START + CHUNK_SIZE - 1) << endl;
        auto chunk_result = verify_chunk(RANGE_START, RANGE_START + CHUNK_SIZE - 1);
        
        cout << "Time: " << chunk_result.elapsed_seconds << "s" << endl;
        cout << "Odd integers checked: " << chunk_result.checked_count << endl;
        cout << "Exceptions: ";
        if (chunk_result.exceptions.empty()) {
            cout << "none" << endl;
        } else {
            for (i64 e : chunk_result.exceptions) cout << e << " ";
            cout << endl;
        }
        
        // Estimate total time
        i64 total_chunks = (RANGE_END - RANGE_START) / CHUNK_SIZE + 1;
        double estimated_hours = (chunk_result.elapsed_seconds * total_chunks) / 3600.0 / NUM_THREADS;
        cout << "\nEstimated total time with " << NUM_THREADS << " threads: " 
             << fixed << setprecision(1) << estimated_hours << " hours" << endl;
        
        return 0;
    }
    
    // Determine starting point
    i64 start_from = RANGE_START;
    if (resume_mode) {
        i64 checkpoint = read_checkpoint();
        if (checkpoint >= RANGE_START) {
            start_from = checkpoint + 1;
            cout << "Resuming from checkpoint: " << format_number(start_from) << endl;
        }
    }
    
    // Calculate chunks
    i64 total_chunks = (RANGE_END - RANGE_START) / CHUNK_SIZE + 1;
    i64 start_chunk = (start_from - RANGE_START) / CHUNK_SIZE;
    i64 remaining_chunks = total_chunks - start_chunk;
    
    cout << "Total chunks: " << total_chunks << endl;
    cout << "Remaining: " << remaining_chunks << " chunks" << endl;
    cout << "Starting verification..." << endl;
    cout << "------------------------------------------------------------" << endl;
    
    // Open results file
    ofstream results_file;
    if (resume_mode && start_chunk > 0) {
        results_file.open(RESULTS_FILE, ios::app);
    } else {
        results_file.open(RESULTS_FILE);
        results_file << "timestamp,chunk_start,chunk_end,status,exceptions,checked_count,elapsed_seconds" << endl;
    }
    
    omp_set_num_threads(NUM_THREADS);
    
    auto total_start = chrono::high_resolution_clock::now();
    
    // Process chunks in parallel batches
    const i64 BATCH_SIZE = NUM_THREADS * 4;  // Process multiple chunks per batch
    
    i64 global_chunks_completed = 0;
    double global_total_time = 0;
    
    for (i64 batch_start = start_chunk; batch_start < total_chunks; batch_start += BATCH_SIZE) {
        i64 batch_end = min(batch_start + BATCH_SIZE, total_chunks);
        i64 batch_count = batch_end - batch_start;
        
        // Results storage for this batch
        vector<ChunkResult> batch_results(batch_count);
        
        // Process batch in parallel
        #pragma omp parallel for schedule(dynamic)
        for (i64 i = 0; i < batch_count; i++) {
            i64 chunk_idx = batch_start + i;
            i64 chunk_start = RANGE_START + chunk_idx * CHUNK_SIZE;
            i64 chunk_end = min(chunk_start + CHUNK_SIZE - 1, RANGE_END);
            
            // Make sure we start with odd number
            if (chunk_start % 2 == 0) chunk_start++;
            
            batch_results[i] = verify_chunk(chunk_start, chunk_end);
        }
        
        // Write results sequentially (in order)
        for (i64 i = 0; i < batch_count; i++) {
            i64 chunk_idx = batch_start + i;
            auto& result = batch_results[i];
            
            global_chunks_completed++;
            global_total_time += result.elapsed_seconds;
            double avg_time = global_total_time / global_chunks_completed;
            double eta_hours = (avg_time * (total_chunks - chunk_idx - 1)) / 3600.0 / NUM_THREADS;
            
            // Print progress
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
            
            write_result(results_file, result, chunk_idx + 1, total_chunks);
        }
        
        // Update checkpoint after each batch
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