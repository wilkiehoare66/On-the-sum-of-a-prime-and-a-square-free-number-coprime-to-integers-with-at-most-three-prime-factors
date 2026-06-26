#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <cstdint>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <numeric>
#include <omp.h>
#include "prime64.hpp"

using namespace std;
using i64 = int64_t;
using u64 = uint64_t;

// Configuration
const i64 RANGE_START = 4810000000LL;       // 4.81 * 10^9 (verified up to here)
const i64 RANGE_END = 2000000000000LL;      // 2 * 10^12
const i64 CHUNK_SIZE = 10000000LL;          // 10^7
const i64 SMALL_PRIME_LIMIT = 500;          // Small primes < 500 for quick filter

const string RESULTS_FILE = "lemma63_results.csv";
const string CHECKPOINT_FILE = "lemma63_checkpoint.csv";

const int NUM_THREADS = 6;

// Primality Testing
using prime64::is_prime;
using prime64::next_prime;
using prime64::prev_prime;

// Prime Sieves
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

// Global prime lists
vector<i64> SMALL_PRIMES;           // Primes < 500 for quick filter
vector<i64> SIEVE_PRIMES;           // Primes up to sqrt(RANGE_END) for segmented sieve
vector<i64> FACTOR_PRIMES;          // Primes up to 10^5 for factorization
vector<i64> FALLBACK_PRIMES;        // Primes up to 10^7 for is_good fallback

void generate_primes() {
    // Small primes for quick filter
    auto all_small = sieve_small_primes(SMALL_PRIME_LIMIT);
    SMALL_PRIMES = all_small;
    
    // Sieve primes for segmented sieve
    i64 sieve_limit = (i64)sqrt((double)RANGE_END) + 1000;
    SIEVE_PRIMES = sieve_small_primes(sieve_limit);
    
    // Factor primes for squarefree/coprime checks
    FACTOR_PRIMES = sieve_small_primes(100000);
    
    // Fallback primes for is_good
    FALLBACK_PRIMES = sieve_small_primes(10000000);
}

// Factorization and Square-free/Coprime Checks

// Get prime factorization
map<i64, int> factorint(i64 n) {
    map<i64, int> factors;
    if (n <= 1) return factors;
    
    for (i64 p : FACTOR_PRIMES) {
        if (p * p > n) break;
        while (n % p == 0) {
            factors[p]++;
            n /= p;
        }
    }
    if (n > 1) factors[n]++;
    return factors;
}

// Check if n is square-free
bool is_squarefree(i64 n) {
    for (i64 p : FACTOR_PRIMES) {
        if (p * p > n) break;
        if (n % p == 0) {
            n /= p;
            if (n % p == 0) return false;
        }
    }
    return true;
}

// Check if a and b are coprime (share no prime factors)
bool are_coprime(i64 a, i64 b) {
    return gcd(a, b) == 1;
}

// is_good(n)
// Find 4 representations n = p + sf where:
//   - p is prime
//   - sf is square-free
//   - All sf values are pairwise coprime

// Find next square-free number > y that is coprime to all in coprime_to
i64 next_coprime_squarefree(i64 y, const vector<i64>& coprime_to) {
    i64 candidate = y + 1;
    while (true) {
        if (is_squarefree(candidate)) {
            bool all_coprime = true;
            for (i64 c : coprime_to) {
                if (!are_coprime(candidate, c)) {
                    all_coprime = false;
                    break;
                }
            }
            if (all_coprime) return candidate;
        }
        candidate++;
    }
}

// Returns (is_good, witnesses)
pair<bool, vector<i64>> is_good(i64 n) {
    vector<i64> witnesses;
    i64 sf = 2;  // First non-trivial square-free
    
    while (sf < n) {
        if (is_prime(n - sf)) {
            witnesses.push_back(sf);
        }
        
        if (witnesses.size() < 4) {
            sf = next_coprime_squarefree(sf, witnesses);
        } else {
            return {true, witnesses};
        }
    }
    
    return {false, witnesses};
}

// Chunk Processing
struct VerifiedNumber {
    i64 n;
    vector<i64> witnesses;
};

struct ChunkResult {
    i64 chunk_start;
    i64 chunk_end;
    vector<i64> true_exceptions;                  // Real exceptions (is_good returns false)
    vector<pair<i64, vector<i64>>> false_alarms;  // Flagged by quick filter but pass is_good (n, witnesses)
    i64 quick_exception_count;                    // Total flagged by quick filter
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
    
    // Generate primes in range using segmented sieve
    i64 prime_start = from_me - SMALL_PRIME_LIMIT;
    if (prime_start < 2) prime_start = 2;
    vector<i64> pc_primes = segmented_sieve(prime_start, to_me, SIEVE_PRIMES);
    
    // Also create a set for fast lookup
    unordered_set<i64> pc_prime_set(pc_primes.begin(), pc_primes.end());
    
    // Quick sieve: count Goldbach representations using small primes
    unordered_map<i64, int> num_representations;
    num_representations.reserve(CHUNK_SIZE + 1000);
    
    for (i64 q : pc_primes) {
        for (i64 sp : SMALL_PRIMES) {
            i64 m = sp + q;
            if (m >= from_me && m <= to_me && m % 2 == 0) {
                num_representations[m]++;
            }
        }
    }
    
    // Check even numbers in range
    i64 m = from_me;
    if (m % 2 != 0) m++;
    
    while (m <= to_me) {
        result.checked_count++;
        
        auto it = num_representations.find(m);
        int sieve_reps = (it != num_representations.end()) ? it->second : 0;
        
        if (sieve_reps < 2) {
            result.quick_exception_count++;
            
            // INTERMEDIATE FALLBACK: Check for 2 Goldbach reps with ANY primes
            // (not just small primes) where m = q + (m-q) and m-q is in pc_primes
            int fallback_reps = 0;
            for (i64 q : FALLBACK_PRIMES) {
                if (2 * q >= m) break;
                if (pc_prime_set.count(m - q)) {
                    fallback_reps++;
                    if (fallback_reps >= 2) break;
                }
            }
            
            if (fallback_reps < 2) {
                // Still not enough reps - need to verify with is_good
                auto [good, witnesses] = is_good(m);
                if (!good) {
                    result.true_exceptions.push_back(m);
                } else {
                    // Passed is_good - store with witnesses for proof justification
                    result.false_alarms.push_back({m, witnesses});
                }
            }
        }
        m += 2;
    }
    
    auto t_end = chrono::high_resolution_clock::now();
    result.elapsed_seconds = chrono::duration<double>(t_end - t_start).count();
    
    return result;
}

// Output Functions
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

void init_results_file() {
    ifstream check(RESULTS_FILE);
    if (!check.good()) {
        ofstream f(RESULTS_FILE);
        f << "timestamp,chunk_start,chunk_end,status,true_exceptions,false_alarm_count,quick_filter_count,checked_count,elapsed_seconds" << endl;
        f.close();
    }
}

// Separate file for false alarms with witnesses (for proof justification)
const string FALSE_ALARMS_FILE = "lemma59_false_alarms.csv";

void init_false_alarms_file() {
    ifstream check(FALSE_ALARMS_FILE);
    if (!check.good()) {
        ofstream f(FALSE_ALARMS_FILE);
        f << "n,witnesses" << endl;
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
    
    // True exceptions
    if (r.true_exceptions.empty()) {
        f << "none";
    } else {
        for (size_t i = 0; i < r.true_exceptions.size(); i++) {
            if (i > 0) f << ";";
            f << r.true_exceptions[i];
        }
    }
    f << ","
      << r.false_alarms.size() << ","
      << r.quick_exception_count << ","
      << r.checked_count << ","
      << fixed << setprecision(2) << r.elapsed_seconds << endl;
    f.close();
    
    // Write false alarms with witnesses to separate file
    if (!r.false_alarms.empty()) {
        ofstream fa(FALSE_ALARMS_FILE, ios::app);
        for (auto& [n, witnesses] : r.false_alarms) {
            fa << n << ",\"[";
            for (size_t i = 0; i < witnesses.size(); i++) {
                if (i > 0) fa << ";";
                fa << witnesses[i];
            }
            fa << "]\"" << endl;
        }
        fa.close();
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
    getline(f, line);  // Skip header
    
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

// Main
int main(int argc, char* argv[]) {
    bool resume = false;
    bool test_mode = false;
    
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--resume") resume = true;
        if (arg == "--test") test_mode = true;
    }
    
    int num_threads = NUM_THREADS;
    omp_set_num_threads(num_threads);
    
    cout << "============================================================" << endl;
    cout << "Lemma 6.3 Verification (C++ with OpenMP)" << endl;
    cout << "============================================================" << endl;
    cout << "Range: " << format_number(RANGE_START) << " to " << format_number(RANGE_END) << endl;
    cout << "Chunk size: " << format_number(CHUNK_SIZE) << endl;
    cout << "Threads: " << num_threads << endl;
    cout << "Results file: " << RESULTS_FILE << endl;
    cout << "============================================================" << endl;
    
    // Generate all prime lists
    cout << "Generating primes..." << flush;
    generate_primes();
    cout << " done" << endl;
    cout << "  Small primes (< 500): " << SMALL_PRIMES.size() << endl;
    cout << "  Sieve primes: " << SIEVE_PRIMES.size() << endl;
    cout << "  Factor primes: " << FACTOR_PRIMES.size() << endl;
    cout << "  Fallback primes: " << FALLBACK_PRIMES.size() << endl;
    
    if (test_mode) {
        cout << "\n=== TEST MODE ===" << endl;
        
        // Test is_good on known values
        cout << "Testing is_good(740000138)..." << endl;
        auto [good, witnesses] = is_good(740000138);
        cout << "  Result: " << (good ? "True" : "False") << endl;
        cout << "  Witnesses: ";
        for (i64 w : witnesses) cout << w << " ";
        cout << endl;
        cout << "  Expected: True, [21, 235, 247, 391]" << endl;
        
        // Test is_good on small values that should fail
        cout << "\nTesting is_good(14)..." << endl;
        auto [good2, witnesses2] = is_good(14);
        cout << "  Result: " << (good2 ? "True" : "False") << endl;
        cout << "  Witnesses found: " << witnesses2.size() << endl;
        cout << "  Expected: False (small exception)" << endl;
        
        // Run single chunk
        cout << "\nRunning single chunk: " << RANGE_START << " to " << (RANGE_START + CHUNK_SIZE - 1) << endl;
        auto r = verify_chunk(RANGE_START, RANGE_START + CHUNK_SIZE - 1);
        
        cout << "Time: " << r.elapsed_seconds << "s" << endl;
        cout << "Even integers checked: " << r.checked_count << endl;
        cout << "Quick filter exceptions: " << r.quick_exception_count << endl;
        cout << "False alarms (passed is_good): " << r.false_alarms.size() << endl;
        cout << "True exceptions (failed is_good): " << (r.true_exceptions.empty() ? "none" : to_string(r.true_exceptions.size())) << endl;
        
        if (!r.true_exceptions.empty()) {
            cout << "  True exception values: ";
            for (i64 e : r.true_exceptions) cout << e << " ";
            cout << endl;
        }
        
        if (!r.false_alarms.empty() && r.false_alarms.size() <= 10) {
            cout << "  False alarms with witnesses:" << endl;
            for (auto& [n, w] : r.false_alarms) {
                cout << "    " << n << ": [";
                for (size_t i = 0; i < w.size(); i++) {
                    if (i > 0) cout << ", ";
                    cout << w[i];
                }
                cout << "]" << endl;
            }
        }
        
        i64 total_chunks = (RANGE_END - RANGE_START + CHUNK_SIZE - 1) / CHUNK_SIZE;
        double est_hours = (total_chunks * r.elapsed_seconds) / 3600.0 / num_threads;
        cout << "\nEstimated total time with " << num_threads << " threads: " 
             << fixed << setprecision(1) << est_hours << " hours" << endl;
        
        return 0;
    }
    
    // Build chunk list
    vector<pair<i64, i64>> all_chunks;
    for (i64 cs = RANGE_START; cs < RANGE_END; cs += CHUNK_SIZE) {
        i64 ce = min(cs + CHUNK_SIZE - 1, RANGE_END);
        all_chunks.push_back({cs, ce});
    }
    
    i64 total_chunks = all_chunks.size();
    cout << "Total chunks: " << total_chunks << endl;
    
    // Load completed chunks if resuming
    set<pair<i64,i64>> completed;
    if (resume) {
        completed = load_completed_chunks();
        cout << "Resuming: " << completed.size() << " chunks already completed" << endl;
    }
    
    // Filter to remaining chunks
    vector<pair<i64, i64>> chunks;
    for (auto& c : all_chunks) {
        if (completed.find(c) == completed.end()) {
            chunks.push_back(c);
        }
    }
    
    i64 remaining_chunks = chunks.size();
    cout << "Remaining: " << remaining_chunks << " chunks" << endl;
    
    if (remaining_chunks == 0) {
        cout << "\nAll chunks already verified!" << endl;
        return 0;
    }
    
    init_results_file();
    init_false_alarms_file();
    
    cout << "\nStarting verification..." << endl;
    cout << "------------------------------------------------------------" << endl;
    
    i64 completed_count = 0;
    double total_time = 0;
    vector<i64> all_true_exceptions;
    i64 total_false_alarms = 0;
    auto global_start = chrono::high_resolution_clock::now();
    
    // Process in batches with OpenMP
    const size_t BATCH_SIZE = num_threads * 4;
    
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
        
        // Write results sequentially
        for (size_t i = 0; i < batch_count; i++) {
            auto& r = batch_results[i];
            
            completed_count++;
            total_time += r.elapsed_seconds;
            total_false_alarms += r.false_alarms.size();
            double avg_time = total_time / completed_count;
            double eta_hours = avg_time * (remaining_chunks - completed_count) / 3600.0 / num_threads;
            
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
            
            cout << " [fa:" << r.false_alarms.size() 
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
    cout << "Total false alarms (with witnesses in " << FALSE_ALARMS_FILE << "): " << total_false_alarms << endl;
    
    if (!all_true_exceptions.empty()) {
        cout << "True exception values: ";
        for (i64 e : all_true_exceptions) cout << e << " ";
        cout << endl;
    }
    
    return 0;
}