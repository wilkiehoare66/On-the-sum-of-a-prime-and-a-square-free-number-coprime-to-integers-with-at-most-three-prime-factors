#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <set>
#include <cstdint>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <ctime>
#include <omp.h>
#include "prime64.hpp"

using namespace std;
using i64 = int64_t;
using u64 = uint64_t;

// Configuration
const i64 RANGE_START = 4810000000LL;       // 4.81 * 10^9 (already verified up to here)
const i64 RANGE_END = 2000000000000LL;      // 2 * 10^12
const i64 CHUNK_SIZE = 10000000LL;          // 10^7 (same as original)
const i64 SQFREE_SIEVE_LIMIT = 100000;      // 10^5 (same as original)
const i64 SQFREE_CHECK_LIMIT = 10000;       // 10^4 (same as original)
const i64 PRIME_GAP = 10000;                // 10^4 (same as original)

const string RESULTS_FILE = "lemma61_results.csv";
const string CHECKPOINT_FILE = "lemma61_checkpoint.csv";

const int NUM_THREADS = 6;  // Number of parallel threads to use

// Primality Testing
using prime64::is_prime;
using prime64::next_prime;
using prime64::prev_prime;

// Square-free Check
bool is_squarefree(u64 n) {
    if (n <= 1) return true;
    
    int count = 0;
    while (n % 2 == 0) {
        count++;
        if (count > 1) return false;
        n /= 2;
    }
    
    for (u64 i = 3; i * i <= n; i += 2) {
        count = 0;
        while (n % i == 0) {
            count++;
            if (count > 1) return false;
            n /= i;
        }
    }
    return true;
}

// Global Square-free Lists (generated once)
vector<i64> SQ_FREES_SIEVE;
vector<i64> SQ_FREES_CHECK;

void generate_squarefrees() {
    // For sieving (up to 10^5)
    for (i64 k = 1; k < SQFREE_SIEVE_LIMIT; k++) {
        if (is_squarefree(k)) {
            SQ_FREES_SIEVE.push_back(k);
        }
    }
    
    // For checking (up to 10^4)
    for (i64 k = 1; k < SQFREE_CHECK_LIMIT; k++) {
        if (is_squarefree(k)) {
            SQ_FREES_CHECK.push_back(k);
        }
    }
}

// Core Verification Function (direct translation of verify_ft)
struct ChunkResult {
    i64 chunk_start;
    i64 chunk_end;
    vector<i64> exceptions;
    i64 unmarked_count;
    double elapsed_seconds;
};

ChunkResult verify_chunk(i64 from_me, i64 to_me) {
    ChunkResult result;
    result.chunk_start = from_me;
    result.chunk_end = to_me;
    result.unmarked_count = 0;
    
    auto t_start = chrono::high_resolution_clock::now();
    
    // Phase 1: Mark verified using sampled primes (same as original)
    unordered_set<i64> verified;
    u64 np = prev_prime(from_me);
    
    while ((i64)np < to_me) {
        for (i64 s : SQ_FREES_SIEVE) {
            i64 target = np + s;
            if (target >= from_me && target <= to_me) {
                verified.insert(target);
            }
        }
        np = next_prime(np + PRIME_GAP);
    }
    
    // Phase 2: Check unmarked integers (same as original)
    for (i64 m = from_me; m <= to_me; m++) {
        if (verified.find(m) == verified.end()) {
            result.unmarked_count++;
            bool found = false;
            for (i64 s : SQ_FREES_CHECK) {
                if (s >= m) break;
                if (is_prime(m - s)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                result.exceptions.push_back(m);
            }
        }
    }
    
    auto t_end = chrono::high_resolution_clock::now();
    result.elapsed_seconds = chrono::duration<double>(t_end - t_start).count();
    
    return result;
}

// CSV I/O
string get_timestamp() {
    auto now = chrono::system_clock::now();
    time_t t = chrono::system_clock::to_time_t(now);
    char buf[64];
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", localtime(&t));
    return string(buf);
}

void init_results_file() {
    ifstream check(RESULTS_FILE);
    if (!check.good()) {
        ofstream f(RESULTS_FILE);
        f << "timestamp,chunk_start,chunk_end,status,exceptions,unmarked_count,elapsed_seconds" << endl;
        f.close();
    }
}

void append_result(const ChunkResult& r) {
    ofstream f(RESULTS_FILE, ios::app);
    
    string status = r.exceptions.empty() ? "OK" : "EXCEPTION";
    string exc_str = "";
    for (size_t i = 0; i < r.exceptions.size(); i++) {
        if (i > 0) exc_str += ";";
        exc_str += to_string(r.exceptions[i]);
    }
    if (exc_str.empty()) exc_str = "none";
    
    f << get_timestamp() << ","
      << r.chunk_start << ","
      << r.chunk_end << ","
      << status << ","
      << exc_str << ","
      << r.unmarked_count << ","
      << fixed << setprecision(2) << r.elapsed_seconds
      << endl;
    
    f.close();
}

set<pair<i64,i64>> load_completed_chunks() {
    set<pair<i64,i64>> completed;
    
    ifstream f(RESULTS_FILE);
    if (!f.good()) return completed;
    
    string line;
    getline(f, line); // Skip header
    
    while (getline(f, line)) {
        if (line.empty()) continue;
        
        stringstream ss(line);
        string timestamp, chunk_start_str, chunk_end_str;
        
        getline(ss, timestamp, ',');
        getline(ss, chunk_start_str, ',');
        getline(ss, chunk_end_str, ',');
        
        i64 cs = stoll(chunk_start_str);
        i64 ce = stoll(chunk_end_str);
        completed.insert({cs, ce});
    }
    
    return completed;
}

// Progress Display
string format_time(double seconds) {
    int h = (int)(seconds / 3600);
    int m = (int)(fmod(seconds, 3600) / 60);
    int s = (int)(fmod(seconds, 60));
    
    stringstream ss;
    if (h > 0) {
        ss << h << "h " << m << "m";
    } else if (m > 0) {
        ss << m << "m " << s << "s";
    } else {
        ss << fixed << setprecision(1) << seconds << "s";
    }
    return ss.str();
}

string format_number(i64 n) {
    if (n >= 1e12) return to_string(n / (i64)1e9) + "B";
    if (n >= 1e9) return to_string((double)n / 1e9).substr(0, 5) + "B";
    if (n >= 1e6) return to_string((double)n / 1e6).substr(0, 5) + "M";
    return to_string(n);
}

// Main
int main(int argc, char* argv[]) {
    int num_threads = NUM_THREADS;
    bool resume = false;
    bool test_mode = false;
    
    // Parse arguments
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg == "--resume") {
            resume = true;
        } else if (arg == "--test") {
            test_mode = true;
        } else if (arg == "--help") {
            cout << "Usage: " << argv[0] << " [options]" << endl;
            cout << "  --resume       Resume from checkpoint" << endl;
            cout << "  --test         Run single chunk test" << endl;
            return 0;
        }
    }
    
    omp_set_num_threads(num_threads);
    
    // Header
    cout << "============================================================" << endl;
    cout << "Lemma 6.1 Verification (C++ with OpenMP)" << endl;
    cout << "============================================================" << endl;
    cout << "Range: " << format_number(RANGE_START) << " to " << format_number(RANGE_END) << endl;
    cout << "Chunk size: " << format_number(CHUNK_SIZE) << endl;
    cout << "Threads: " << num_threads << endl;
    cout << "Results file: " << RESULTS_FILE << endl;
    cout << "============================================================" << endl;
    
    // Generate square-frees
    cout << "Generating square-free numbers..." << flush;
    generate_squarefrees();
    cout << " done (" << SQ_FREES_SIEVE.size() << " for sieve, " 
         << SQ_FREES_CHECK.size() << " for check)" << endl;
    
    // Test mode
    if (test_mode) {
        cout << "\n=== TEST MODE ===" << endl;
        cout << "Running single chunk: " << RANGE_START << " to " << (RANGE_START + CHUNK_SIZE - 1) << endl;
        
        ChunkResult r = verify_chunk(RANGE_START, RANGE_START + CHUNK_SIZE - 1);
        
        cout << "Time: " << r.elapsed_seconds << "s" << endl;
        cout << "Unmarked: " << r.unmarked_count << endl;
        cout << "Exceptions: " << (r.exceptions.empty() ? "none" : to_string(r.exceptions.size())) << endl;
        
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
    
    // Initialize results file
    init_results_file();
    
    cout << "\nStarting verification..." << endl;
    cout << "------------------------------------------------------------" << endl;
    
    // Track progress
    i64 completed_count = 0;
    double total_time = 0;
    vector<i64> all_exceptions;
    auto global_start = chrono::high_resolution_clock::now();
    
    // Process chunks in parallel
    #pragma omp parallel
    {
        #pragma omp for schedule(dynamic)
        for (size_t i = 0; i < chunks.size(); i++) {
            i64 cs = chunks[i].first;
            i64 ce = chunks[i].second;
            
            ChunkResult r = verify_chunk(cs, ce);
            
            // Critical section for output and file writing
            #pragma omp critical
            {
                completed_count++;
                total_time += r.elapsed_seconds;
                
                // Append to CSV
                append_result(r);
                
                // Collect exceptions
                for (i64 e : r.exceptions) {
                    all_exceptions.push_back(e);
                }
                
                // Progress output
                double avg_time = total_time / completed_count;
                double eta_seconds = (remaining_chunks - completed_count) * avg_time / num_threads;
                
                cout << "[" << completed_count << "/" << remaining_chunks << "] "
                     << format_number(cs) << "-" << format_number(ce) << ": ";
                
                if (r.exceptions.empty()) {
                    cout << "OK";
                } else {
                    cout << "EXCEPTION(";
                    for (size_t j = 0; j < r.exceptions.size(); j++) {
                        if (j > 0) cout << ",";
                        cout << r.exceptions[j];
                    }
                    cout << ")";
                }
                
                cout << " [" << r.unmarked_count << " checked, " 
                     << fixed << setprecision(1) << r.elapsed_seconds << "s]"
                     << " ETA: " << format_time(eta_seconds) << endl;
            }
        }
    }
    
    auto global_end = chrono::high_resolution_clock::now();
    double wall_time = chrono::duration<double>(global_end - global_start).count();
    
    cout << "------------------------------------------------------------" << endl;
    cout << "\nVerification complete!" << endl;
    cout << "Wall time: " << format_time(wall_time) << endl;
    cout << "Total CPU time: " << format_time(total_time) << endl;
    cout << "Results saved to: " << RESULTS_FILE << endl;
    
    if (all_exceptions.empty()) {
        cout << "\n*** NO EXCEPTIONS FOUND ***" << endl;
        cout << "All integers in [" << format_number(RANGE_START) << ", " 
             << format_number(RANGE_END) << "] can be written as p + s" << endl;
        cout << "where p is prime and s is square-free." << endl;
    } else {
        cout << "\n*** EXCEPTIONS FOUND: " << all_exceptions.size() << " ***" << endl;
        for (i64 e : all_exceptions) {
            cout << "  " << e << endl;
        }
    }
    
    return 0;
}
