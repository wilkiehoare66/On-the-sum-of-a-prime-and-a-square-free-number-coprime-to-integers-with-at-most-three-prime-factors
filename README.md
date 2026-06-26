# On the sum of a prime and a square-free number coprime to integers with at most three prime factors

Scripts and computational data accompanying the paper of the same name by **Wilkie Hoare**.

> **Paper:** [arXiv:XXXX.XXXXX](https://arxiv.org/abs/XXXX.XXXXX) *(link to be added once posted)*

## Result

For any integer $k>1$ with at most three prime factors, every integer $n\geq 60$ is a sum of a prime and a square-free number coprime to $k$ (every **even** $n\geq 60$ when $k$ is even). This extends the two-prime-factor theorem of Lee and O'Clarey to three prime factors, unconditionally.

The proof has two ingredients, mirrored by the two halves of this repository:

1. an **explicit analytic lower bound** for the weighted representation count $R_k(n)$, positive for all $n$ above an explicit threshold (at most $2.55\cdot10^{11}$); and
2. a **computational verification** that every $60\leq n\leq 2\cdot10^{12}$ is representable.

Together these cover every $n\geq 60$ with overlap.

## Repository layout

```
ComputeRkBound.py        Explicit lower bound for R_k(n)        (Proposition 4.1)
ComputeBqBound.py        Explicit bound for the divisible part   (Proposition 4.4)
bennett_c_theta.tsv  ┐
bennett_x0.tsv       │   Data tables read by the two scripts above
rr_theta_table1.tsv  │   (must stay in the same directory as the scripts)
rr_theta_table2.tsv  ┘

verification/                       Finite check, 4.81e9 < n <= 2e12  (Section 6)
    verify_large_prime.cpp          k a prime q > 10^5
    verify_even.cpp                 even n
    verify_odd.cpp                  odd n   (the heaviest case)
    results/
        large_prime.csv             per-chunk verification logs
        even.csv
        even_false_alarms.csv       sporadic values needing the multi-witness check
        odd.csv                     ~135 MB, stored via Git LFS
    bpsw-montgomery/                faster variant (see "Primality testing")
        verify_large_prime.cpp
        verify_even.cpp
        verify_odd.cpp
        prime64.hpp                 shared Baillie-PSW + Montgomery primality routine
```

## Part 1 — Explicit bounds (Python)

`ComputeRkBound.py` traces the explicit estimate of Proposition 4.1 and prints a rigorous lower bound for $R_k(n)/n$ at $n=8\cdot10^9$ for a given odd square-free modulus. `ComputeBqBound.py` does the same for the Estermann bound on the divisible part $B_q(n)=R(n)-R_q(n)$ (Proposition 4.4) and the splitting criterion $R_{q_1q_2}(n)>\log 2+B_{q_3}(n)$.

Both use only the Python standard library (3.7+) and read the four `.tsv` tables from their own directory.

```bash
python ComputeRkBound.py --k 15      # -> R_15(n)/n >= 0.09527...  (the benchmark of Theorem 4.3)
python ComputeRkBound.py --k 105
python ComputeBqBound.py --k 429
```

Run either with `--help` for the full set of options.

## Part 2 — Computational verification (C++)

The three programs in `verification/` extend the computation of Lee and O'Clarey (which reached $4.81\cdot10^9$) up to $2\cdot10^{12}$, splitting on the shape of $n$:

| Program | Covers | Method |
|---|---|---|
| `verify_large_prime.cpp` | $k$ a prime $q>10^5$ | small-prime sieve + fallback |
| `verify_even.cpp` | even $n$ | two Goldbach splits into distinct primes |
| `verify_odd.cpp` | odd $n$ | $\geq 3$ pairwise-coprime square-free witnesses |

They rely on a segmented sieve of Eratosthenes and OpenMP shared-memory parallelism. The number of threads is the constant `NUM_THREADS` near the top of each file (default 6); set it to your core count.

```bash
g++ -O3 -fopenmp -std=c++17 verify_odd.cpp -o verify_odd
./verify_odd
```

Each run appends per-chunk logs to a CSV in `results/`; the `even_false_alarms.csv` lists the handful of even values that fail the two-split search and are closed by an explicit multi-witness check (e.g. $n=7\,740\,000\,088$).

### Primality testing

The results of record were produced with the **twelve-base Miller–Rabin test of Sorenson–Webster** ([*Math. Comp.* **86** (2017)](https://doi.org/10.1090/mcom/3134)), which is *deterministic* for every $n<3.3\cdot10^{24}$ — far beyond the $2\cdot10^{12}$ tested here. This is the test used by the programs in `verification/`.

`verification/bpsw-montgomery/` contains a faster variant suggested by Andy Booker, which replaces this with a Baillie–PSW test and Montgomery multiplication, abstracting the primality routine into the shared header `prime64.hpp`. It is provided as a speed-oriented alternative (useful for extending the range); it is **not** the results of record. Compile it from inside its own directory so the local `prime64.hpp` is found:

```bash
cd verification/bpsw-montgomery
g++ -O3 -fopenmp -std=c++17 verify_odd.cpp -o verify_odd
```

## How the ranges fit together

| Range of $n$ | Established by |
|---|---|
| $60\leq n\leq 4.81\cdot10^9$ | prior work (Lee–O'Clarey, Hathi–Johnston) |
| $4.81\cdot10^9 < n\leq 2\cdot10^{12}$ | `verification/` (this repository) |
| $n > 2\cdot10^{12}$ | the analytic argument, with constants from `ComputeRkBound.py` / `ComputeBqBound.py` |

## Large files (Git LFS)

`results/odd.csv` (~135 MB) is tracked with [Git LFS](https://git-lfs.com). To obtain the real file rather than a pointer:

```bash
git lfs install
git clone <repo-url>          # or, in an existing clone:  git lfs pull
```

## Data sources

- `bennett_c_theta.tsv`, `bennett_x0.tsv` — explicit constants for $\theta(x;q,a)$ from Bennett, Martin, O'Bryant and Rechnitzer, *Explicit bounds for primes in arithmetic progressions*, [*Illinois J. Math.* **62** (2018)](https://www.nt.math.ubc.ca/BeMaObRe/).
- `rr_theta_table1.tsv`, `rr_theta_table2.tsv` — tables from Ramaré and Rumely, *Primes in arithmetic progressions*, *Math. Comp.* **65** (1996), transcribed into TSV for use by the scripts.

## Citation

```bibtex
@article{hoare2026sum,
  title  = {On the sum of a prime and a square-free number coprime to integers with at most three prime factors},
  author = {Hoare, Wilkie},
  year   = {2026},
  note   = {Preprint}
}
```
