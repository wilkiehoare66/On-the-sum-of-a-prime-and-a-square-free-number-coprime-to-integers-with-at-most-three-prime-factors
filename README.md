# On the sum of a prime and a square-free number coprime to integers with at most three prime factors

Code and data for the computational parts of the paper

> **On the sum of a prime and a square-free number coprime to integers with at most three prime factors**
> W. Hoare, E. Lee, and A. Pearce-Crump.

The paper's main theorem states that for every integer `k > 1` with at most three
prime factors, every integer `n ≥ 60` (every even `n ≥ 60` when `k` is even) is a
sum of a prime and a square-free number coprime to `k`. Its proof has two
computational halves, and this repository contains both:

1. an **analytic** half (Python) that evaluates the explicit lower bound for the
   weighted representation count `R_k(n)` and the upper bound for the divisible
   mass `B_q(n)`, producing the constants and thresholds of Sections 4–6 with
   directed-rounding certificates; and
2. a **finite** half (C++) that exhaustively verifies the statement for
   `60 ≤ n ≤ 2·10¹²`, below the point where the analytic bounds take over.

Everything is deterministic and self-contained; no external services are used.

---

## Repository layout

```
.
├── ComputeRkBound.py          # explicit lower bound for R_k(n)         (Prop. 4.1)
├── ComputeBqBound.py          # explicit upper bound for B_q(n) + the   (Prop. 4.3,
│                              #   split/comparison criteria of Lemma 5.4  Lemma 5.4)
├── make_certificates.py       # builds the machine-readable certificate bundle
├── verify_certificate.py      # independent checker for that bundle
├── row_certificates.json      # archived certificate for every three-prime modulus
├── bennett_c_theta.tsv        # per-modulus θ(x;m,a) error constants  (Bennett et al.)
├── bennett_x0.tsv             #   and their validity thresholds x₀
├── rr_theta_table1.tsv        # Ramaré–Rumely ε(x;m) table 1
├── rr_theta_table2.tsv        # Ramaré–Rumely √x-bound table 2
└── verification/              # the finite (C++) verification
    ├── verify_odd.cpp         #   odd n:   four disjoint-support square-free witnesses
    ├── verify_even.cpp        #   even n:  two distinct Goldbach splits
    ├── verify_large_prime.cpp #   prime + square-free (unconstrained), as a cross-check
    ├── prime64.hpp            #   Baillie–PSW / Montgomery primality backend
    └── results/               #   recorded output of the exhaustive runs
```

---

## Part 1 — Analytic constants (Python)

Requires **Python 3.8+** and only the standard library. The four `.tsv` tables
must sit next to the scripts; the scripts abort if a table is missing rather than
silently falling back to a weaker envelope.

### The two evaluators

`ComputeRkBound.py` evaluates the explicit lower bound for `R_k(n)/n`
(Proposition 4.1). Its error budget is `(I) + (II) + (III)`, where `(III)`
includes the tail range `d > n^A/√k`, the trivial range, and the bad-gcd terms
`(d,n) > 1`.

```bash
python3 ComputeRkBound.py --k 15               # R_15(n)/n bound at n = 8·10⁹
python3 ComputeRkBound.py --k 105 --threshold  # also report the least n with R_k(n) > 0
python3 ComputeRkBound.py --k 1  --n 8e9       # the unrestricted count R(n)/n
```

`ComputeBqBound.py` evaluates the two-family upper bound for the divisible mass
`B_q(n)/n` (Proposition 4.3) and the two criteria that clear a three-prime
modulus `k = q₁q₂q₃`:

- **split** — `R_{q₁q₂}(n) > log 2 + B_{q₃}(n)`
- **comparison** — `R(n) > log 2 + B_{q₁}(n) + B_{q₂}(n) + B_{q₃}(n)`

Both criteria are taken over the common Euler product
`P_k(n) = ∏_{p∤kn}(1 − 1/(p(p−1))) ≥ C_Artin`, so the unrestricted side
contributes its genuine explicit-estimate error `E_R(n)` rather than a flat
lower bound.

```bash
python3 ComputeBqBound.py --bq 13              # just the B_13 error term
python3 ComputeBqBound.py --k 429              # both criteria + best threshold for k
python3 ComputeBqBound.py --k 105 --certify    # directed-rounding certificate for k
```

### Two implementation notes

**Two families.** Imposing `q | (n−p)` splits the sieve modulus `lcm(q,d²)` into a
family `qd²` (when `(d,q)=1`) and a family `q²b²` (writing `d = qb`). The two
families carry **separate cutoffs** `(c₁,Z₁)` and `(c₂,Z₂)`, with the second
family's large range cut at `b > n^A/q` — since `q²b² ≤ n^{2A}` forces
`b ≤ n^A/q`, not `b ≤ n^A`. Keeping them separate is what makes the bound sound.

**Directed rounding.** Every error term is rounded **up** and every lower bound
**down**, with a safety widening of `10⁻⁹` (more than six orders of magnitude
above the accumulated double-precision rounding error, which is at the `10⁻¹⁶`
scale). A positive certified slack is therefore a genuine proof of the
corresponding inequality.

### Certificates

The prime-counting bounds available per modulus change admissibility at
`x = 10¹⁰` (the Ramaré–Rumely `√x`-bound is used only for `n ≤ 10¹⁰`), so each
threshold is certified **separately** on `[8·10⁹, 10¹⁰]` and on `(10¹⁰, ∞)`. On
each interval the admissible-bound set is fixed and every error term decreases in
`n`, so the left endpoint of the interval furnishes a rigorous maximum of the
error — no single search is ever run across the discontinuity.

`make_certificates.py` regenerates `row_certificates.json`, which records, for
each of the twenty three-prime moduli:

- the exact parameter choices (`c₁, c₂, A`, and the `c` for each `R`);
- the **source and validity range** of every prime-counting bound used, per
  modulus (Bennett-raw / RR-Table1 / RR-Table2 / Bennett-envelope, with its `x₀`);
- every contribution **before** rounding;
- the directed-rounded interval used;
- the certified threshold and the interval-by-interval check.

```bash
python3 make_certificates.py       # (re)build row_certificates.json  (~2.3 MB)
python3 verify_certificate.py      # independently re-check every record
```

`verify_certificate.py` is a deliberately **separate** checker: it imports
neither evaluator, reloads the tables itself, re-validates that every recorded
bound is in-date at the threshold, independently recomputes each contribution,
and re-checks that every slack is positive. It exits nonzero if any record fails.

### Reproducing the paper's constants

| Quantity | Command | Paper |
| --- | --- | --- |
| `R_15(n)/n ≥ 0.09527` | `python3 ComputeRkBound.py --k 15` | Cor. 4.2 |
| `R(n)/n` error at `k=1` | `python3 ComputeRkBound.py --k 1` | §4.4 |
| `B_13` error | `python3 ComputeBqBound.py --bq 13` | §4 example |
| `k = 105` threshold `≈ 1.23·10¹¹` | `python3 ComputeBqBound.py --k 105 --certify` | Table 2 |
| all twenty rows certified | `python3 make_certificates.py && python3 verify_certificate.py` | Table 2 |

---

## Part 2 — Finite verification (C++)

The C++ programs in `verification/` exhaustively check the theorem for
`60 ≤ n ≤ 2·10¹²`. Each is a single source that builds with either of two
primality backends, selected at compile time:

- **default** — inline deterministic Miller–Rabin with the twelve
  Sorenson–Webster bases, valid unconditionally for every `n < 3.317·10²⁴`; this
  is the backend of record for the reported ranges.
- **`-DUSE_BPSW`** — Baillie–PSW with Montgomery multiplication (from
  `prime64.hpp`); faster, but exhaustive only conjecturally. Requires C++20.

```bash
cd verification

# odd n — build and self-test, then run
g++ -O2 -std=c++17 -fopenmp verify_odd.cpp -o verify_odd
g++ -O0 -g -std=c++17 -fopenmp -fsanitize=address,undefined \
    verify_odd.cpp -o verify_odd_san
./verify_odd_san --selftest          # regression suite (run before any full run)
./verify_odd --test                  # single-chunk timing sample
./verify_odd                         # full range  (resumable with --resume)

# even n and the unconstrained cross-check build the same way
g++ -O2 -std=c++17 -fopenmp verify_even.cpp        -o verify_even
g++ -O2 -std=c++17 -fopenmp verify_large_prime.cpp -o verify_large_prime

# faster Baillie–PSW variants (C++20)
g++ -O2 -std=c++20 -fopenmp -DUSE_BPSW verify_odd.cpp -o verify_odd_bpsw
```

Each verifier writes a CSV of its per-chunk results and checkpoints its progress,
so a run can be interrupted and resumed with `--resume`. The recorded output of
the exhaustive runs is kept under `verification/results/`.

**Method, in brief.**
For **odd** `n`, the program seeks four square-free summands `ℓ` with `n − ℓ`
prime and pairwise disjoint odd prime supports; four such witnesses are pairwise
coprime in their odd parts, so at least one is coprime to any modulus with at
most three prime factors. A fast path uses `ℓ = 2r` for an odd prime `r` (which
is automatically square-free with singleton support `{r}`), backed by a complete
square-free test on the exhaustive fallback. For **even** `n`, it seeks two
distinct Goldbach splits `n = p₁+p₂ = p₃+p₄`; four distinct primes are pairwise
coprime, and the search runs in tiers of increasing cost that all certify the
same object.

---

## Notes for reviewers

- The analytic and finite halves meet below `2·10¹²`: every threshold the
  analytic lemmas invoke (`8·10⁹` and `1.25·10¹¹`) lies inside the exhaustively
  verified range, so the two halves together cover every `n ≥ 60`.
- Every displayed numerical bound in the paper is rounded in the safe direction
  (errors and thresholds up, main terms and margins down); `row_certificates.json`
  records the pre-rounding values and the rounded interval for each row, and
  `verify_certificate.py` checks the arithmetic independently of the optimisation.
- The C++ self-tests (`--selftest`) encode the regression checks required for the
  finite verification and should pass under the address/undefined-behaviour
  sanitizers before any full run.
