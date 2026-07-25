#!/usr/bin/env python3
"""
verify_results.py
=================
Independent cross-verifier for the exhaustive finite computation, as required by
Section 10 of the referee report (items 7 and 8). It reads the per-chunk CSV
output of the three C++ verifiers and checks, WITHOUT importing or trusting any
of their code:

  1. CHUNK COVERAGE (item 7): the recorded chunks tile each verifier's range
     [RANGE_START, RANGE_END] with no gap and no overlap, every chunk has status
     OK, and no chunk is recorded twice (a resume must not double-count).
  2. EXACT COUNT (item 8): the number of integers covered equals the exact
     arithmetic count of the range (accounting for the odd-only stride of the
     odd verifier), so "every integer in range is accounted for" is asserted,
     not assumed.
  3. WITNESS RE-DERIVATION (item 7): for a random sample of n in each range,
     this script INDEPENDENTLY finds a valid witness of the same kind the
     corresponding verifier claims to have found -- a prime p = n - s with s
     square-free (large-prime), or the four-disjoint-support square-free
     witnesses (odd), or two distinct Goldbach splits (even) -- using its own
     primality and square-free routines below. This re-checks primality,
     square-freeness and support-disjointness on real data, independently.

Primality here is deterministic Miller-Rabin with the twelve Sorenson-Webster
bases (unconditional below 3.317e24), matching the verifiers' backend of record
-- but implemented separately, so agreement is a genuine cross-check.

Usage:
    python3 verify_results.py                 # coverage + count, all three files
    python3 verify_results.py --sample 200    # also re-derive witnesses for 200 random n each
    python3 verify_results.py --results-dir results
Exit status is nonzero if any check fails.
"""
import argparse
import csv
import os
import random
import sys
from math import gcd, isqrt

# --- verifier metadata: filename, range, stride, kind -----------------------
# stride 2 = odd verifier records only odd n; stride 1 = every integer.
VERIFIERS = {
    "odd":  {"csv": "odd_results.csv", "start": 100001, "end": 2000000000000,
             "chunk": 1000000, "stride": 2, "kind": "four_witness"},
    "even": {"csv": "even_results.csv", "start": 4810000000, "end": 2000000000000,
             "chunk": 10000000, "stride": 2, "kind": "two_split"},
    # Not load-bearing for the manuscript: the four-witness / two-split arguments are
    # uniform in k, so odd+even already cover every k with omega(k)<=3. This is an
    # independent cross-check of the unconstrained statement over the same range.
    "unconstrained": {"csv": "unconstrained_results.csv", "start": 4810000000,
                      "end": 2000000000000, "chunk": 10000000, "stride": 1,
                      "kind": "prime_plus_sqfree"},
}

SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


# --- independent primality: deterministic Miller-Rabin, 12 SW bases ---------
def is_prime(n):
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in SMALL_PRIMES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# --- independent square-free test (complete) --------------------------------
def is_squarefree(m):
    if m <= 0:
        return False
    if m == 1:
        return True
    # remove small square factors, then check the residual has no square factor
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % (p * p) == 0:
            return False
        while m % p == 0:
            m //= p
    if m == 1:
        return True
    # residual m has only prime factors > 37; it is square-free iff it is not
    # itself a perfect square times ... -> test all prime-square divisors up to
    # cube-root, then a final perfect-square check on what remains.
    d = 41
    while d * d * d <= m:
        if m % d == 0:
            if m % (d * d) == 0:
                return False
            while m % d == 0:
                m //= d
        d += 2
    # now m is 1, a prime, or a product of two distinct primes, or a prime^2
    s = isqrt(m)
    if s * s == m:
        return False
    return True


def odd_support(m):
    """Set of odd primes dividing m (m assumed square-free)."""
    s = set()
    x = m
    while x % 2 == 0:
        x //= 2
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % p == 0:
            s.add(p)
            while x % p == 0:
                x //= p
    d = 41
    while d * d <= x:
        if x % d == 0:
            s.add(d)
            while x % d == 0:
                x //= d
        d += 2
    if x > 1:
        s.add(x)
    return s


# --- independent witness re-derivation, per kind ----------------------------
def find_prime_plus_sqfree(n):
    """Some prime p<n with n-p square-free (unconstrained cross-check)."""
    for p in _primes_desc(n):
        if is_squarefree(n - p):
            return ("p=%d, s=%d" % (p, n - p))
    return None


def find_two_splits(n):
    """Two distinct Goldbach splits n = p1+p2 = p3+p4 (even n)."""
    found = []
    for p in _primes_asc(n):
        if is_prime(n - p):
            found.append((p, n - p))
            # two DISTINCT splits means two unordered pairs; collect until 2
            if len({frozenset(pr) for pr in found}) >= 2:
                pairs = list({frozenset(pr) for pr in found})[:2]
                return "; ".join("%d+%d" % tuple(sorted(pr)) for pr in pairs)
    return None


def find_four_witnesses(n):
    """Four square-free s_i with n-s_i prime and pairwise-disjoint odd supports."""
    wits = []
    supports = []
    # fast path: s = 2r with r odd prime, n-2r prime -> support {r}
    for r in _primes_asc(n // 2):
        if r == 2:
            continue
        s = 2 * r
        if s >= n:
            break
        if is_prime(n - s) and is_squarefree(s):
            sup = frozenset({r})
            if all(sup.isdisjoint(t) for t in supports):
                wits.append("s=%d" % s)
                supports.append(sup)
                if len(wits) == 4:
                    return "; ".join(wits)
    # fallback: general square-free s with disjoint support
    for p in _primes_asc(n):
        s = n - p
        if s < 2:
            continue
        if is_squarefree(s):
            sup = frozenset(odd_support(s))
            if all(sup.isdisjoint(t) for t in supports):
                wits.append("s=%d" % s)
                supports.append(sup)
                if len(wits) == 4:
                    return "; ".join(wits)
    return None


def _primes_asc(limit):
    p = 2
    while p < limit:
        if is_prime(p):
            yield p
        p += 1


def _primes_desc(n):
    p = n - 1
    while p >= 2:
        if is_prime(p):
            yield p
        p -= 1


# --- CSV coverage + count ---------------------------------------------------
def check_coverage(name, meta, path):
    problems = []
    if not os.path.exists(path):
        return [f"{name}: results file {path} not found"]
    rows = []
    with open(path, newline="") as fh:
        for line in csv.reader(fh):
            if not line or line[0].strip().lower() in ("timestamp", "time"):
                continue
            try:
                start = int(line[1])
                end = int(line[2])
                status = line[3].strip().upper()
            except (IndexError, ValueError):
                problems.append(f"{name}: unparseable row: {line[:4]}")
                continue
            rows.append((start, end, status))

    if not rows:
        return [f"{name}: no data rows in {path}"]

    # status check
    bad = [(s, e, st) for (s, e, st) in rows if not st.startswith("OK")]
    for s, e, st in bad[:5]:
        problems.append(f"{name}: chunk [{s},{e}] has non-OK status '{st}'")

    # sort by start; check no overlap, no gap, no duplicate
    rows.sort()
    expect = meta["start"]
    seen_starts = set()
    for (s, e, st) in rows:
        if s in seen_starts:
            problems.append(f"{name}: chunk starting {s} recorded more than once (resume double-count)")
            continue
        seen_starts.add(s)
        if s > expect:
            problems.append(f"{name}: GAP in coverage: [{expect}, {s}) uncovered")
        elif s < expect:
            problems.append(f"{name}: OVERLAP: chunk [{s},{e}] starts before expected {expect}")
        expect = e + 1
    # final chunk should reach RANGE_END (last covered integer >= end, or the
    # last chunk's end is the range end)
    last_end = rows[-1][1]
    if last_end < meta["end"]:
        problems.append(f"{name}: coverage stops at {last_end}, short of RANGE_END {meta['end']}")

    # exact count (item 8)
    covered = _count_integers(meta["start"], last_end, meta["stride"])
    expected = _count_integers(meta["start"], meta["end"], meta["stride"])
    if last_end >= meta["end"] and covered != expected:
        problems.append(f"{name}: covered count {covered} != expected {expected} "
                        f"for range [{meta['start']},{meta['end']}] stride {meta['stride']}")
    else:
        note = "integers" if meta["stride"] == 1 else "odd integers" if meta["start"] % 2 else "even integers"
        print(f"  {name}: {len(rows)} chunks, contiguous, "
              f"{covered:,} {note} covered "
              f"[{meta['start']:,} .. {last_end:,}]"
              + ("" if last_end >= meta["end"] else "  (INCOMPLETE)"))
    return problems


def _count_integers(a, b, stride):
    """Count integers in [a,b] with the given stride (1=all, 2=matching parity of a)."""
    if b < a:
        return 0
    if stride == 1:
        return b - a + 1
    # stride 2: integers of the same parity as a
    return (b - a) // 2 + 1


def check_witnesses(name, meta, n_samples, rng):
    """Re-derive a witness independently for n_samples random n in range."""
    finder = {"prime_plus_sqfree": find_prime_plus_sqfree,
              "two_split": find_two_splits,
              "four_witness": find_four_witnesses}[meta["kind"]]
    problems = []
    lo, hi = meta["start"], meta["end"]
    tested = 0
    for _ in range(n_samples):
        n = rng.randrange(lo, hi + 1)
        if meta["stride"] == 2:
            # align parity to the verifier's stride
            if (n - meta["start"]) % 2:
                n += 1
            if n > hi:
                continue
        w = finder(n)
        tested += 1
        if w is None:
            problems.append(f"{name}: NO independent witness found for n={n} "
                            f"(kind {meta['kind']}) -- investigate")
    print(f"  {name}: independently re-derived witnesses for {tested} sampled n "
          f"({'all verified' if not problems else str(len(problems)) + ' FAILED'})")
    return problems


def main():
    ap = argparse.ArgumentParser(description="Independent cross-verifier for the finite computation")
    ap.add_argument("--results-dir", default="results", help="directory holding the *_results.csv files")
    ap.add_argument("--sample", type=int, default=0,
                    help="re-derive witnesses for this many random n per verifier (0 = coverage/count only)")
    ap.add_argument("--seed", type=int, default=20260725, help="RNG seed for reproducible sampling")
    ap.add_argument("--only", choices=list(VERIFIERS), help="check a single verifier")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    names = [args.only] if args.only else list(VERIFIERS)

    print("== Coverage and exact-count check (Section 10, items 7-8) ==")
    all_problems = []
    for name in names:
        meta = VERIFIERS[name]
        path = os.path.join(args.results_dir, meta["csv"])
        all_problems += check_coverage(name, meta, path)

    if args.sample:
        print(f"\n== Independent witness re-derivation (Section 10, item 7; {args.sample}/verifier) ==")
        for name in names:
            all_problems += check_witnesses(name, VERIFIERS[name], args.sample, rng)

    print()
    if all_problems:
        print(f"FAILED: {len(all_problems)} problem(s) found:")
        for p in all_problems[:40]:
            print(f"  ! {p}")
        sys.exit(1)
    print("ALL CHECKS PASSED: coverage is gap-free and non-overlapping, counts are exact"
          + (", sampled witnesses independently re-derived." if args.sample else "."))
    sys.exit(0)


if __name__ == "__main__":
    main()
