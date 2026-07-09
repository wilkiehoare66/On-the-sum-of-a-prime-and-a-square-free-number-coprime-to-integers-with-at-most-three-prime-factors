#!/usr/bin/env python3
"""
ComputeBqBound.py
=================
Explicit upper bound for the divisible part

        B_q(n) = sum_{p<n, q|(n-p)} mu^2(n-p) log p  =  R(n) - R_q(n),

and the two criteria used to clear a three-prime modulus k = q1 q2 q3 (q1<q2<q3)
in the small-prime block of Lemma 5.4:

    (split)         R_{q1 q2}(n) > log 2 + B_{q3}(n)                    ==> R_k(n) > 0
    (comparison)    R(n)         > log 2 + B_{q1}(n)+B_{q2}(n)+B_{q3}(n) ==> R_k(n) > 0

For each k this script reports the smaller threshold of the two.  The THIRD strategy
of Lemma 5.4 -- the direct bound R_k(n) > 0 from Proposition 4.1 -- lives in
ComputeRkBound.py and is the one that clears k = 105 (neither criterion here does,
because 105's B_3+B_5+B_7 stays too large below 10^13).  Between the two scripts,
every modulus in the block clears within 2.55e11.

Raw c_theta data.  B_q's error term (I)_B, like R_k's, is sharpest when the
per-modulus theta bounds are read from the tables rather than the 1/840,1/160
envelope.  To keep this script and ComputeRkBound.py numerically identical on the
shared quantities (e.g. R_15(8e9) = 0.09527, not the envelope's 0.088), the raw
c_theta lookup, the table loaders, the R_m machinery and the missing-table guard
are IMPORTED from ComputeRkBound.py.  This script therefore requires

    ComputeRkBound.py        (its companion)
    bennett_c_theta.tsv  bennett_x0.tsv  rr_theta_table1.tsv  rr_theta_table2.tsv

to be present in the same directory; it aborts (via that guard) if a table is
missing rather than falling back to the envelope.  Main terms (the margin
coefficients below) involve no c_theta and are unchanged from the elementary
Estermann evaluation; only the error terms use the tables.

Usage:
    python3 ComputeBqBound.py --k 429            # both criteria for k, best threshold
    python3 ComputeBqBound.py --bq 13            # just the B_13 upper-bound error
    python3 ComputeBqBound.py --k 2431 --n 1e10  # criteria at a chosen n
"""
import argparse
import math
from math import gcd
from pathlib import Path

# Shared raw-c_theta infrastructure -- single source of truth, imported so the two
# scripts can never disagree on a c_theta value or on R_m.
from ComputeRkBound import (
    C_ARTIN, MAX_TABLE_MOD, Z, MIN_VALID_N, DEFAULT_N,
    require_tables,
    load_bennett_c_theta, load_bennett_x0, load_rr_table1, load_rr_table2,
    BennettBound,
    mobius_sieve, spf_sieve, phi_sieve, phi_square,
    choose_best_bound,
    factor_squarefree, alpha_coeff, beta_coeff, tail_constant, evaluate,
)


def one_minus(p):
    """The local Euler factor 1 - 1/(p(p-1))."""
    return 1.0 - 1.0 / (p * (p - 1))


# R(n)/n > 0.32035 for n >= 4.81e9, by Theorem 2.4 (Lee-O'Clarey Thm 3.3, imported,
# not re-proved here).  Used only in the R-comparison; the split's R_{q1q2} is the
# raw Corollary 4.2 value computed via ComputeRkBound.evaluate.
R_UNRESTRICTED_LOWER = 0.32035


# --------------------------------------------------------------------------
# context: sieves, loaded tables, and a cache of suffix tails
# --------------------------------------------------------------------------
def build_context():
    here = Path(__file__).resolve().parent
    require_tables(here)                      # aborts if any table is missing/empty
    bennett_c_theta = load_bennett_c_theta(here / "bennett_c_theta.tsv")
    bennett_x0 = load_bennett_x0(here / "bennett_x0.tsv")
    bennett = {m: BennettBound(c_theta=bennett_c_theta[m], x_theta=bennett_x0[m])
               for m in bennett_c_theta if m in bennett_x0}
    return {
        "mu": mobius_sieve(Z),
        "spf": spf_sieve(Z),
        "phi": phi_sieve(MAX_TABLE_MOD),
        "bennett": bennett,
        "rr1": load_rr_table1(here / "rr_theta_table1.tsv"),
        "rr2": load_rr_table2(here / "rr_theta_table2.tsv"),
        "suf_cache": {},
    }


def suffix_tail(q, ctx):
    """suf[a] = sum_{a'>=a, (a',q)=1, mu!=0} 1/phi(a'^2), tabulated to Z (cached per q)."""
    cache = ctx["suf_cache"]
    if q not in cache:
        mu, spf = ctx["mu"], ctx["spf"]
        suf = [0.0] * (Z + 2)
        for a in range(Z, 0, -1):
            add = (1.0 / phi_square(a, spf)) if (mu[a] and gcd(a, q) == 1) else 0.0
            suf[a] = suf[a + 1] + add
        cache[q] = suf
    return cache[q]


# --------------------------------------------------------------------------
# B_q(n)/n upper-bound ERROR term (main term handled separately via margins)
#   err = (I)_B + (II)_B + (III)_B ;  (I)_B uses the raw tables, (II)/(III) do not
# --------------------------------------------------------------------------
def Bq_error(q, n, ctx):
    mu, phi = ctx["mu"], ctx["phi"]
    bennett, rr1, rr2 = ctx["bennett"], ctx["rr1"], ctx["rr2"]
    logn = math.log(n)
    c = int(math.floor(math.sqrt(MAX_TABLE_MOD / q)))     # ensures every modulus <= 1e5
    suf = suffix_tail(q, ctx)

    # (I)_B : two families of moduli q a^2 (a<=c) and q^2 b^2 (b<=c/q), sharp per modulus
    I = 0.0
    for a in range(1, c + 1):
        if mu[a] and gcd(a, q) == 1:
            m = q * a * a
            I += choose_best_bound(n, m, phi[m], bennett, rr1, rr2).contribution
    for b in range(1, c // q + 1):
        if mu[b] and gcd(b, q) == 1:
            m = q * q * b * b
            I += choose_best_bound(n, m, phi[m], bennett, rr1, rr2).contribution

    T = suf[c + 1] + 4.0 / Z
    cb = c // q
    T_b = suf[cb + 1] + 4.0 * q / Z

    # (II)_B (sharp Brun-Titchmarsh) + (III)_B (trivial range) depend only on A: optimise
    def tail_err(A):
        denom = (1 - 2 * A) * logn - math.log(q)
        if denom <= 0:
            return float("inf")
        f = logn / denom
        II = (1.0 / (q - 1)) * (1 + 2 * f) * T + (1.0 / (q * (q - 1))) * (1 + 2 * f) * T_b
        III = ((1 + 1.0 / q) * math.exp(-A * logn) / q
               + (1 + 1.0 / q) * math.exp(-0.5 * logn)
               + math.exp((A - 1) * logn)) * logn
        return II + III

    A = min((i / 10000.0 for i in range(100, 4900)), key=tail_err)
    return {"main_coeff": 1.0 / q, "I": I, "err": I + tail_err(A), "A": A, "c": c}


# --------------------------------------------------------------------------
# R_m(n)/n lower bound via the imported ComputeRkBound machinery (fixed c,
# so it is byte-identical to Corollary 4.2).  Returns (G, bound), G the main term.
# --------------------------------------------------------------------------
def R_lower(m, n, ctx):
    primes = factor_squarefree(m)                      # [] when m == 1  -> unrestricted R
    beta = beta_coeff(primes)
    alpha = alpha_coeff(primes)
    c = int(math.floor(math.sqrt(MAX_TABLE_MOD / m)))
    tail = tail_constant(m, c, ctx["mu"], ctx["spf"])
    r = evaluate(n, m, c, ctx["mu"], ctx["phi"], ctx["bennett"], ctx["rr1"], ctx["rr2"],
                 tail, alpha, beta)
    return beta * C_ARTIN, r["bound"]


# --------------------------------------------------------------------------
# the two criteria, expressed as SLACK over the common product W >= C_Artin.
# slack > 0  <=>  criterion holds (telescopes to R_lower - B_upper - log2/n).
# --------------------------------------------------------------------------
def split_terms(q1, q2, q3, n, ctx):
    G, Rb = R_lower(q1 * q2, n, ctx)
    B = Bq_error(q3, n, ctx)
    coef = (((q1 - 2) / (q1 - 1)) * ((q2 - 2) / (q2 - 1)) * (1 - 1.0 / (q3 * (q3 - 1)))
            - (1.0 / q3) * (1 - 1.0 / (q1 * (q1 - 1))) * (1 - 1.0 / (q2 * (q2 - 1))))
    margin = coef * C_ARTIN
    E = (G - Rb) + B["err"]
    slack = margin - E - math.log(2) / n
    return slack, {"Rbound": Rb, "E_R": G - Rb, "E_B": B["err"], "margin": margin, "base": q1 * q2, "sub": q3}


def rcomp_terms(q1, q2, q3, n, ctx):
    Rb = R_UNRESTRICTED_LOWER                           # thm:R; worst-case main G = C_Artin
    G = C_ARTIN
    Bs = {q: Bq_error(q, n, ctx)["err"] for q in (q1, q2, q3)}
    fR = one_minus(q1) * one_minus(q2) * one_minus(q3)
    fB = ((1.0 / q1) * one_minus(q2) * one_minus(q3)
          + (1.0 / q2) * one_minus(q1) * one_minus(q3)
          + (1.0 / q3) * one_minus(q1) * one_minus(q2))
    margin = (fR - fB) * C_ARTIN
    E = (G - Rb) + sum(Bs.values())
    slack = margin - E - math.log(2) / n
    return slack, {"Rbound": Rb, "E_R": G - Rb, "sumB": sum(Bs.values()), "margin": margin}


def best_slack(k, n, ctx):
    q1, q2, q3 = factor_squarefree(k)
    ss, sd = split_terms(q1, q2, q3, n, ctx)
    rs, rd = rcomp_terms(q1, q2, q3, n, ctx)
    if ss >= rs:
        return ss, "split", sd
    return rs, "R-comparison", rd


def threshold(k, ctx, nmax=1e13):
    f = lambda n: best_slack(k, n, ctx)[0]
    lo, hi = MIN_VALID_N, nmax
    if f(lo) > 0:
        return lo, best_slack(k, lo, ctx)[1]
    if f(hi) <= 0:
        return None, None
    for _ in range(200):
        if hi / lo <= 1.0005:
            break
        mid = math.sqrt(lo * hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return hi, best_slack(k, hi, ctx)[1]


# --------------------------------------------------------------------------
def report_criterion(k, n, ctx):
    q1, q2, q3 = factor_squarefree(k)
    slack, which, d = best_slack(k, n, ctx)
    print(f"  k = {k} = {q1}*{q2}*{q3}    n = {n:.3e}")
    ss, sd = split_terms(q1, q2, q3, n, ctx)
    rs, rd = rcomp_terms(q1, q2, q3, n, ctx)
    print(f"    split       R_{q1*q2} >= {sd['Rbound']:.5f}  (E_R={sd['E_R']:.5f}), "
          f"E_B{q3}={sd['E_B']:.5f}, margin={sd['margin']:.5f}  ->  slack {ss:+.5f}")
    print(f"    comparison  R >= {rd['Rbound']:.5f}  (E_R={rd['E_R']:.5f}), "
          f"sum B_q={rd['sumB']:.5f}, margin={rd['margin']:.5f}  ->  slack {rs:+.5f}")
    print(f"    best: {which}, slack {slack:+.5f}  ->  "
          f"{'R_%d(n) > 0 PROVEN' % k if slack > 0 else 'not yet (raise n)'}")


def main():
    ap = argparse.ArgumentParser(description="Explicit B_q bound and the two small-block criteria")
    ap.add_argument("--k", type=int, help="three-prime squarefree k (e.g. 429, 105, 2431)")
    ap.add_argument("--bq", type=int, help="just print the B_q upper-bound error for prime q")
    ap.add_argument("--n", type=float, default=DEFAULT_N, help="evaluation point (default 8e9)")
    args = ap.parse_args()

    if args.n < MIN_VALID_N:
        raise SystemExit(f"n = {args.n:.3e} is below the validity floor {MIN_VALID_N:.0e}.")

    ctx = build_context()

    if args.bq:
        b = Bq_error(args.bq, args.n, ctx)
        print(f"B_{args.bq} upper-bound error at n={args.n:.3e}: "
              f"E_B{args.bq} = {b['err']:.6f}  (main coeff 1/{args.bq} = {b['main_coeff']:.5f}, "
              f"I={b['I']:.5f}, c={b['c']}, A={b['A']:.4f})")

    if args.k:
        primes = factor_squarefree(args.k)
        if len(primes) != 3:
            raise SystemExit(f"k={args.k} must be a squarefree product of three odd primes")
        report_criterion(args.k, args.n, ctx)
        t, which = threshold(args.k, ctx)
        if t is None:
            print("  threshold: neither criterion clears below 1e13 "
                  "(if k has a factor 3, this is expected -- use ComputeRkBound.py's direct bound)")
        else:
            print(f"  threshold: R_{args.k}(n) > 0 for n >= {t:.3e} via {which} "
                  f"(log10 {math.log10(t):.2f}; within 2.55e11: {t <= 2.55e11})")

    if not args.k and not args.bq:
        ap.print_help()


if __name__ == "__main__":
    main()
