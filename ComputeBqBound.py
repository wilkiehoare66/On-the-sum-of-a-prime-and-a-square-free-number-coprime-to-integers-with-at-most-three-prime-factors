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

For each k this script reports the better threshold of the two, and (with
--certify) a directed-rounding certificate proving R_k(n) > 0 at that threshold.

Two-family B_q (Proposition 4.3).  Imposing q | (n-p) splits the sieve modulus
lcm(q,d^2) into a family qd^2 (when (d,q)=1) and a family q^2 b^2 (writing
d=qb). The two families carry SEPARATE cutoffs: c1,Z1 for qd^2 with large-range
boundary d>n^A, and c2,Z2 for q^2 b^2 with boundary b>n^A/q (since
q^2 b^2 <= n^{2A} forces b <= n^A/q). Keeping them separate prevents the second
family's large range from being undercounted. The short range carries a p=n
endpoint term; the large range carries the bad-gcd (d,n)>1 / (b,n)>1 terms.

Coupled comparison.  The comparison is taken over the common Euler product
P_k(n) = prod_{p not| kn}(1-1/(p(p-1))) >= C_Artin, so the unrestricted side
contributes its genuine explicit-estimate error E_R(n) (from R_k at k=1,
including its bad-gcd term), not a flat lower bound.

Raw c_theta data, table loaders, R_m machinery and the missing-table guard are
IMPORTED from ComputeRkBound.py. Requires ComputeRkBound.py and the four
c_theta tables in the same directory; aborts if a table is missing.

Usage:
    python3 ComputeBqBound.py --k 429              # both criteria for k, best threshold
    python3 ComputeBqBound.py --bq 13              # just the B_13 upper-bound error
    python3 ComputeBqBound.py --k 2431 --n 1e10    # criteria at a chosen n
    python3 ComputeBqBound.py --k 105 --certify    # directed-rounding certificate
"""
import argparse
import json
import math
from math import gcd, floor, sqrt
from pathlib import Path
from decimal import Decimal, getcontext, ROUND_UP, ROUND_DOWN

from ComputeRkBound import (
    C_ARTIN, MAX_TABLE_MOD, Z, MIN_VALID_N, DEFAULT_N,
    require_tables,
    load_bennett_c_theta, load_bennett_x0, load_rr_table1, load_rr_table2,
    BennettBound,
    mobius_sieve, spf_sieve, phi_sieve, phi_square,
    choose_best_bound,
    factor_squarefree, alpha_coeff, beta_coeff, tail_constant, evaluate,
)

getcontext().prec = 40

# Directed-rounding envelope: >6 orders of magnitude above the measured double
# rounding error (~1e-16 on the tail sums).
SAFE_WIDEN = Decimal("1e-9")


def build_context():
    here = Path(__file__).resolve().parent
    require_tables(here)
    bct = load_bennett_c_theta(here / "bennett_c_theta.tsv")
    bx0 = load_bennett_x0(here / "bennett_x0.tsv")
    bennett = {m: BennettBound(c_theta=bct[m], x_theta=bx0[m]) for m in bct if m in bx0}
    return {"mu": mobius_sieve(Z), "spf": spf_sieve(Z), "phi": phi_sieve(MAX_TABLE_MOD),
            "bennett": bennett, "rr1": load_rr_table1(here / "rr_theta_table1.tsv"),
            "rr2": load_rr_table2(here / "rr_theta_table2.tsv"), "suf": {}}


def suffix_tail(q, ctx):
    if q not in ctx["suf"]:
        mu, spf = ctx["mu"], ctx["spf"]
        suf = [0.0] * (Z + 2)
        for a in range(Z, 0, -1):
            suf[a] = suf[a + 1] + ((1.0 / phi_square(a, spf)) if (mu[a] and gcd(a, q) == 1) else 0.0)
        ctx["suf"][q] = suf
    return ctx["suf"][q]


def S_tail(c, Zc, suf):
    return suf[c + 1] + 4.0 / Zc


def one_minus(p):
    return 1.0 - 1.0 / (p * (p - 1))


R_UNRESTRICTED_LOWER = 0.32035   # Theorem 2.4 flat bound (crude Lemma 5.1-type checks only)


def Bq_error(q, n, ctx, A=None, c1=None, c2=None, Z1=None, Z2=None):
    mu, phi = ctx["mu"], ctx["phi"]
    bennett, rr1, rr2 = ctx["bennett"], ctx["rr1"], ctx["rr2"]
    logn = math.log(n)
    suf = suffix_tail(q, ctx)
    if c1 is None:
        c1 = int(floor(sqrt(MAX_TABLE_MOD / q)))
    if c2 is None:
        c2 = c1 // q
    if Z1 is None:
        Z1 = Z
    if Z2 is None:
        Z2 = Z
    I = 0.0
    cnt1 = 0
    for d in range(1, c1 + 1):
        if mu[d] and gcd(d, q) == 1:
            m = q * d * d
            I += choose_best_bound(n, m, phi[m], bennett, rr1, rr2).contribution
            cnt1 += 1
    cnt2 = 0
    for b in range(1, c2 + 1):
        if mu[b] and gcd(b, q) == 1:
            m = q * q * b * b
            I += choose_best_bound(n, m, phi[m], bennett, rr1, rr2).contribution
            cnt2 += 1
    endpoint = (logn / n) * (cnt1 + cnt2)
    E_short = I + endpoint
    S1 = S_tail(c1, Z1, suf)
    S2 = S_tail(c2, Z2, suf)

    def E_med(A):
        d1 = (1 - 2 * A) * logn - math.log(q)
        if d1 <= 0:
            return None
        f1 = logn / d1
        f2 = 1.0 / (1 - 2 * A)
        return ((1 + 2 * f1) / (q - 1)) * S1 + ((1 + 2 * f2) / (q * (q - 1))) * S2

    def E_large(A):
        return ((2.0 / q) * n ** (-A) + (1 + 1.0 / q) * n ** (-0.5)
                + (1 + 1.0 / q) * n ** (A - 1.0)) * logn

    def tot(A):
        em = E_med(A)
        return None if em is None else E_short + em + E_large(A)

    if A is None:
        best = None
        for i in range(100, 4900):
            a = i / 10000.0
            t = tot(a)
            if t is not None and (best is None or t < best[1]):
                best = (a, t)
        A = best[0]
    em = E_med(A)
    return {"q": q, "A": A, "c1": c1, "c2": c2, "main_coeff": 1.0 / q,
            "E_short": E_short, "endpoint": endpoint, "E_med": em, "E_large": E_large(A),
            "err": E_short + em + E_large(A)}


def R_lower(m, n, ctx):
    primes = factor_squarefree(m)
    beta = beta_coeff(primes)
    alpha = alpha_coeff(primes)
    c = int(floor(sqrt(MAX_TABLE_MOD / m))) if m > 1 else 316
    tail = tail_constant(m, c, ctx["mu"], ctx["spf"])
    r = evaluate(n, m, c, ctx["mu"], ctx["phi"], ctx["bennett"], ctx["rr1"], ctx["rr2"],
                 tail, alpha, beta)
    return beta * C_ARTIN, r["bound"]


def split_terms(q1, q2, q3, n, ctx):
    G, Rb = R_lower(q1 * q2, n, ctx)
    B = Bq_error(q3, n, ctx)
    coef = (((q1 - 2) / (q1 - 1)) * ((q2 - 2) / (q2 - 1)) * (1 - 1.0 / (q3 * (q3 - 1)))
            - (1.0 / q3) * (1 - 1.0 / (q1 * (q1 - 1))) * (1 - 1.0 / (q2 * (q2 - 1))))
    margin = coef * C_ARTIN
    E = (G - Rb) + B["err"]
    slack = margin - E - math.log(2) / n
    return slack, {"Rbound": Rb, "E_R": G - Rb, "E_B": B["err"], "margin": margin, "B": B}


def rcomp_terms(q1, q2, q3, n, ctx):
    _, R_bound = R_lower(1, n, ctx)
    E_R = C_ARTIN - R_bound
    Bs = {q: Bq_error(q, n, ctx) for q in (q1, q2, q3)}
    fR = one_minus(q1) * one_minus(q2) * one_minus(q3)
    fB = ((1.0 / q1) * one_minus(q2) * one_minus(q3)
          + (1.0 / q2) * one_minus(q1) * one_minus(q3)
          + (1.0 / q3) * one_minus(q1) * one_minus(q2))
    margin = (fR - fB) * C_ARTIN
    E = E_R + sum(Bs[q]["err"] for q in (q1, q2, q3))
    slack = margin - E - math.log(2) / n
    return slack, {"E_R": E_R, "sumB": sum(Bs[q]["err"] for q in (q1, q2, q3)),
                   "margin": margin, "Bs": Bs}


def best_slack(k, n, ctx):
    q1, q2, q3 = factor_squarefree(k)
    ss, sd = split_terms(q1, q2, q3, n, ctx)
    rs, rd = rcomp_terms(q1, q2, q3, n, ctx)
    if ss >= rs:
        return ss, "split", sd
    return rs, "comparison", rd


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


def _D(x):
    return Decimal(repr(x))


def _up(x):
    return (_D(x) + SAFE_WIDEN).quantize(Decimal("1e-12"), rounding=ROUND_UP)


def _down(x):
    return (_D(x) - SAFE_WIDEN).quantize(Decimal("1e-12"), rounding=ROUND_DOWN)


def certify(k, n, ctx):
    q1, q2, q3 = factor_squarefree(k)
    G, Rb = R_lower(q1 * q2, n, ctx)
    Bsub = Bq_error(q3, n, ctx)
    coef = (((q1 - 2) / (q1 - 1)) * ((q2 - 2) / (q2 - 1)) * (1 - 1.0 / (q3 * (q3 - 1)))
            - (1.0 / q3) * (1 - 1.0 / (q1 * (q1 - 1))) * (1 - 1.0 / (q2 * (q2 - 1))))
    s_slack = _down(coef * C_ARTIN) - _up(G - Rb) - _up(Bsub["err"]) - _up(math.log(2) / n)
    _, R_bound = R_lower(1, n, ctx)
    Bs = {q: Bq_error(q, n, ctx) for q in (q1, q2, q3)}
    fR = one_minus(q1) * one_minus(q2) * one_minus(q3)
    fB = ((1.0 / q1) * one_minus(q2) * one_minus(q3)
          + (1.0 / q2) * one_minus(q1) * one_minus(q3)
          + (1.0 / q3) * one_minus(q1) * one_minus(q2))
    c_slack = (_down((fR - fB) * C_ARTIN) - _up(C_ARTIN - R_bound)
               - _up(sum(Bs[q]["err"] for q in (q1, q2, q3))) - _up(math.log(2) / n))
    which = "split" if s_slack >= c_slack else "comparison"
    slack = max(s_slack, c_slack)
    return {"k": k, "n": n, "criterion": which, "slack": str(slack), "proven": slack > 0,
            "split": {"margin_down": str(_down(coef * C_ARTIN)), "E_R_up": str(_up(G - Rb)),
                      "E_B_up": str(_up(Bsub["err"])), "slack": str(s_slack),
                      "Bq_terms": {kk: Bsub[kk] for kk in ("c1", "c2", "A", "E_short", "endpoint", "E_med", "E_large", "err")}},
            "comparison": {"margin_down": str(_down((fR - fB) * C_ARTIN)),
                           "E_R_up": str(_up(C_ARTIN - R_bound)),
                           "sumB_up": str(_up(sum(Bs[q]["err"] for q in (q1, q2, q3)))),
                           "slack": str(c_slack),
                           "Bq_terms": {q: {kk: Bs[q][kk] for kk in ("c1", "c2", "A", "err")} for q in (q1, q2, q3)}}}


def certified_threshold(k, ctx, nmax=1e13):
    f = lambda n: Decimal(certify(k, n, ctx)["slack"]) > 0
    lo, hi = MIN_VALID_N, nmax
    if f(lo):
        return lo
    if not f(hi):
        return None
    for _ in range(200):
        if hi / lo <= 1.0005:
            break
        mid = math.sqrt(lo * hi)
        if f(mid):
            hi = mid
        else:
            lo = mid
    return hi


def report_criterion(k, n, ctx):
    q1, q2, q3 = factor_squarefree(k)
    slack, which, _ = best_slack(k, n, ctx)
    print(f"  k = {k} = {q1}*{q2}*{q3}    n = {n:.3e}")
    ss, sd = split_terms(q1, q2, q3, n, ctx)
    rs, rd = rcomp_terms(q1, q2, q3, n, ctx)
    print(f"    split       R_{q1*q2} >= {sd['Rbound']:.5f}  (E_R={sd['E_R']:.5f}), "
          f"E_B{q3}={sd['E_B']:.5f}, margin={sd['margin']:.5f}  ->  slack {ss:+.6f}")
    print(f"    comparison  E_R={rd['E_R']:.5f} (coupled), "
          f"sum B_q={rd['sumB']:.5f}, margin={rd['margin']:.5f}  ->  slack {rs:+.6f}")
    print(f"    best: {which}, slack {slack:+.6f}  ->  "
          f"{'R_%d(n) > 0 PROVEN' % k if slack > 0 else 'not yet (raise n)'}")


def main():
    ap = argparse.ArgumentParser(description="Explicit two-family B_q bound and the small-block criteria")
    ap.add_argument("--k", type=int, help="three-prime squarefree k (e.g. 429, 105, 2431)")
    ap.add_argument("--bq", type=int, help="just print the B_q upper-bound error for prime q")
    ap.add_argument("--n", type=float, default=DEFAULT_N, help="evaluation point (default 8e9)")
    ap.add_argument("--certify", action="store_true", help="directed-rounding certificate at the threshold")
    args = ap.parse_args()
    if args.n < MIN_VALID_N:
        raise SystemExit(f"n = {args.n:.3e} is below the validity floor {MIN_VALID_N:.0e}.")
    ctx = build_context()
    if args.bq:
        b = Bq_error(args.bq, args.n, ctx)
        print(f"B_{args.bq} upper-bound error at n={args.n:.3e}: "
              f"E_B{args.bq} = {b['err']:.6f}  (main coeff 1/{args.bq} = {b['main_coeff']:.5f}, "
              f"c1={b['c1']}, c2={b['c2']}, A={b['A']:.4f}; "
              f"short={b['E_short']:.5f} med={b['E_med']:.5f} large={b['E_large']:.2e})")
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
        if args.certify:
            ct = certified_threshold(args.k, ctx)
            if ct is None:
                print("  certificate: no certified threshold below 1e13")
            else:
                cert = certify(args.k, ct, ctx)
                print(f"  certificate (directed rounding) at n={ct:.4e}: "
                      f"criterion={cert['criterion']}, slack={cert['slack']}, proven={cert['proven']}")
                fname = f"certificate_k{args.k}.json"
                with open(fname, "w") as fh:
                    json.dump({"threshold": ct, **cert}, fh, indent=2)
                print(f"  wrote {fname}")
    if not args.k and not args.bq:
        ap.print_help()


if __name__ == "__main__":
    main()
