#!/usr/bin/env python3
"""
make_certificates.py
====================
Produce the full machine-readable certificate bundle required by Section 7.3:
for every three-prime modulus, a record containing

  * the exact parameter choices (c1, c2, A per B_q; c per R);
  * the source and validity range of every prime-counting bound used, per
    modulus (Bennett-raw / RR-Table1 / RR-Table2 / Bennett-envelope, with x0);
  * every contribution before rounding;
  * the directed-rounded interval used (errors up, main terms down);
  * the certified threshold and the interval-by-interval check.

Interval structure (Section 7.2).  The admissible prime-counting bounds change
at 1e10 (the Ramare-Rumely Table-2 sqrt bound is valid only for n <= 1e10), so
the implemented minimum can jump upward there. Every error term is otherwise
monotone decreasing in n on a fixed-candidate interval (each is O(n^{-delta} log n)
or O(1/log n)), so the slack's minimum on such an interval is at its LEFT
endpoint. The certificate therefore splits [8e9, inf) at 1e10 and records the
certified slack at the left endpoint of each interval the row's relevant range
meets -- a rigorous per-interval maximum of the error, not a sample.

Companion: verify_certificate.py re-checks every record independently.
"""
import json
import math
from pathlib import Path
from decimal import Decimal, getcontext

import ComputeBqBound as B
from ComputeRkBound import (
    choose_best_bound, factor_squarefree, alpha_coeff, beta_coeff,
    collect_required_terms, tail_constant, MAX_TABLE_MOD, C_ARTIN,
    BROADBENT_THETA_CONST, BROADBENT_LOWER_X0,
)

getcontext().prec = 40

INTERVAL_BREAK = 1.0e10   # RR-Table2 validity edge
KS = [105, 165, 195, 231, 255, 273, 357, 385, 429, 455,
      561, 595, 663, 715, 935, 1001, 1105, 1309, 1547, 2431]


def bound_provenance_Bq(q, n, ctx):
    """Record which prime-counting bound is used for each modulus in B_q(q,n)."""
    mu, phi = ctx["mu"], ctx["phi"]
    bennett, rr1, rr2 = ctx["bennett"], ctx["rr1"], ctx["rr2"]
    B_terms = B.Bq_error(q, n, ctx)
    c1, c2 = B_terms["c1"], B_terms["c2"]
    recs = []
    for d in range(1, c1 + 1):
        if mu[d] and math.gcd(d, q) == 1:
            m = q * d * d
            cb = choose_best_bound(n, m, phi[m], bennett, rr1, rr2)
            recs.append({"family": "qd2", "d": d, "modulus": m, "source": cb.source,
                         "valid_x0": cb.lower_x0, "contribution": cb.contribution})
    for b in range(1, c2 + 1):
        if mu[b] and math.gcd(b, q) == 1:
            m = q * q * b * b
            cb = choose_best_bound(n, m, phi[m], bennett, rr1, rr2)
            recs.append({"family": "q2b2", "b": b, "modulus": m, "source": cb.source,
                         "valid_x0": cb.lower_x0, "contribution": cb.contribution})
    return {"c1": c1, "c2": c2, "A": B_terms["A"], "modulus_bounds": recs,
            "E_short": B_terms["E_short"], "endpoint": B_terms["endpoint"],
            "E_med": B_terms["E_med"], "E_large": B_terms["E_large"], "err": B_terms["err"]}


def bound_provenance_R(m, n, ctx):
    """Record which prime-counting bound is used for each modulus in R_m(m,n)."""
    mu, phi = ctx["mu"], ctx["phi"]
    bennett, rr1, rr2 = ctx["bennett"], ctx["rr1"], ctx["rr2"]
    from math import floor, sqrt
    c = int(floor(sqrt(MAX_TABLE_MOD / m))) if m > 1 else 316
    recs = []
    for a, d, modulus in collect_required_terms(m, c, mu):
        if modulus == 1:
            recs.append({"a": a, "modulus": 1, "source": "Broadbent-theta",
                         "valid_x0": BROADBENT_LOWER_X0,
                         "contribution": BROADBENT_THETA_CONST / math.log(n) ** 3})
        else:
            cb = choose_best_bound(n, modulus, phi[modulus], bennett, rr1, rr2)
            recs.append({"a": a, "divisor": d, "modulus": modulus, "source": cb.source,
                         "valid_x0": cb.lower_x0, "contribution": cb.contribution})
    _, Rb = B.R_lower(m, n, ctx)
    return {"c": c, "modulus_bounds": recs, "lower_bound": Rb}


def interval_checks(k, ctx, thr):
    """Left-endpoint certified slack on each fixed-candidate interval the row meets."""
    endpoints = []
    lo = max(thr, 8e9)
    # interval 1: [lo, 1e10] if lo < 1e10
    if lo < INTERVAL_BREAK:
        s = B.certify(k, lo, ctx)["slack"]
        endpoints.append({"interval": f"[{lo:.4e}, 1e10]", "left_endpoint": lo,
                          "candidates": "Bennett/RR-T1/RR-T2 admissible",
                          "slack_at_left": s, "positive": Decimal(s) > 0,
                          "note": "errors decrease in n on this interval; left endpoint is the max"})
    # interval 2: (1e10, inf), worst point just above 1e10 (or thr if higher)
    lo2 = max(thr, INTERVAL_BREAK * (1 + 1e-7))
    s2 = B.certify(k, lo2, ctx)["slack"]
    endpoints.append({"interval": f"({max(thr,1e10):.4e}, inf)", "left_endpoint": lo2,
                      "candidates": "Bennett/RR-T1 admissible (RR-T2 dropped at 1e10)",
                      "slack_at_left": s2, "positive": Decimal(s2) > 0,
                      "note": "RR-Table2 no longer admissible; errors decrease, left endpoint is the max"})
    return endpoints


def build_record(k, ctx):
    q1, q2, q3 = factor_squarefree(k)
    thr = B.certified_threshold(k, ctx)
    cert = B.certify(k, thr, ctx)
    which = cert["criterion"]

    rec = {
        "k": k, "factors": [q1, q2, q3],
        "certified_threshold": thr,
        "criterion": which,
        "slack_at_threshold": cert["slack"],
        "proven": cert["proven"],
        "rounded_interval": {
            "split": {kk: cert["split"][kk] for kk in ("margin_down", "E_R_up", "E_B_up", "slack")},
            "comparison": {kk: cert["comparison"][kk] for kk in ("margin_down", "E_R_up", "sumB_up", "slack")},
        },
        "parameters_and_provenance": {},
        "interval_checks": interval_checks(k, ctx, thr),
        "rounding_convention": "errors rounded UP, main/lower terms rounded DOWN, safety widening 1e-9",
    }
    # provenance for whichever pieces the winning criterion uses (record both anyway)
    rec["parameters_and_provenance"]["R_unrestricted"] = bound_provenance_R(1, thr, ctx)
    rec["parameters_and_provenance"][f"R_{q1*q2}"] = bound_provenance_R(q1 * q2, thr, ctx)
    for q in (q1, q2, q3):
        rec["parameters_and_provenance"][f"B_{q}"] = bound_provenance_Bq(q, thr, ctx)
    return rec


def main():
    ctx = B.build_context()
    bundle = {}
    print(f"{'k':>5} {'crit':>10} {'threshold':>12} {'proven':>7} {'intervals_ok':>12}")
    print("-" * 55)
    allok = True
    for k in KS:
        rec = build_record(k, ctx)
        iok = all(iv["positive"] for iv in rec["interval_checks"])
        proven = rec["proven"] and iok
        allok = allok and proven
        bundle[str(k)] = rec
        print(f"{k:>5} {rec['criterion']:>10} {rec['certified_threshold']:>12.3e} "
              f"{'yes' if rec['proven'] else 'NO':>7} {'yes' if iok else 'NO':>12}")
    print("-" * 55)
    print(f"all rows proven with interval checks: {allok}")

    out = Path("row_certificates.json")
    with out.open("w") as fh:
        json.dump(bundle, fh, indent=2, default=str)
    print(f"wrote {out} ({out.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
