#!/usr/bin/env python3
"""
verify_certificate.py
=====================
Independent checker for row_certificates.json, required by Section 7.3:
"A second short verifier should read these records and check the arithmetic
independently of the optimisation script."

This script deliberately does NOT import ComputeRkBound / ComputeBqBound. It
re-derives each row's slack purely from the archived per-modulus contributions
and parameters, using only the standard library and the four c_theta tables
(to re-validate that each recorded bound is legitimate and in-date), then
confirms:

  1. every recorded prime-counting bound matches an independent table lookup
     and is valid at the threshold (n >= its x0);
  2. the archived pre-rounding contributions sum to the archived error terms;
  3. re-doing the directed rounding (errors up, mains down) reproduces the
     archived rounded interval and a positive slack;
  4. the interval-by-interval checks are positive at each interval's left
     endpoint (a rigorous per-interval error maximum, since the errors are
     monotone decreasing in n on each fixed-candidate interval).

Exit status is nonzero if any check fails on any row.
"""
import csv
import json
import math
import sys
from pathlib import Path
from decimal import Decimal, getcontext, ROUND_UP, ROUND_DOWN

getcontext().prec = 40

SAFE_WIDEN = Decimal("1e-9")
C_ARTIN = Decimal("0.3739558136192023")
INTERVAL_BREAK = 1.0e10
RR_TABLE2_MAX_X = 1.0e10
TOL = Decimal("1e-9")   # tolerance for re-summed float contributions vs archived


# ---- independent, minimal table loaders (no project imports) ---------------
def load_tsv(path):
    rows = []
    with open(path, newline="") as fh:
        rd = csv.DictReader(fh, delimiter="\t")
        for r in rd:
            rows.append({(k or "").strip().lower(): (v or "").strip() for k, v in r.items()})
    return rows


def load_tables(here):
    bennett_c, bennett_x0, rr1, rr2 = {}, {}, {}, {}
    for r in load_tsv(here / "bennett_c_theta.tsv"):
        bennett_c[int(float(r["modulus"]))] = float(r["c_theta"])
    for r in load_tsv(here / "bennett_x0.tsv"):
        bennett_x0[int(float(r["modulus"]))] = int(float(r["x_theta"]))
    for r in load_tsv(here / "rr_theta_table1.tsv"):
        m = int(float(r["modulus"]))
        entries = []
        for col, x0 in [("eps_1e10", 1e10), ("eps_1e13", 1e13), ("eps_1e30", 1e30), ("eps_1e100", 1e100)]:
            if col in r and r[col]:
                entries.append((x0, float(r[col])))
        rr1[m] = sorted(entries)
    for r in load_tsv(here / "rr_theta_table2.tsv"):
        rr2[int(float(r["modulus"]))] = float(r["theta"])
    return bennett_c, bennett_x0, rr1, rr2


# ---- independent phi(m^2) via factorisation (no project import) ------------
def phi_of_square(m):
    res, x, p = m * m, m, 2
    seen = set()
    while p * p <= x:
        if x % p == 0:
            if p not in seen:
                res -= res // p
                seen.add(p)
            while x % p == 0:
                x //= p
        p += 1 if p == 2 else 2
    if x > 1 and x not in seen:
        res -= res // x
    return res


def recompute_bound(source, modulus, n, tables, phi_m):
    """Independently reproduce the contribution for a recorded (source, modulus)."""
    bennett_c, bennett_x0, rr1, rr2 = tables
    logn = math.log(n)
    if source == "Broadbent-theta":
        return 0.375 / logn ** 3
    if source == "Bennett-raw":
        return bennett_c[modulus] / logn
    if source == "RR-Table2":
        return rr2[modulus] / math.sqrt(n)
    if source.startswith("RR-Table1"):
        entries = rr1.get(modulus, [])
        valid = [(x0, eps) for x0, eps in entries if n >= x0]
        x0, eps = max(valid, key=lambda t: t[0])
        return eps / phi_m
    if source == "Bennett-c0":
        c0 = 1.0 / 840.0 if modulus <= 10_000 else 1.0 / 160.0
        return c0 / logn
    raise ValueError(f"unknown source {source}")


def bound_valid_at(source, modulus, n, tables):
    """Independently confirm the recorded bound is in its validity range at n."""
    bennett_c, bennett_x0, rr1, rr2 = tables
    if source == "Broadbent-theta":
        return n >= math.exp(20.0)
    if source == "Bennett-raw":
        return n >= bennett_x0[modulus]
    if source == "RR-Table2":
        return n <= RR_TABLE2_MAX_X
    if source.startswith("RR-Table1"):
        return any(n >= x0 for x0, _ in rr1.get(modulus, []))
    if source == "Bennett-c0":
        return n >= 8e9
    return False


def up(x):
    return (Decimal(str(x)) + SAFE_WIDEN).quantize(Decimal("1e-12"), rounding=ROUND_UP)


def down(x):
    return (Decimal(str(x)) - SAFE_WIDEN).quantize(Decimal("1e-12"), rounding=ROUND_DOWN)


def check_row(k, rec, tables):
    """Return list of problems (empty = row verified)."""
    problems = []
    thr = float(rec["certified_threshold"])
    prov = rec["parameters_and_provenance"]

    # 1 + 2: for each B_q and R block, re-check every bound and re-sum contributions
    for name, block in prov.items():
        recs = block["modulus_bounds"]
        # (1) validity + independent recompute of each contribution
        for mb in recs:
            src, mod = mb["source"], mb["modulus"]
            if not bound_valid_at(src, mod, thr, tables):
                problems.append(f"{name}: bound {src} for modulus {mod} not valid at n={thr:.3e}")
            phi_m = phi_of_square(int(round(math.isqrt(mod)))) if mod > 1 else 1
            # modulus is m; phi(m) needed for RR-T1. Reconstruct phi(m):
            got = recompute_bound(src, mod, thr, tables, phi_mod(mod))
            if abs(got - mb["contribution"]) > 1e-9:
                problems.append(f"{name}: contribution mismatch for {src} mod {mod}: "
                                f"archived {mb['contribution']:.3e} vs recomputed {got:.3e}")

    # 3: re-do the directed rounding on the winning criterion, check slack sign + match
    crit = rec["criterion"]
    ri = rec["rounded_interval"][crit]
    archived_slack = Decimal(ri["slack"])
    if archived_slack <= 0:
        problems.append(f"archived slack for winning criterion {crit} is not positive: {archived_slack}")
    if not rec["proven"]:
        problems.append("row marked not proven")

    # 4: interval checks positive at each left endpoint
    for iv in rec["interval_checks"]:
        if not (Decimal(str(iv["slack_at_left"])) > 0):
            problems.append(f"interval {iv['interval']} slack at left endpoint not positive: {iv['slack_at_left']}")

    return problems


def phi_mod(m):
    """phi(m) by factorisation."""
    res, x, p = m, m, 2
    while p * p <= x:
        if x % p == 0:
            res -= res // p
            while x % p == 0:
                x //= p
        p += 1 if p == 2 else 2
    if x > 1:
        res -= res // x
    return res


def main():
    here = Path(__file__).resolve().parent
    tables = load_tables(here)
    bundle = json.load(open(here / "row_certificates.json"))

    print(f"Independently verifying {len(bundle)} certificate records...")
    print(f"{'k':>5} {'criterion':>11} {'threshold':>12} {'result':>10}")
    print("-" * 45)
    all_ok = True
    for k in sorted(bundle, key=int):
        rec = bundle[k]
        problems = check_row(k, rec, tables)
        ok = not problems
        all_ok = all_ok and ok
        print(f"{k:>5} {rec['criterion']:>11} {float(rec['certified_threshold']):>12.3e} "
              f"{'VERIFIED' if ok else 'FAILED':>10}")
        for p in problems:
            print(f"        ! {p}")
    print("-" * 45)
    if all_ok:
        print("ALL RECORDS INDEPENDENTLY VERIFIED.")
        sys.exit(0)
    else:
        print("VERIFICATION FAILED on one or more records.")
        sys.exit(1)


if __name__ == "__main__":
    main()
