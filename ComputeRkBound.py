#!/usr/bin/env python3
"""
ComputeRkBound.py
=================
Explicit lower bound for R_k(n), k odd square-free, (n,k)=1, n >= 8e9, via the
generalised Theorem 5.6 of the thesis (divisor-sum form for any omega(k)):

  R_k(n)/n  >  C_Artin * prod_{q|k} lambda_q  -  (I) - (II) - (III),

  lambda_q = q(q-2)/(q^2-q-1),   and with c>=1, Z>c integers, A in (0,1/2):

  (I)   = (1/log n) sum_{a<=c,(a,k)=1} mu^2(a) sum_{j|k} c_theta(j a^2)
          [the j=a=1 modulus-1 term uses Broadbent: 0.375/(log n)^3]
  (II)  = ( prod_{q|k} (q-2)/(q-1) + 2/(1-2A) )
          ( sum_{c<a<=Z,(a,k)=1} mu^2(a)/phi(a^2) + 4/Z )
  (III) = ( k n^{-2A} + sqrt(k) n^{-A} ) log n.

Constants (same as the thesis):
  Bennett et al. (Thm 4.1):  c_theta(m) <= 1/840 (3<=m<=1e4), <= 1/160 (1e4<m<=1e5),
                             valid for n >= x0 = 8e9 on this modulus range.
  Broadbent et al. (Thm 4.2): |theta(n)-n| <= 0.375 n/(log n)^3.

Companion to ComputeBqBound.py. Self-contained; pure Python 3, no dependencies.

Usage:
    python3 ComputeRkBound.py                 # k = 15 (validation), 105, 429
    python3 ComputeRkBound.py --k 33
    python3 ComputeRkBound.py --k 105 --n 2.55e11
    python3 ComputeRkBound.py --k 429 --threshold   # least n with R_k>0
"""
import argparse, math

ZMAX = 200_000
C_ARTIN = 0.37395581361920228805

# ---- sieves: smallest prime factor, mobius, totient ----
_spf = list(range(ZMAX + 1))
for i in range(2, int(ZMAX ** 0.5) + 1):
    if _spf[i] == i:
        for j in range(i * i, ZMAX + 1, i):
            if _spf[j] == j:
                _spf[j] = i

def _factor(a):
    f = {}
    while a > 1:
        p = _spf[a]; e = 0
        while a % p == 0:
            a //= p; e += 1
        f[p] = e
    return f

MU = [0] * (ZMAX + 1); PHI = [0] * (ZMAX + 1); MU[1] = PHI[1] = 1
for a in range(2, ZMAX + 1):
    f = _factor(a)
    MU[a] = (-1) ** len(f) if all(e == 1 for e in f.values()) else 0
    ph = a
    for p in f:
        ph = ph // p * (p - 1)
    PHI[a] = ph

def phi2(a):                     # phi(a^2) = a*phi(a)
    return a * PHI[a]

def primefactors(k):
    return sorted(_factor(k).keys())

def divisors(k):
    ds = [1]
    for p, e in _factor(k).items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return sorted(ds)

def is_odd_squarefree(k):
    f = _factor(k)
    return k % 2 == 1 and all(e == 1 for e in f.values())

def c_theta(m):
    """Bennett Thm 4.1 (simplified). None => outside the explicit range."""
    if m == 1:
        return None
    if m <= 10 ** 4:
        return 1.0 / 840
    if m <= 10 ** 5:
        return 1.0 / 160
    return None


def Rk_lower(k, n, c, Z, A, suf):
    """Lower bound for R_k(n)/n. Returns None if a needed modulus exceeds 1e5."""
    logn = math.log(n); qs = primefactors(k); ds = divisors(k)
    G = C_ARTIN
    for q in qs:
        G *= (q * (q - 2)) / (q * q - q - 1)
    I = 0.0
    for a in range(1, c + 1):
        if not (MU[a] and math.gcd(a, k) == 1):
            continue
        for j in ds:
            m = j * a * a
            if m == 1:
                I += 0.375 / logn ** 3
            else:
                ct = c_theta(m)
                if ct is None:
                    return None
                I += ct / logn
    coef = 1.0
    for q in qs:
        coef *= (q - 2) / (q - 1)
    II = (coef + 2.0 / (1 - 2 * A)) * (suf[c + 1] + 4.0 / Z)
    III = (k * math.exp(-2 * A * logn) + math.sqrt(k) * math.exp(-A * logn)) * logn
    return G - I - II - III


def _suffix(k):
    suf = [0.0] * (ZMAX + 2)
    for a in range(ZMAX, 0, -1):
        suf[a] = suf[a + 1] + ((1.0 / phi2(a)) if (MU[a] and math.gcd(a, k) == 1) else 0.0)
    return suf


def best_bound(k, n):
    """Optimise over c (so all j a^2 <= 1e5) and A; return (value, c, A, G)."""
    if not is_odd_squarefree(k):
        raise SystemExit(f"k={k} must be odd and square-free")
    cmax = int(math.isqrt(10 ** 5 // k)); suf = _suffix(k)
    G = C_ARTIN
    for q in primefactors(k):
        G *= (q * (q - 2)) / (q * q - q - 1)
    best = (-9.0, None, None)
    for c in range(4, cmax + 1):
        for Ai in range(1, 49):
            v = Rk_lower(k, n, c, 2 * 10 ** 5, Ai / 100, suf)
            if v is not None and v > best[0]:
                best = (v, c, Ai / 100)
    return best[0], best[1], best[2], G


def threshold(k):
    lo, hi = 8e9, 1e16
    if best_bound(k, lo)[0] > 0:
        return lo
    if best_bound(k, hi)[0] <= 0:
        return None
    while hi / lo > 1.0005:
        mid = math.sqrt(lo * hi)
        if best_bound(k, mid)[0] > 0:
            hi = mid
        else:
            lo = mid
    return hi


def report(k, n):
    v, c, A, G = best_bound(k, n)
    qs = primefactors(k)
    lam = "".join(f" λ_{q}" for q in qs)
    print(f"k = {k} = {'*'.join(map(str, qs))}   at n = {n:.3e}")
    print(f"  main term  C_Artin{lam} = {G:.5f}")
    print(f"  R_{k}(n)/n  >=  {v:.5f}   (c={c}, A={A};  error = {G - v:.5f})"
          f"   {'>0' if v > 0 else '<=0'}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Explicit lower bound for R_k(n)")
    ap.add_argument("--k", type=int, help="odd square-free k")
    ap.add_argument("--n", type=float, default=8e9, help="evaluation point (default 8e9)")
    ap.add_argument("--threshold", action="store_true",
                    help="report least n with R_k(n) > 0 (moduli <= 1e5)")
    args = ap.parse_args()

    if args.k:
        report(args.k, args.n)
        if args.threshold:
            t = threshold(args.k)
            if t:
                print(f"  => R_{args.k}(n) > 0 for n >= {t:.3e}"
                      f"  (log10 {math.log10(t):.2f}); inside 2e12 computation: {t < 2e12}")
            else:
                print(f"  => not provable below 1e16 with moduli <= 1e5")
    else:
        print("Validation + exceptional values (Bennett+Broadbent constants):\n")
        for kk in (15, 105, 429):
            report(kk, 8e9)
        print("\n(For k=15 the thesis obtains 0.09527 with sharper raw c_theta data;")
        print(" 0.08805 here uses the simplified Theorem 4.1 constants.)")
