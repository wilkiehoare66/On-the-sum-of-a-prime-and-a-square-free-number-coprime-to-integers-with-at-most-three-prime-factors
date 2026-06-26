#!/usr/bin/env python3
"""
ComputeBqBound.py
=================
Explicit upper bound for the "divisible part"

        B_q(n) = sum_{p<n, q|(n-p)} mu^2(n-p) log p  =  R(n) - R_q(n),

and the combined criterion

        R_{q1 q2}(n) > log 2 + B_{q3}(n)   ==>   R_{q1 q2 q3}(n) > 0,

used to resolve the three-prime values k = q1 q2 q3 (in particular k = 429 and
k = 105) WITHOUT any prime-counting data beyond moduli 10^5.  Companion to
ComputeRkBound.py; same constants:

  * Bennett et al. (Thm 4.1):  |theta(n;m,n) - n/phi(m)| < c_theta(m) n/log n,
        c_theta(m) <= 1/840  (3 <= m <= 1e4),  <= 1/160  (1e4 < m <= 1e5),
        valid for n >= x0 = 8e9 on this modulus range.
  * Broadbent et al. (Thm 4.2): |theta(n) - n| <= 0.375 n/(log n)^3.

Term-by-term, with (n,q)=1, n >= 8e9, integers c>=1, Z>c, A in (0,1/2):

  B_q(n)/n  <  (1/q) * prod_{p ! qn} (1 - 1/(p(p-1)))            [main, = M_B]
               + (I)_B + (II)_B + (III)_B,

  (I)_B   = (1/log n) [ sum_{a<=c,(a,q)=1} mu^2(a) c_theta(q a^2)
                        + sum_{b<=c/q,(b,q)=1} mu^2(b) c_theta(q^2 b^2) ]
  (II)_B  = (1/(q-1)) (1 + 2 f_BT) (T + 4/Z)
            + (1/(q(q-1))) (1 + 2 f_BT) (T_b + 4q/Z)            [q|a family]
            with  f_BT = log n / ((1-2A) log n - log q),
                  T   = sum_{c<a<=Z,(a,q)=1} mu^2(a)/phi(a^2),
                  T_b = sum_{c/q<b<=Z,(b,q)=1} mu^2(b)/phi(b^2).
  (III)_B = ( (1+1/q) n^{-A}/q + (1+1/q) n^{-1/2} + n^{A-1} ) log n
            [ trivial range n^A<a<=sqrt(n) for both families, plus (a,n)>1 ].

The f_BT factor is the sharp form of the Brun-Titchmarsh denominator
log(n/(q a^2)) >= (1-2A) log n - log q  (since a <= n^A => q a^2 <= q n^{2A}),
replacing the looser 1/(1-2A) used in the first draft.

Usage:
    python3 ComputeBqBound.py --k 429            # combined criterion for k
    python3 ComputeBqBound.py --bq 13            # just the B_13 upper bound
    python3 ComputeBqBound.py --k 429 --n 1.24e10
"""
import argparse, math

# --------------------------------------------------------------------------
# arithmetic sieves
# --------------------------------------------------------------------------
ZMAX = 200_000
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

def phi2(a):          # phi(a^2) = a * phi(a)
    return a * PHI[a]

def primefactors(k):
    return sorted(_factor(k).keys())

def divisors(k):
    ds = [1]
    for p, e in _factor(k).items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return sorted(ds)

C_ARTIN = 0.37395581361920228805

def c_theta(m):
    """Bennett Thm 4.1 (simplified). Returns None if outside the explicit range."""
    if m == 1:
        return None                       # handled by Broadbent (Thm 4.2)
    if m <= 10 ** 4:
        return 1.0 / 840
    if m <= 10 ** 5:
        return 1.0 / 160
    return None                           # modulus too large: no data at x0=8e9


# --------------------------------------------------------------------------
# suffix tails  T(c) = sum_{a>c, (a,K)=1} mu^2(a)/phi(a^2)   (built per K)
# --------------------------------------------------------------------------
def suffix_tail(K):
    suf = [0.0] * (ZMAX + 2)
    for a in range(ZMAX, 0, -1):
        add = (1.0 / phi2(a)) if (MU[a] and math.gcd(a, K) == 1) else 0.0
        suf[a] = suf[a + 1] + add
    return suf


# --------------------------------------------------------------------------
# B_q(n) upper bound (single prime q)
# --------------------------------------------------------------------------
def Bq_upper(q, n, c, Z, A, suf=None):
    """Return dict with main M_B and the three error terms; bound = M_B + I+II+III.
       M_B is expressed PER (1/n) over prod_{p ! qn}; here returned as the
       coefficient (1/q) so callers can multiply by the actual Euler product."""
    logn = math.log(n)
    if suf is None:
        suf = suffix_tail(q)
    # ---- (I)_B : PNTAP over a<=c, two families ----
    I = 0.0; maxmod = 0; ok = True
    for a in range(1, c + 1):
        if MU[a] and math.gcd(a, q) == 1:           # modulus q a^2
            m = q * a * a; maxmod = max(maxmod, m)
            ct = c_theta(m)
            if ct is None: ok = False; break
            I += ct / logn
    for b in range(1, c // q + 1):                  # modulus q^2 b^2  (a=qb<=c)
        if MU[b] and math.gcd(b, q) == 1:
            m = q * q * b * b; maxmod = max(maxmod, m)
            ct = c_theta(m)
            if ct is None: ok = False
            else: I += ct / logn
    # ---- (II)_B : main-comparison tail + sharp Brun-Titchmarsh ----
    denom = (1 - 2 * A) * logn - math.log(q)
    f_BT = logn / denom if denom > 0 else float('inf')
    T   = suf[c + 1] + 4.0 / Z
    cb  = c // q
    T_b = (suf[cb + 1] if cb + 1 <= ZMAX else 0.0) + 4.0 * q / Z
    II = (1.0 / (q - 1)) * (1 + 2 * f_BT) * T \
       + (1.0 / (q * (q - 1))) * (1 + 2 * f_BT) * T_b
    # ---- (III)_B : trivial range n^A<a<=sqrt(n) (both families) + (a,n)>1 ----
    III = ((1 + 1.0 / q) * math.exp(-A * logn) / q
           + (1 + 1.0 / q) * math.exp(-0.5 * logn)
           + math.exp((A - 1) * logn)) * logn
    return dict(main_coeff=1.0 / q, I=I, II=II, III=III,
                err=I + II + III, maxmod=maxmod, ok=ok, c=c, A=A, f_BT=f_BT)


# --------------------------------------------------------------------------
# R_m(n) lower bound  (generalised Thm 5.6 / ComputeRkBound logic, m squarefree)
# --------------------------------------------------------------------------
def Rm_lower(m, n, c, Z, A, suf=None):
    logn = math.log(n); qs = primefactors(m); ds = divisors(m)
    if suf is None:
        suf = suffix_tail(m)
    G = C_ARTIN
    for q in qs: G *= (q * (q - 2)) / (q * q - q - 1)     # worst-case main coeff
    I = 0.0; ok = True; maxmod = 0
    for a in range(1, c + 1):
        if not (MU[a] and math.gcd(a, m) == 1): continue
        for j in ds:
            mm = j * a * a; maxmod = max(maxmod, mm)
            if mm == 1:
                I += 0.375 / logn ** 3
            else:
                ct = c_theta(mm)
                if ct is None: ok = False
                else: I += ct / logn
    coef = 1.0
    for q in qs: coef *= (q - 2) / (q - 1)
    II = (coef + 2.0 / (1 - 2 * A)) * (suf[c + 1] + 4.0 / Z)
    III = (m * math.exp(-2 * A * logn) + math.sqrt(m) * math.exp(-A * logn)) * logn
    return dict(G=G, I=I, II=II, III=III, val=G - I - II - III, ok=ok,
                maxmod=maxmod, c=c, A=A)


# --------------------------------------------------------------------------
# optimisation helpers
# --------------------------------------------------------------------------
def best_Rm(m, n):
    cmax = int(math.isqrt(10 ** 5 // m)); suf = suffix_tail(m)
    best = None
    for c in range(4, cmax + 1):
        for Ai in range(1, 49):
            r = Rm_lower(m, n, c, 2 * 10 ** 5, Ai / 100, suf)
            if r['ok'] and (best is None or r['val'] > best['val']): best = r
    return best

def best_Bq(q, n):
    cmax = int(math.isqrt(10 ** 5 // q)); suf = suffix_tail(q)
    best = None
    for c in range(4, cmax + 1):
        for Ai in range(1, 49):
            b = Bq_upper(q, n, c, 2 * 10 ** 5, Ai / 100, suf)
            if b['ok'] and (best is None or b['err'] < best['err']): best = b
    return best


# --------------------------------------------------------------------------
# common-Euler-product main-difference coefficient for R_{q1q2} - B_{q3}
#   R_{q1q2} main = prod_i (q_i-2)/(q_i-1) * prod_{p ! q1q2 n}
#   B_{q3}   main = (1/q3)                * prod_{p ! q3 n}
#   express both over W = prod_{p ! k n} (k=q1q2q3), W >= C_ARTIN
# --------------------------------------------------------------------------
def margin_coeff(q1, q2, q3):
    fR = ((q1 - 2) / (q1 - 1)) * ((q2 - 2) / (q2 - 1))
    fR *= (1 - 1.0 / (q3 * (q3 - 1)))          # restore p=q3 factor: prod_{!q1q2 n}=W*(...)
    fB = (1.0 / q3)
    fB *= (1 - 1.0 / (q1 * (q1 - 1))) * (1 - 1.0 / (q2 * (q2 - 1)))  # restore p=q1,q2
    return fR - fB


# --------------------------------------------------------------------------
# combined criterion for k = q1 q2 q3
# --------------------------------------------------------------------------
def criterion(k, n, verbose=True):
    qs = primefactors(k)
    if len(qs) != 3 or any(_factor(k)[q] > 1 for q in qs):
        raise SystemExit(f"k={k} must be a squarefree product of three odd primes")
    q1, q2, q3 = qs                       # q1<q2<q3 ; subtract the largest
    m = q1 * q2
    R = best_Rm(m, n); B = best_Bq(q3, n)
    coef = margin_coeff(q1, q2, q3); margin = coef * C_ARTIN
    E = (R['G'] - R['val']) + B['err']    # E_m + E_Bq
    slack = margin - E                    # >0  ==>  R_k(n) > 0 proven
    if verbose:
        print(f"  k = {k} = {q1}*{q2}*{q3}    base m = {m}, subtract B_{q3}    n = {n:.3e}")
        print(f"  R_{m}(n)/n  >=  G - (I+II+III) = {R['G']:.5f} - {R['G']-R['val']:.5f}"
              f"  = {R['val']:.5f}    [c={R['c']}, A={R['A']}, maxmod={R['maxmod']}]")
        print(f"    E_{m}  = {R['G']-R['val']:.5f}")
        print(f"  B_{q3}(n)/n <=  M_B + (I_B+II_B+III_B);  error terms:")
        print(f"    (I)_B  = {B['I']:.5f}   (II)_B = {B['II']:.5f}   (III)_B = {B['III']:.5f}"
              f"   [c={B['c']}, A={B['A']}, maxmod={B['maxmod']}, f_BT={B['f_BT']:.3f}]")
        print(f"    E_B{q3} = {B['err']:.5f}")
        print(f"  main-difference coeff (over W>=C_Artin) = {coef:.5f}")
        print(f"  margin = coeff * C_Artin = {margin:.5f}")
        print(f"  E_{m} + E_B{q3}          = {E:.5f}")
        print(f"  SLACK = margin - errors  = {slack:+.5f}   ->  "
              f"{'R_%d(n) > 0  PROVEN' % k if slack > 0 else 'not yet (raise n)'}")
    return slack

def threshold(k):
    lo, hi = 8e9, 1e13
    if criterion(k, lo, verbose=False) > 0:
        return lo
    if criterion(k, hi, verbose=False) <= 0:
        return None
    while hi / lo > 1.0005:
        mid = math.sqrt(lo * hi)
        if criterion(k, mid, verbose=False) > 0: hi = mid
        else: lo = mid
    return hi


# --------------------------------------------------------------------------
if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Explicit B_q bound and R_{q1q2}-B_{q3} criterion")
    ap.add_argument("--k", type=int, help="three-prime squarefree k (e.g. 429, 105)")
    ap.add_argument("--bq", type=int, help="just print the B_q upper-bound error for prime q")
    ap.add_argument("--n", type=float, default=8e9, help="evaluation point (default 8e9)")
    args = ap.parse_args()

    if args.bq:
        b = best_Bq(args.bq, args.n)
        print(f"B_{args.bq} upper bound at n={args.n:.3e}:")
        print(f"  main coeff 1/{args.bq} = {b['main_coeff']:.5f}  (x prod_p!qn)")
        print(f"  (I)_B={b['I']:.5f}  (II)_B={b['II']:.5f}  (III)_B={b['III']:.5f}"
              f"  => E_B{args.bq}={b['err']:.5f}   [c={b['c']}, A={b['A']}, maxmod={b['maxmod']}]")
    if args.k:
        criterion(args.k, args.n)
        t = threshold(args.k)
        if t:
            print(f"  => R_{args.k}(n) > 0 for all n >= {t:.3e}  (log10 {math.log10(t):.2f});"
                  f"  inside 2e12 computation: {t < 2e12}")
        else:
            print(f"  => not provable below 1e13 with moduli<=1e5; needs extended data")
    if not args.k and not args.bq:
        print("examples:")
        for kk in (429, 105):
            criterion(kk, 8e9); t = threshold(kk)
            print(f"  => threshold {t:.3e}\n")
