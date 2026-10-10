#!/usr/bin/env python3
"""pred647.py — Erdős #647 sweep predicate for scripts/solve.sh.

Searches for a WITNESS n > 24 with  max_{m<n} (m + tau(m)) <= n + 2  (tau = number of divisors).
Erdős called such an n "extremely doubtful"; a witness would be the (£25) prize object, an empty
result is honest evidence of none in [a,b) — NEVER a proof (that is the Certify.Sup bridge's job).

Contract (solve.sh sweep): CLI `--a A --b B [--jobs N]`; prints ONE json object to stdout:
    {"witnesses": [n, ...], "checked": INT, "notes": {...}}

Method: numpy global divisor-count sieve up to b, prefix-max of f(m)=m+tau(m), then the
window test. Memory is O(b) int64 (~8 B/n) → keep b <= ~2e7 for this simple version; the numba /
segmented sweep (the full solve.sh backend) is what reaches 1e9. `--jobs` is accepted but unused here.
"""
import argparse, json, sys
try:
    import numpy as np
except ImportError:
    sys.exit("error: pred647.py needs numpy — install it: python3 -m pip install numpy")


def sweep(a: int, b: int):
    a0 = max(a, 25)                       # the problem asks n > 24
    if b <= a0:
        return {"witnesses": [], "checked": 0, "notes": {"note": f"empty range [{a0},{b})"}}
    tau = np.zeros(b, dtype=np.int64)
    for d in range(1, b):                 # tau[m] = #divisors of m
        tau[d::d] += 1
    f = np.arange(b, dtype=np.int64) + tau        # f(m) = m + tau(m)
    prefmax = np.maximum.accumulate(f)            # prefmax[k] = max_{m<=k} f(m)
    ns = np.arange(a0, b, dtype=np.int64)
    excess = prefmax[a0 - 1: b - 1] - (ns + 2)    # <= 0  ⇔  n is a witness
    witnesses = ns[excess <= 0].tolist()
    k = int(excess.argmin())
    return {
        "witnesses": witnesses,
        "checked": int(b - a0),
        "notes": {
            "min_excess": int(excess[k]),         # smallest (max_{m<n}(m+tau m)) - (n+2)
            "argmin_n": int(ns[k]),
            "method": "numpy global divisor sieve + prefix-max",
        },
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", type=int, required=True)
    ap.add_argument("--b", type=int, required=True)
    ap.add_argument("--jobs", type=int, default=1)   # accepted, unused (single-process numpy)
    args = ap.parse_args()
    json.dump(sweep(args.a, args.b), sys.stdout)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
