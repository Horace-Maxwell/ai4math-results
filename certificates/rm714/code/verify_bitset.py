"""Second, independent witness check (pure Python big integers, no numpy, no Moebius transform).
Truth table of f on F_2^14 is a 16384-bit integer T: bit x of T is f(x), where coordinate i of the
point x is bit i of x.  Variable x_i has table V[i] = sum of 2^x over x with bit i set.  A monomial s
has table AND_{i in s} V[i]; f = XOR of its monomials.  Weight = number of 1 bits of T."""
import sys, json
m = 14; N = 1 << m
V = [sum(1 << x for x in range(N) if (x >> i) & 1) for i in range(m)]
ALL = (1 << N) - 1
def table(mons):
    T = 0
    for s in mons:
        t = ALL
        for i in range(m):
            if (s >> i) & 1: t &= V[i]
        T ^= t
    return T
def check(w, mons):
    assert all(0 <= s < N for s in mons)
    assert len(set(mons)) == len(mons)
    deg = max(bin(s).count("1") for s in mons)
    wt = bin(table(mons)).count("1")
    return wt, deg
if __name__ == "__main__":
    d = json.load(open(sys.argv[1]))
    bad = 0
    for k in sorted(d, key=int):
        wt, deg = check(int(k), d[k])
        ok = (wt == int(k) and deg <= 7)
        bad += not ok
        print(k, wt, "maxdeg=%d" % deg, "k=%d" % len(d[k]), "OK" if ok else "FAIL")
    print("failures:", bad)
