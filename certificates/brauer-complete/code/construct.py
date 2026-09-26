"""Explicit complete mappings of principal factors of B_n and PB_n
(implementation 1; uses diagrams.py for the Rees coordinates).

Rees coordinates of the rank-r J-class: x <-> (U(x), g(x), L(x)) in H x S_r x H,
product (i,a,lam)(j,b,mu) = (i, a*P[lam,j]*b, mu) if P[lam,j] defined, else 0.
P[lam,lam] = identity for every half-diagram lam (reflexive, identity diagonal).

Constructions (see PROOF.md, Section 4):
  (A) S_r has a complete mapping phi (r <= 1 or r >= 4):
        f(i,g,lam) = (lam, phi(g), L(i,lam)),          L a Latin square on H.
  (B) r in {2,3}, N = |H| even, t: H -> {0,1} with t(delta mu) = 1 - t(mu)
      for a fixed-point-free involution delta of H:   (quotient level, C_2)
        f(i, 1+t(L(i,lam)), lam) = (lam, 1, L(i,lam))
        f(i,   t(L(i,lam)), lam) = (lam, 0, delta(L(i,lam)))
  (C) r in {2,3}, N odd: rho a permutation of H with P[lam, rho lam] defined,
      no fixed points, and on every rho-cycle B: |B| + #{odd P[lam,rho lam]} even;
      c: H -> {0,1} with c(rho lam) = c(lam) + 1 + sgnbit(P[lam, rho lam]):
        f(i,   c(lam), lam) = (lam,     1 + c(lam),   L(i,lam))
        f(i, 1+c(lam), lam) = (rho lam, c(rho lam),   L(i,rho lam))
  For S_3 the quotient map (i,u,lam) -> (j,v,mu) is lifted through A_3
  (Theorem 5.2 'going up' of arXiv:2608.25092 with the identity complete
  mapping of A_3):  g = g_u h (g_0 = id, g_1 = (0 1), h in A_3),
        f(i,g,lam) = (j, p^{-1} h p g_v, mu),   p = P[lam, j].
"""
import random, math, sys, json
from itertools import permutations
from diagrams import *

ID = lambda r: tuple(range(r))


def sgnbit(p):
    return 0 if sign(p) == 1 else 1


# ------------------------------------------------ complete mappings of S_r
def group_cm(r, seed=0, p_up=0.02):
    """complete mapping phi of (S_r, compose): g -> compose(g, phi(g)) bijective.
    Targeted local search: repeatedly give a duplicated product x*alpha(x) a
    missing value z by swapping alpha-values (always accepted if the number of
    collisions does not increase, otherwise with probability p_up)."""
    G = list(permutations(range(r)))
    m = len(G)
    if m == 1:
        return {G[0]: G[0]}
    idx = {g: k for k, g in enumerate(G)}
    inv = [idx[inverse(g)] for g in G]
    rnd = random.Random(seed)
    alpha = list(range(m))
    rnd.shuffle(alpha)
    ainv = [0] * m
    for x, a in enumerate(alpha):
        ainv[a] = x
    prod = lambda x, y: idx[compose(G[x], G[y])]
    theta = [prod(x, alpha[x]) for x in range(m)]
    cnt = [0] * m
    for z in theta:
        cnt[z] += 1
    bad = sum(c - 1 for c in cnt if c > 1)
    it = 0
    while bad > 0:
        it += 1
        x = rnd.randrange(m)
        while cnt[theta[x]] < 2:
            x = rnd.randrange(m)
        z = rnd.randrange(m)
        while cnt[z] != 0:
            z = rnd.randrange(m)
        target = prod(inv[x], z)            # alpha(x) := x^{-1} z  gives theta(x) = z
        y = ainv[target]
        if y == x:
            continue
        ox, oy = theta[x], theta[y]
        ny = prod(y, alpha[x])
        keys = {ox, oy, z, ny}
        b0 = sum(max(0, cnt[k] - 1) for k in keys)
        cnt[ox] -= 1; cnt[oy] -= 1; cnt[z] += 1; cnt[ny] += 1
        b1 = sum(max(0, cnt[k] - 1) for k in keys)
        if b1 <= b0 or rnd.random() < p_up:
            ax, ay = alpha[x], alpha[y]
            alpha[x], alpha[y] = ay, ax
            ainv[ay], ainv[ax] = x, y
            theta[x], theta[y] = z, ny
            bad += b1 - b0
        else:
            cnt[ox] += 1; cnt[oy] += 1; cnt[z] -= 1; cnt[ny] -= 1
        if it > 20_000_000:
            raise RuntimeError("no convergence")
    phi = {G[x]: G[alpha[x]] for x in range(m)}
    assert len(set(phi.values())) == m
    assert len({compose(g, phi[g]) for g in G}) == m
    return phi


# ------------------------------------------------ quotient-level maps (C_2)
def quotient_map_even(H, P):
    N = len(H)
    assert N % 2 == 0
    idx = {h: k for k, h in enumerate(H)}
    L = lambda i, lam: H[(idx[i] + idx[lam]) % N]
    delta = {H[k]: H[k ^ 1] for k in range(N)}          # fixed-point-free involution
    t = {H[k]: k & 1 for k in range(N)}                  # t(delta mu) = 1 - t(mu)
    fbar = {}
    for i in H:
        for lam in H:
            mu = L(i, lam)
            fbar[(i, 1 ^ t[mu], lam)] = (lam, 1, mu)
            fbar[(i, t[mu], lam)] = (lam, 0, delta[mu])
    return fbar


def quotient_map_odd(H, P, rho):
    N = len(H)
    idx = {h: k for k, h in enumerate(H)}
    L = lambda i, lam: H[(idx[i] + idx[lam]) % N]
    # solve c(rho lam) = c(lam) + 1 + sgnbit(P[lam, rho lam]) on each cycle
    c = {}
    for start in H:
        if start in c:
            continue
        c[start] = 0
        lam = start
        while True:
            nxt = rho[lam]
            p = P[(lam, nxt)]
            assert p is not None and nxt != lam
            val = c[lam] ^ 1 ^ sgnbit(p)
            if nxt in c:
                assert c[nxt] == val, "cycle parity condition violated"
                break
            c[nxt] = val
            lam = nxt
    fbar = {}
    for i in H:
        for lam in H:
            fbar[(i, c[lam], lam)] = (lam, 1 ^ c[lam], L(i, lam))
            fbar[(i, 1 ^ c[lam], lam)] = (rho[lam], c[rho[lam]], L(i, rho[lam]))
    return fbar, c


def lift(H, P, r, fbar):
    """lift a complete mapping of the C_2-quotient to S_r, r in {2,3}."""
    G = list(permutations(range(r)))
    g1 = tuple([1, 0] + list(range(2, r)))       # the transposition (0 1)
    reps = {0: ID(r), 1: g1}
    f = {}
    for i in H:
        for lam in H:
            for g in G:
                u = sgnbit(g)
                h = compose(inverse(reps[u]), g)            # g = g_u * h (first g_u then h)
                assert sgnbit(h) == 0
                j, v, mu = fbar[(i, u, lam)]
                p = P[(lam, j)]
                assert p is not None
                img = compose(compose(compose(inverse(p), h), p), reps[v])
                f[(i, g, lam)] = (j, img, mu)
    return f


def brandt_level(H, P, r, phi):
    N = len(H)
    idx = {h: k for k, h in enumerate(H)}
    f = {}
    for i in H:
        for lam in H:
            mu = H[(idx[i] + idx[lam]) % N]
            for g in permutations(range(r)):
                f[(i, g, lam)] = (lam, phi[g], mu)
    return f


# ------------------------------------------------ rho for the odd case
def rho_generic(H, P):
    """negative triangle found by search + maximum matching of the rest."""
    import networkx as nx
    r = len(free_points(H[0]))
    adj = {a: [b for b in H if b != a and P[(a, b)] is not None] for a in H}
    tri = None
    for a in H:
        for b in adj[a]:
            for c in adj[b]:
                if c != a and P[(c, a)] is not None:
                    if (sgnbit(P[(a, b)]) + sgnbit(P[(b, c)]) + sgnbit(P[(c, a)])) % 2 == 1:
                        tri = (a, b, c)
                        break
            if tri: break
        if tri: break
    assert tri is not None, "no negative triangle"
    return tri


def rho_from_triangle_and_matching(H, P, tri, matching):
    rho = {}
    a, b, c = tri
    rho[a], rho[b], rho[c] = b, c, a
    for x, y in matching:
        assert x not in rho and y not in rho
        rho[x], rho[y] = y, x
    assert len(rho) == len(H)
    return rho


def max_matching_rest(H, P, exclude):
    import networkx as nx
    Gr = nx.Graph()
    rest = [h for h in H if h not in exclude]
    Gr.add_nodes_from(rest)
    for a in rest:
        for b in rest:
            if repr(a) < repr(b):
                if P[(a, b)] is not None:
                    Gr.add_edge(a, b)
    M = nx.max_weight_matching(Gr, maxcardinality=True)
    return [tuple(e) for e in M]


# ------------------------------------------------ the proof's explicit choices (Brauer)
def brauer_half(n, free, arcs):
    h = [None] * n
    for f_ in free:
        h[f_] = 'F'
    for a, b in arcs:
        h[a] = b; h[b] = a
    assert None not in h
    return tuple(h)


def proof_triangle(n, r):
    """I_0, I_1, I_2 of PROOF.md Lemma 4.3 (0-based points: point k <-> k+1)."""
    if r == 2:
        extra_free = []
        rest = list(range(4, n))
    else:
        extra_free = [4]
        rest = list(range(5, n))
    rest_arcs = [(rest[2 * t], rest[2 * t + 1]) for t in range(len(rest) // 2)]
    I0 = brauer_half(n, [2, 3] + extra_free, [(0, 1)] + rest_arcs)
    I1 = brauer_half(n, [1, 3] + extra_free, [(0, 2)] + rest_arcs)
    I2 = brauer_half(n, [1, 2] + extra_free, [(0, 3)] + rest_arcs)
    return (I0, I1, I2)


def proof_matching(n, r, H, P, tri):
    """perfect matching of G - X following PROOF.md Lemma 4.4:
    fibres (free sets) F0,F1,F2 of the triangle pair internally; the other
    fibres are paired (F,F') and joined by one explicit edge (v,w)."""
    from itertools import combinations
    fib = {}
    for h in H:
        fib.setdefault(tuple(free_points(h)), []).append(h)
    X = set(tri)
    tri_f = [tuple(free_points(h)) for h in tri]
    others = [F for F in sorted(fib) if F not in tri_f]
    # pair the other fibres greedily into joinable pairs (|F ^ F'| = 2k, r+2k <= n)
    def joinable(F, Fp):
        k = len(set(F) - set(Fp))
        return r + 2 * k <= n
    import networkx as nx
    FG = nx.Graph()
    FG.add_nodes_from(others)
    for F, Fp in combinations(others, 2):
        if joinable(F, Fp):
            FG.add_edge(F, Fp)
    FM = nx.max_weight_matching(FG, maxcardinality=True)
    assert 2 * len(FM) == len(others), "fibre pairing failed"
    used = set()
    pairs = []
    for F, Fp in FM:
        xs = sorted(set(F) - set(Fp)); ys = sorted(set(Fp) - set(F))
        outside = [p for p in range(n) if p not in set(F) | set(Fp)]
        k = len(xs)
        zs = outside[:k]; W = outside[k:]
        R0 = [(W[2 * t], W[2 * t + 1]) for t in range(len(W) // 2)]
        v = brauer_half(n, list(F), [(zs[t], ys[t]) for t in range(k)] + R0)
        w = brauer_half(n, list(Fp), [(xs[t], zs[t]) for t in range(k)] + R0)
        assert P[(v, w)] is not None and v not in X and w not in X
        pairs.append((v, w)); used |= {v, w}
    for F, members in fib.items():
        rest = [h for h in members if h not in used and h not in X]
        assert len(rest) % 2 == 0
        for t in range(0, len(rest), 2):
            a, b = rest[t], rest[t + 1]
            assert P[(a, b)] is not None
            pairs.append((a, b))
    return pairs


# ------------------------------------------------ assemble a factor CM
def factor_cm(S_elements, n, r, family, phis, mode="proof"):
    J = [x for x in S_elements if rank(x) == r]
    H = halves(S_elements, r)
    N = len(H)
    P = sandwich(H)
    info = {"n": n, "r": r, "family": family, "N": N}
    if r <= 1 or r >= 4:
        f = brandt_level(H, P, r, phis[r])
        info["construction"] = "A (Brandt level, CM of S_r)"
    elif N % 2 == 0:
        fbar = quotient_map_even(H, P)
        f = lift(H, P, r, fbar)
        info["construction"] = "B (Brandt level, N even)"
    else:
        if family == "B" and mode == "proof":
            tri = proof_triangle(n, r)
            match = proof_matching(n, r, H, P, tri)
            info["construction"] = "C (odd N; proof triangle + proof matching)"
        else:
            tri = rho_generic(H, P)
            match = max_matching_rest(H, P, set(tri))
            info["construction"] = "C (odd N; searched triangle + max matching)"
        s = [sgnbit(P[(tri[0], tri[1])]), sgnbit(P[(tri[1], tri[2])]), sgnbit(P[(tri[2], tri[0])])]
        info["triangle"] = [str(t) for t in tri]
        info["triangle_sign_bits"] = s
        assert sum(s) % 2 == 1
        if 2 * len(match) != N - 3:
            raise RuntimeError(f"no perfect matching of G-X: {2*len(match)} vs {N-3}")
        rho = rho_from_triangle_and_matching(H, P, tri, match)
        fbar, c = quotient_map_odd(H, P, rho)
        f = lift(H, P, r, fbar)
    # convert to diagrams and self-check (implementation 1)
    alpha = {}
    for (i, g, lam), (j, h, mu) in f.items():
        alpha[assemble(i, g, lam)] = assemble(j, h, mu)
    assert set(alpha) == set(J) and set(alpha.values()) == set(J)
    thetas = set()
    for x, y in alpha.items():
        z = product(x, y)
        assert rank(z) == r
        thetas.add(z)
    assert len(thetas) == len(J)
    return alpha, info


def encode(x):
    n = len(x) // 2
    name = lambda p: str(p + 1) if p < n else str(p - n + 1) + "'"
    blocks = []
    for p in range(2 * n):
        q = x[p]
        if q == -1:
            blocks.append(name(p))
        elif q > p:
            blocks.append(name(p) + ":" + name(q))
    return " ".join(blocks)


def group_phis(max_r):
    phis = {}
    for r in range(0, max_r + 1):
        if r in (2, 3):
            continue
        phis[r] = group_cm(r, seed=r)
    return phis


if __name__ == "__main__":
    import time, hashlib, os
    family, n = sys.argv[1], int(sys.argv[2])
    what = sys.argv[3] if len(sys.argv) > 3 else "all"      # 'all' or a rank
    mode = sys.argv[4] if len(sys.argv) > 4 else "proof"
    outdir = sys.argv[5] if len(sys.argv) > 5 else "../certificates"
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()
    S = brauer_elements(n) if family == "B" else partial_brauer_elements(n)
    ranks = sorted({rank(x) for x in S})
    if what != "all":
        ranks = [int(what)]
    need = [r for r in ranks if r not in (2, 3)]
    phis = {}
    for r in need:
        jp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "certificates", f"cm_S{r}.json")
        if r >= 4 and os.path.exists(jp):
            phis[r] = {tuple(a): tuple(b) for a, b in json.load(open(jp))}
            G = list(phis[r])
            assert len(set(phis[r].values())) == len(G) == math.factorial(r)
            assert len({compose(g, phis[r][g]) for g in G}) == len(G)
        else:
            phis[r] = group_cm(r, seed=1000 + r)
    alpha = {}
    infos = []
    for r in ranks:
        if r == n or (family == "PB" and False):
            pass
        H = halves(S, r)
        if r in (2, 3) and len(H) % 2 == 1 and len(H) > 1 and family == "PB":
            # the only odd PB case is (n,r) = (3,2): identity pattern, no CM
            raise SystemExit(f"PB_{n} rank {r}: N={len(H)} odd -> no complete mapping (Theorem t:converse0)")
        a, info = factor_cm(S, n, r, family, phis, mode)
        alpha.update(a)
        infos.append(info)
        print(json.dumps(info), flush=True)
    tag = f"{family}{n}_" + ("all" if what == "all" else f"rank{what}")
    path = os.path.join(outdir, f"cm_{tag}.txt")
    with open(path, "w") as fh:
        fh.write(f"# complete mapping certificate: {family}_{n} {'whole monoid' if what=='all' else 'principal factor of rank '+what}\n")
        fh.write("# format: x TAB alpha(x); blocks 'a:b' (a,b in 1..n, 1'..n'); singletons listed alone\n")
        for x in sorted(alpha, key=encode):
            fh.write(encode(x) + "\t" + encode(alpha[x]) + "\n")
    h = hashlib.sha256(open(path, "rb").read()).hexdigest()
    print(f"wrote {path} ({len(alpha)} lines) sha256={h} time={time.time()-t0:.1f}s")
