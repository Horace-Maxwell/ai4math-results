"""Referee-2, test 4.  End-to-end bookkeeping of CH_a (chains for cheap last columns) and of the full-chain bounds, on actual
sign matrices, exact arithmetic.  For a in {3,4}, sample (p,q) in both regions, b up to BMAX, every cheap last column g
(g_a = -1, g != anti column, Delta(g) < 2 delta_a at this p), every k = number of chain steps (0..b-1) and every deviation c:
build Y = [random prefix | c at J' = b-1-k | chain (-1)^{b-j} g for J' < j < b | g at column b] and check, against the true
column path of Y:
  (a) state zeta_{J'} = (-1)^k mu_{k-1} g exactly;  (b) chain columns have s_j = chat_j Delta(g) exactly;
  (c) sum of chain s_j == sum_{n=1..k} Q(1 + it(y,n))/q * Delta(g) with y = mu_{b-2-k} (the prover's parametrisation);
  (d) rho == it(y, k+1);  (e) the potential at J' equals y;  (f) y lies in the parity range claimed ([mu0,L) for even index,
      (L,mu1] for odd index) or y = 1 iff b = k+1;  (g) Proposition 1 total and Theta - G > 0.
  For k >= K+1 = 5: chain-alone sum over the last K+1 chain columns == formula with y = mu_{b-2-K} and exceeds
  (2 delta_a - Delta(g)) rho.  Full chain: Delta(g) Dhat_b > 2 delta_a rho_b and the ratio bounds
  Dhat_b/rho_b >= Dhat_1/mu_1 + 2 (b even), = Dhat_1/mu_0 (b = 1), >= Dhat_2/L + 2 (b odd >= 3), b <= 60.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from r2core import T, mus, matvec, l1, svec, dd, de, G, Theta, colpath, h, d_closed, delta_closed

random.seed(99)
BMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
K = 4
out = open('logs/t4_chain_bookkeeping.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

# full-chain ratio bounds
for q in (Fr(3), Fr(5), Fr(7), Fr(7, 2), Fr(101), Fr(1001)):
    Q = q - 1; mu = mus(80, q)
    mu0 = (Q - 1) / q; mu1 = (Q * Q + 1) / q ** 2; L = Q / (q + 1)
    D1 = d_closed(1, q) / q; D2 = d_closed(2, q) / q ** 2
    for b in range(1, 61):
        Db = d_closed(b, q) / q ** b; rb = delta_closed(b, q) / q ** b
        assert rb == mu[b - 1]
        if b % 2 == 0: assert Db / rb >= D1 / mu1 + 2
        elif b == 1: assert Db / rb == D1 / mu0
        else: assert Db / rb >= D2 / L + 2
log("full-chain ratio bounds Dhat_b/rho_b hold for b <= 60 at q in {3,5,7,7/2,101,1001}: OK")

params = [(Fr(5), Fr(3)), (Fr(7), Fr(3)), (Fr(3), Fr(5)), (Fr(3), Fr(7)), (Fr(11, 2), Fr(7, 2)), (Fr(3), Fr(21, 4)),
          (Fr(101), Fr(3)), (Fr(3), Fr(101))]
stat = {}
for a in (3, 4):
    sa = svec(a)
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    for (p, q) in params:
        Q = q - 1
        M = T(a, p); Da = dd(a, p); da = de(a, p)
        mu0 = (Q - 1) / q; mu1 = (Q * Q + 1) / q ** 2; L = Q / (q + 1)
        def it(y, n):
            for _ in range(n): y = (Q - y) / q
            return y
        cheap = [g for g in vecs if g[a] == -1 and list(g) != [-(-1) ** a * x for x in sa]
                 and Da - l1(matvec(M, list(g))) < 2 * da]
        worst_alone = None
        for b in [bb for bb in range(1, BMAX + 1) if (a + bb) % 2 == 0]:
            N = T(b, q); mu = mus(b + 2, q); rho = mu[b - 1]; th = Theta(a, b, p, q)
            for g in cheap:
                Dg = Da - l1(matvec(M, list(g)))
                extra = (2 * da - Dg) * rho
                for k in range(0, b):
                    Jp = b - 1 - k
                    eps = (-1) ** k
                    cont = [-eps * x for x in g]
                    devs = [c for c in vecs if list(c) != cont]
                    for c in random.sample(devs, 4) + [None]:     # None = continue the chain (tests full chain / longer k)
                        cols = [None] * (b + 1)
                        cols[b] = list(g)
                        for j in range(Jp + 1, b):
                            cols[j] = [(-1) ** (b - j) * x for x in g]
                        cols[Jp] = list(c) if c is not None else cont
                        for j in range(Jp):
                            cols[j] = list(random.choice(vecs))
                        z = colpath(cols, q)
                        s = [Q * (1 + mu[j - 1]) / q * (Da - l1(matvec(M, cols[j])))
                             - sum(h(Q, mu[j - 1], matvec(M, cols[j])[i], matvec(M, z[j])[i]) for i in range(a + 1)) / q
                             for j in range(b)]
                        Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
                        kappa = 2 * max(Fr(0), -matvec(M, z[-1])[a])
                        gap = (th - G(Y, M, N)) / q ** b
                        assert gap == sum(s) + rho * Dg + kappa - 2 * da * rho                                 # (g) identity
                        assert gap > 0                                                                          # (g)
                        if c is None: continue
                        assert z[Jp] == [eps * mu[k - 1] * x for x in g]                                        # (a)
                        for j in range(Jp + 1, b):
                            assert s[j] == Q * (1 + mu[j - 1]) / q * Dg                                         # (b)
                        y = mu[b - 2 - k]
                        assert mu[Jp - 1] == y                                                                  # (e)
                        chain_f = sum(Q * (1 + it(y, n)) / q for n in range(1, k + 1)) * Dg
                        assert chain_f == sum(s[Jp + 1:b])                                                      # (c)
                        assert it(y, k + 1) == rho                                                              # (d)
                        idx = b - 2 - k
                        if idx == -1: assert y == 1
                        elif idx % 2 == 0: assert mu0 <= y < L                                                  # (f)
                        else: assert L < y <= mu1
                        if k <= K:
                            assert s[Jp] + chain_f > extra                                                      # need
                            stat['dev'] = stat.get('dev', 0) + 1
                        else:
                            yK = mu[b - 2 - K]
                            alone = sum(Q * (1 + it(yK, n)) / q for n in range(0, K + 1)) * Dg
                            assert alone == sum(s[b - 1 - K:b])
                            assert alone > extra
                            r = alone / extra
                            worst_alone = r if worst_alone is None or r < worst_alone else worst_alone
                            stat['alone'] = stat.get('alone', 0) + 1
                # full chain
                cols = [[(-1) ** (b - j) * x for x in g] for j in range(b + 1)]
                Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
                Dhat = d_closed(b, q) / q ** b
                assert Dg * Dhat > 2 * da * rho
                assert th - G(Y, M, N) > 0
                stat['full'] = stat.get('full', 0) + 1
        log(f"a={a} p={p} q={q}: cheap={cheap} b<={BMAX}: bookkeeping (a)-(g) OK; chain-alone min ratio "
            f"{'n/a' if worst_alone is None else f'{float(worst_alone):.3f}'}")
log(f"counts {stat}")
