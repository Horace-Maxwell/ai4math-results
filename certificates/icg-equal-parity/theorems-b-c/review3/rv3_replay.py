"""Referee-3: replay of the proof of Proposition 31 on actual sign matrices, exact arithmetic, for a = 5..8.

For each (a, b, p, q, Y) (b = a mod 2, (p, q) in R1 or R2, rational points included) it checks:
  (i)   Lemma 21:  x^{1-b}(Theta - G(Y)) = sum_{j<b} psi_j + x rho (Delta(c_b) - 2 delta_a) + 2x ((M zeta_{-1})_a)^-,
        with G(Y) computed from the matrix model Z = T_a(p) Y T_b(q)^T;
  (ii)  psi_j >= 0 for all j, and psi_j > 0 when c_j != +-s_a;
  (iii) the case analysis of the proof: J = max{j : c_j != (-1)^{j+1} s_a};
        J < b : the state is zeta_J = (-1)^J mu_{b-2-J} s_a, (mu_{J-1}, mu_{b-2-J}) lies in the box of the family of F_a the
                proof assigns, its r satisfies r >= rho, and psi_J > 2 x delta_a rho;
        J = b : g = c_b; g = g_+ (then Theta - G >= 0, = 0 iff Y = Y^+), or Delta(g) > 2 delta_a, or the chain case: k as in the
                proof, y = mu_{b-2-k} in I_k (k <= 4, k < b), zeta_{b-1-k} = (-1)^k mu_{k-1} g, and (C1) holds at the true values;
                or k >= 5: y = mu_{b-6} in its interval and (C2) holds; or k = b: Delta(g) Dhat/rho > 2 delta_a;
  (iv)  Theta - G(Y) > 0 unless Y is Y^- or Y^+, where it is 0.
Sign matrices are drawn to hit every branch: uniform, first deviation from Y^- at a random J, chains of a random last column
of random length k, and perturbations of Y^+.
Usage: python3 rv3_replay.py N_per_a seed
"""
import itertools, random, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rv3_bnb import T, G_matrix, dk

N_PER = int(sys.argv[1]) if len(sys.argv) > 1 else 200
rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 4242)


def h(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)


def mv(M, v):
    return [sum(M[i][k] * v[k] for k in range(len(v))) for i in range(len(M))]


stats = {}
bad = []


def bump(k):
    stats[k] = stats.get(k, 0) + 1


t0 = time.time()
for a in (5, 6, 7, 8):
    sa = tuple((-1) ** i for i in range(a + 1))
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    gp = [((-1) ** a) * z for z in sa]
    gp[a] -= 2
    gplus = tuple(gp)
    for it in range(N_PER):
        b = rnd.choice([x for x in range(1, 14) if x % 2 == a % 2])
        if rnd.random() < 0.5:
            p, q = 5 + Fr(rnd.randint(0, 12), rnd.randint(1, 3)), 3 + Fr(rnd.randint(0, 12), rnd.randint(1, 3))
        else:
            p, q = Fr(3), 5 + Fr(rnd.randint(0, 12), rnd.randint(1, 3))
        x, P = q, q - 1
        M, N = T(a, p), T(b, q)
        Mc = {c: mv(M, c) for c in vecs}
        Da, dela = dk(a, p)
        Db, delb = dk(b, q)
        Theta = Da * Db - 2 * dela * delb
        Delta = {c: Da - sum(abs(z) for z in Mc[c]) for c in vecs}
        mu = {-1: Fr(1)}
        for j in range(b + 12):
            mu[j] = (P - mu[j - 1]) / x
        mu0, mu1, muinf = mu[0], mu[1], P / (x + 1)
        rho = mu[b - 1]
        anti_col = lambda j: tuple(((-1) ** (j + 1)) * z for z in sa)
        # ---- draw Y (columns c_0..c_b, c_b[a] = -1)
        mode = rnd.choice(['uniform', 'deviate', 'chain', 'plus'])
        cols = [rnd.choice(vecs) for _ in range(b + 1)]
        if mode == 'deviate':
            J = rnd.randint(0, b)
            for j in range(J + 1, b + 1):
                cols[j] = anti_col(j)
            if J < b:
                cols[J] = rnd.choice([c for c in vecs if c != anti_col(J)])
        elif mode == 'chain':
            cheapg = [c for c in vecs if c[a] == -1 and c != anti_col(b) and c != gplus and Delta[c] <= 2 * dela]
            g = rnd.choice(cheapg) if (cheapg and rnd.random() < 0.85) else rnd.choice([c for c in vecs if c[a] == -1])
            k = rnd.choice([rnd.randint(0, min(b, 5)), rnd.randint(0, b), b])
            cols[b] = g
            for i in range(1, k + 1):
                cols[b - i] = tuple(((-1) ** i) * z for z in g)
        elif mode == 'plus':
            cols = [tuple(((-1) ** j) * z for z in sa) for j in range(b)] + [gplus]
            if rnd.random() < 0.7:
                j = rnd.randint(0, b - 1) if b >= 1 else 0
                cols[j] = rnd.choice(vecs)
        if cols[b][a] != -1:
            cols[b] = tuple(list(cols[b][:a]) + [-1])
        Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
        G = G_matrix(Y, M, N)
        # ---- column path and psi_j
        zeta = {b - 1: [Fr(z) for z in cols[b]]}
        for j in range(b - 1, -1, -1):
            zeta[j - 1] = [(zeta[j][i] + P * cols[j][i]) / x for i in range(a + 1)]
        psi = {}
        for j in range(b):
            Mz = mv(M, zeta[j])
            psi[j] = P * (1 + mu[j - 1]) * Delta[cols[j]] - sum(h(P, mu[j - 1], Mc[cols[j]][i], Mz[i]) for i in range(a + 1))
            if psi[j] < 0 or (psi[j] == 0 and cols[j] not in (sa, tuple(-z for z in sa))):
                bad.append(('psi sign', a, b, p, q, j))
        kappa = 2 * x * max(Fr(0), -mv(M, zeta[-1])[a])
        lhs = (Theta - G) / x ** (b - 1)
        rhs = sum(psi.values()) + x * rho * (Delta[cols[b]] - 2 * dela) + kappa
        if lhs != rhs:
            bad.append(('Lemma 21', a, b, p, q))
        bump('lemma21')
        # ---- case analysis
        Ym = all(cols[j] == anti_col(j) for j in range(b + 1))
        Yp = all(cols[j] == tuple(((-1) ** j) * z for z in sa) for j in range(b)) and cols[b] == gplus
        if Ym or Yp:
            bump('extremal')
            if G != Theta:
                bad.append(('extremal G != Theta', a, b))
            continue
        J = max(j for j in range(b + 1) if cols[j] != anti_col(j))
        if J < b:
            bump('case J<b')
            muJ, mJ = mu[J - 1], mu[b - 2 - J]
            if zeta[J] != [((-1) ** J) * mJ * z for z in sa]:
                bad.append(('state zeta_J', a, b, J))
            # family assignment of the proof
            if a % 2 == 0:
                if J == 0:
                    fam, r = 'F1', (P - mJ) / x
                    inbox = muJ == 1 and mu0 <= mJ <= muinf
                elif J == b - 1:
                    fam, r = 'F2', (P - muJ) / x
                    inbox = mJ == 1 and mu0 <= muJ <= muinf
                elif J % 2 == 0:
                    fam, r = 'F3', muJ
                    inbox = muinf <= muJ <= mu1 and mu0 <= mJ <= muinf
                else:
                    fam, r = 'F4', mJ
                    inbox = mu0 <= muJ <= muinf and muinf <= mJ <= mu1
            else:
                if b == 1:
                    fam, r = 'F0', mu0
                    inbox = muJ == 1 and mJ == 1
                elif J == 0:
                    fam, r = 'F1', (P - mJ) / x
                    inbox = muJ == 1 and muinf <= mJ <= mu1
                elif J == b - 1:
                    fam, r = 'F2', (P - muJ) / x
                    inbox = mJ == 1 and muinf <= muJ <= mu1
                else:
                    fam, r = ('F3' if (J - 1) % 2 == 0 else 'F4'), muinf
                    inbox = (mu0 <= muJ <= muinf and mu0 <= mJ <= muinf) if (J - 1) % 2 == 0 else \
                        (muinf <= muJ <= mu1 and muinf <= mJ <= mu1)
            bump('fam ' + fam)
            if not inbox or r < rho:
                bad.append(('family box / r >= rho', a, b, J, fam))
            if not psi[J] > 2 * x * dela * rho:
                bad.append(('F_a at true values', a, b, J))
        else:
            g = cols[b]
            if g == gplus:
                bump('case g_+')
                if not Theta - G > 0:
                    bad.append(('g_+ but not strict and not Y+', a, b))
            elif Delta[g] > 2 * dela:
                bump('case expensive')
                if not Theta - G > 0:
                    bad.append(('expensive', a, b))
            else:
                gam = 2 * dela - Delta[g]
                k = 0
                while k < b and cols[b - k - 1] == tuple(((-1) ** (k + 1)) * z for z in g):
                    k += 1
                if k < b and k <= 4:
                    bump(f'case chain k={k}')
                    y = mu[b - 2 - k]
                    Ik = (mu0 <= y <= muinf) if k % 2 == a % 2 else (muinf <= y <= mu1 or y == 1)
                    if not Ik:
                        bad.append(('y not in I_k', a, b, k))
                    j = b - 1 - k
                    if zeta[j] != [((-1) ** k) * mu[k - 1] * z for z in g]:
                        bad.append(('chain state', a, b, k))
                    chain = sum(psi[b - i] for i in range(1, k + 1))
                    if chain != sum(P * (1 + mu[b - i - 1]) for i in range(1, k + 1)) * Delta[g]:
                        bad.append(('chain cost (Lemma 23)', a, b, k))
                    if not chain + psi[j] > x * rho * gam:
                        bad.append(('(C1) at true values', a, b, k))
                elif k < b:
                    bump('case chain k>=5')
                    y = mu[b - 6]
                    ok = (mu0 <= y <= muinf) if a % 2 == 0 else (muinf <= y <= mu1)
                    if not ok or not sum(P * (1 + mu[b - i - 1]) for i in range(1, 6)) * Delta[g] > x * rho * gam:
                        bad.append(('(C2) at true values', a, b, k))
                else:
                    bump('case full chain')
                    Dhat = Db / x ** b
                    if not Delta[g] * Dhat / rho > 2 * dela:
                        bad.append(('(C3) at true values', a, b))
        if not Theta - G > 0:
            bad.append(('Theta - G not > 0 for a non-extremal Y', a, b, p, q))
        bump('checked')
print(f'rv3_replay: {stats}')
print(f'problems: {len(bad)}  {bad[:10]}')
print(f'time {time.time() - t0:.0f}s')
