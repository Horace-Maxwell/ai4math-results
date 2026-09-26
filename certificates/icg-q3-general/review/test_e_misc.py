"""(e) Misc exact checks:
 1. Lemma 3: four cases of h, the bound, and its hypothesis (P>0 vs P>=mu).
 2. Theorem 5 internal identities on random Y (exact): column path formula, telescoping,
    p f_k = Lambda(ybar_k, zeta_k), stepwise f_k <= c_k D_b (strict unless ybar_k = +-s_b).
 3. Remark (ii): stepwise bound at p=3.   4. Remark (i): inertia of Delta_b(3) +- T_b(3).
 5. Lemma 4 constants at q=3 (min of P*beta over the admissible box)."""
import random, itertools
from fractions import Fraction as Fr
import numpy as np
from rv_core import T_gen, d_formula, zpath, mu_c, svec, matvec, matmul, transpose, l1, l1mat, delta_diag

random.seed(99)
fails = []


def h(A, B, P, mu):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)


# 1. Lemma 3
rr = lambda lo, hi: Fr(random.randint(int(lo * 1000), int(hi * 1000)), 1000)
for _ in range(20000):
    P, mu = rr(0.01, 10), rr(0, 1)
    A, B = rr(-3, 3), rr(-30, 30)
    Aa, Bb = (A, B) if A >= 0 else (-A, -B)
    if 0 <= Bb <= Aa: want = -2 * (P - mu) * Bb
    elif Bb > Aa: want = 2 * (mu * Bb - P * Aa)
    elif -P * Aa <= Bb < 0: want = Fr(0)
    else: want = 2 * mu * (abs(Bb) - P * Aa)
    if h(A, B, P, mu) != want or h(A, B, P, mu) != h(-A, -B, P, mu):
        fails.append(('h cases', P, mu, A, B))
    bound_ok = h(A, B, P, mu) <= 2 * mu * max(Fr(0), abs(B) - P * abs(A))
    if P >= mu and not bound_ok:
        fails.append(('lemma3 with P>=mu', P, mu, A, B))
ce = (Fr(1, 2), Fr(1), Fr(1), Fr(1, 10))
print('Lemma 3 as stated (P>0, 0<=mu<=1): counterexample P=1/2, mu=1, A=1, B=1/10: h=%s, bound=%s'
      % (h(ce[2], ce[3], ce[0], ce[1]), 2 * ce[1] * max(Fr(0), abs(ce[3]) - ce[0] * abs(ce[2]))))

# 2. Theorem 5 internal identities
def thm5_pieces(p, q, a, b, Y):
    M, N = T_gen(a, p), T_gen(b, q)
    F = lambda w: l1(matvec(N, w))
    Db = d_formula(b, q)
    rows = [list(map(Fr, r)) for r in Y]
    zeta = zpath(rows, p)  # vector-valued path
    mu, c = mu_c(a, p)
    lhs = l1mat(matmul(matmul(M, [list(r) for r in Y]), transpose(N)))
    path = p ** a * (F(zeta[-1]) + sum(F([u - v for u, v in zip(zeta[k - 1], zeta[k])]) for k in range(a)))
    fk = [F([u - v for u, v in zip(zeta[k - 1], zeta[k])]) + mu[k - 1] * F(zeta[k - 1]) - mu[k] * F(zeta[k])
          for k in range(a)]
    tele = p ** a * (sum(fk) + mu[a - 1] * F(rows[a]))
    P_, lam = p - 1, []
    for k in range(a):
        yk, zk, m_ = rows[k], zeta[k], mu[k - 1]
        L = P_ * F([u - v for u, v in zip(yk, zk)]) + m_ * F([v + P_ * u for u, v in zip(yk, zk)]) - (P_ - m_) * F(zk)
        lam.append(L)
    return lhs, path, tele, fk, lam, c, Db, rows, mu


cnt = 0
for (p, q) in [(Fr(5), Fr(3)), (Fr(7), Fr(3)), (Fr(11, 2), Fr(3)), (Fr(5), Fr(4)), (Fr(6), Fr(13, 4))]:
    for a in range(1, 7):
        for b in range(1, 7):
            for _ in range(15):
                Y = [[random.choice([1, -1]) for _ in range(b + 1)] for _ in range(a + 1)]
                if random.random() < 0.3:  # rows mostly +-s_b to probe equality structure
                    Y = [[g * s for s in svec(b)] for g in [random.choice([1, -1]) for _ in range(a + 1)]]
                lhs, path, tele, fk, lam, c, Db, rows, mu = thm5_pieces(p, q, a, b, Y)
                if lhs != path: fails.append(('path', p, q, a, b))
                if lhs != tele: fails.append(('tele', p, q, a, b))
                for k in range(a):
                    if p * fk[k] != lam[k]: fails.append(('p f_k = Lambda', p, q, a, b, k))
                    alt = rows[k] in (list(map(Fr, svec(b))), [Fr(-e) for e in svec(b)])
                    if fk[k] > c[k] * Db or (not alt and fk[k] >= c[k] * Db):
                        fails.append(('stepwise', p, q, a, b, k))
                    if not (Fr(3, 5) <= mu[k - 1] <= 1): fails.append(('mu range', p, a, k))
                if lhs > d_formula(a, p) * Db: fails.append(('thm5', p, q, a, b))
                cnt += 1
print('Theorem 5 internal identities + stepwise bound: %d random Y, a,b in 1..6, (p,q) in {(5,3),(7,3),(11/2,3),(5,4),(6,13/4)}' % cnt)

# 3. Remark (ii): stepwise bound at p = 3
viol = 0
for a in (1, 2):
    for b in (1, 2, 3):
        for signs in itertools.product([1, -1], repeat=(a + 1) * (b + 1)):
            Y = [list(signs[i * (b + 1):(i + 1) * (b + 1)]) for i in range(a + 1)]
            lhs, path, tele, fk, lam, c, Db, rows, mu = thm5_pieces(Fr(3), Fr(3), a, b, Y)
            if any(fk[k] > c[k] * Db for k in range(a)):
                viol += 1
                if viol == 1:
                    ex = (a, b, Y, [str(fk[k] - c[k] * Db) for k in range(a)])
print('Remark (ii): #sign matrices with some f_k > c_k D_b at p=q=3 (a<=2,b<=3): %d; first: a=%d b=%d Y=%s excess=%s'
      % ((viol,) + ex if viol else (0, 0, 0, None, None)))

# 4. Remark (i): inertia of Delta_b(3) +- T_b(3), b odd
for b in (1, 3, 5, 7, 9):
    T = np.array([[float(v) for v in r] for r in T_gen(b, 3)])
    Dg = np.diag([float(v) for v in delta_diag(b, 3)])
    ep, em = np.linalg.eigvalsh(Dg + T), np.linalg.eigvalsh(Dg - T)
    print('Remark (i): b=%d  Delta+T eig min/max %.4f/%.4f   Delta-T eig min/max %.4f/%.4f'
          % (b, ep.min(), ep.max(), em.min(), em.max()))

# 5. Lemma 4 constants at q=3: min over x in[1/3,1], mu in[3/5,1], muq in [1/3,1] of P*beta, P=4
best = min(4 * (m * Fr(2, 3) * (1 - x) + (1 + m) * mq * x)
           for x in (Fr(1, 3), Fr(1)) for m in (Fr(3, 5), Fr(1)) for mq in (Fr(1, 3), Fr(1)))
print('Lemma 4 q=3: min P*beta = %s (claimed >= 16/9); max mu|B_j| = %s' % (best, Fr(4, 3)))
# actual range of muq_j for q=3, j>=0
muq, _ = mu_c(12, 3)
print('mu^q_j (q=3), j=0..11 range: [%s, %s]' % (min(muq[j] for j in range(12)), max(muq[j] for j in range(12))))

print('FAILURES:', len(fails), fails[:5])
