"""Closed forms for the surplus s at a column with state B-vector eps*m*beta (FD1) or eps'*m*gamma (B-chain),
as functions of (P, Q, mu, m).  Checked against the direct cell computation at random rational points."""
import random
from fractions import Fraction as Fr

def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)

def vecs(P):
    p = P + 1
    alpha = {'A': (2*p*P, -2*P*P, P*P+1), 'B': (-2*p*P, -2*P, p*p-2), 'C': (0, -2*p*P, P*P-1), 'E': (0, 0, p*p)}
    Delta = {'A': 0, 'B': 2*(P-1)**2, 'C': 2*(P*P+1), 'E': 4*P*P}
    return alpha, Delta

def s_direct(P, Q, mu, m, t, sigma, ref='A', eps=1):
    """surplus for column sigma*alpha(t) at state eps*m*alpha(ref)."""
    q = Q + 1
    alpha, Delta = vecs(P)
    A = [sigma * x for x in alpha[t]]
    B = [eps * m * x for x in alpha[ref]]
    chat = Q * (1 + mu) / q
    return chat * Delta[t] - sum(hfun(Q, mu, A[i], B[i]) for i in range(3)) / q

def s_formula_FD1(P, Q, mu, m, dev):
    """closed forms (state eps*m*beta, beta = alpha(A)); dev in Asame,Bsame,Bopp,Csame,Copp,Esame,Eopp."""
    p = P + 1; q = Q + 1
    chat = Q * (1 + mu) / q; muJ = (Q - mu) / q
    D = 5*P*P + 2*P + 1
    if dev == 'Asame': return 2 * muJ * m * D
    if dev == 'Bsame':
        b1 = (4 * P / q) * min((Q - mu) * P * m, Q - mu * P * m)
        return 2*(P-1)**2 * chat + 2 * muJ * (P*P+1) * m + b1
    if dev == 'Bopp':
        return 2*(P-1)**2 * chat + 4 * muJ * p * P * m - (4 * mu * P / q) * max(0, P * m - Q)
    if dev == 'Csame':
        b2 = (2 / q) * min((Q - mu) * (P*P+1) * m, Q * (P*P-1) - mu * (P*P+1) * m)
        return 2*(P*P+1) * chat - (4 * mu / q) * p * P * m + 4 * muJ * P * P * m + b2
    if dev == 'Copp': return 2*(P*P+1) * chat - (4 * mu / q) * p * P * m
    if dev == 'Esame': return 4*P*P * chat - (4 * mu / q) * (p*P + P*P) * m + 2 * muJ * (P*P+1) * m
    if dev == 'Eopp': return 4*P*P * chat - (4 * mu / q) * (p*P + P*P) * m
    raise ValueError

def s_formula_chain(P, Q, mu, m, dev):
    """B-chain state eps'*m*gamma (gamma = alpha(B)); chain continuation is -eps' B.  Lower bounds / closed forms."""
    p = P + 1; q = Q + 1
    chat = Q * (1 + mu) / q; muJ = (Q - mu) / q
    if dev == 'Asame':   # exact
        return 4 * muJ * P * m + (2 / q) * min((Q - mu) * (p*p-2) * m, Q * (P*P+1) - mu * (p*p-2) * m)
    if dev == 'Aopp': return 4 * muJ * p * P * m
    if dev == 'Bsame': return 2*(P-1)**2 * chat + 2 * muJ * m * (3*p*p - 4)
    if dev == 'Csame':
        return 2*(P*P+1) * chat - (4 * mu / q) * p * P * m + 4 * muJ * P * m + (2 / q) * min((Q - mu) * (p*p-2) * m, Q * (P*P-1) - mu * (p*p-2) * m)
    if dev == 'Copp': return 2*(P*P+1) * chat - (4 * mu / q) * p * P * m
    if dev == 'Esame': return 4*P*P * chat - (4 * mu / q) * (p*P + P) * m + 2 * muJ * (p*p-2) * m
    if dev == 'Eopp': return 4*P*P * chat - (4 * mu / q) * (p*P + P) * m
    raise ValueError

DEV = {'Asame': ('A', 1), 'Bsame': ('B', 1), 'Bopp': ('B', -1), 'Csame': ('C', 1), 'Copp': ('C', -1), 'Esame': ('E', 1), 'Eopp': ('E', -1)}
CHAIN_DEV = {'Asame': ('A', 1), 'Aopp': ('A', -1), 'Bsame': ('B', 1), 'Csame': ('C', 1), 'Copp': ('C', -1), 'Esame': ('E', 1), 'Eopp': ('E', -1)}

if __name__ == "__main__":
    random.seed(1)
    n = 0
    for trial in range(4000):
        if trial % 2 == 0:
            P = Fr(random.randint(4, 60)) + Fr(random.randint(0, 9), 10); Q = Fr(2) + Fr(random.randint(0, 400), 10)
        else:
            P = Fr(2); Q = Fr(4) + Fr(random.randint(0, 400), 10)
        mu = Fr(random.randint(0, 1000), 1000); m = Fr(random.randint(0, 1000), 1000)
        for dev, (t, rel) in DEV.items():
            for eps in (1, -1):
                d = s_direct(P, Q, mu, m, t, rel * eps, 'A', eps)
                f = s_formula_FD1(P, Q, mu, m, dev)
                assert d == f, ('FD1', dev, P, Q, mu, m, d, f)
                n += 1
        for dev, (t, rel) in CHAIN_DEV.items():
            for eps in (1, -1):
                d = s_direct(P, Q, mu, m, t, rel * eps, 'B', eps)
                f = s_formula_chain(P, Q, mu, m, dev)
                assert d == f, ('chain', dev, P, Q, mu, m, d, f)
                n += 1
        # chain continuation -eps B costs exactly chat*Delta(B)
        for eps in (1, -1):
            d = s_direct(P, Q, mu, m, 'B', -eps, 'B', eps)
            assert d == Q * (1 + mu) / (Q + 1) * 2 * (P - 1) ** 2
        # anti-checkerboard continuation -eps A costs 0
        for eps in (1, -1):
            assert s_direct(P, Q, mu, m, 'A', -eps, 'A', eps) == 0
    print(f"all closed forms agree with direct cell computation: {n} checks (P>=4,Q>=2 and P=2,Q>=4; mu,m in [0,1])")
