# Exact confirmation (sympy) of candidates: factor F(x) = det(x(x^2-1)(xI-C) - diag(p_k(x^2-1)+q_k x^2))
# and the full characteristic polynomial p_G = x^(P-b) (x^2-1)^(Q-b) F.
import sympy as sp, sys
x = sp.symbols('x')
def charpoly_G(pq):
    b = len(pq); M = sp.zeros(b, b)
    for k,(p,q) in enumerate(pq):
        M[k,k] = x**2*(x**2-1) - p*(x**2-1) - q*x**2
        M[k,(k+1)%b] += -x*(x**2-1); M[k,(k-1)%b] += -x*(x**2-1)
    F = sp.expand(M.det(method='berkowitz'))
    P = sum(p for p,q in pq); Q = sum(q for p,q in pq)
    pG = sp.cancel(F * x**(P-b) * (x**2-1)**(Q-b))
    return sp.factor(pG)
for s in sys.argv[1:]:
    pq = [tuple(map(int, t.split(','))) for t in s.split(';')]
    print(s, '->', charpoly_G(pq))
