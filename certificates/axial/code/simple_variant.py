# E4'(eta, mu, gamma): 3C(eta) on (a,b,x); c^2=c, ca=cb=0, cx = mu(x-a-b) + gamma c.
import sys
from fractions import Fraction as Q
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from axial_tools import *
from variants import union_law

def E4p(eta, mu, gamma):
    n = 4
    T = [[None]*n for _ in range(n)]
    def setp(i, j, w): T[i][j] = w; T[j][i] = w
    h = Q(eta)/2
    setp(0,0,vec(n,{0:1})); setp(1,1,vec(n,{1:1})); setp(2,2,vec(n,{2:1})); setp(3,3,vec(n,{3:1}))
    setp(0,1,vec(n,{0:h,1:h,2:-h})); setp(0,2,vec(n,{0:h,2:h,1:-h})); setp(1,2,vec(n,{1:h,2:h,0:-h}))
    setp(3,0,vec(n,{})); setp(3,1,vec(n,{}))
    setp(3,2,vec(n,{2:mu,0:-mu,1:-mu,3:gamma}))
    return Alg(T, ['a','b','x','c'])

def analyse(eta, mu, gamma, F):
    A = E4p(eta, mu, gamma)
    a, b, x, c = A.basis()
    print(f"==== eta={eta} mu={mu} gamma={gamma}")
    info, law = union_law(A, {'a': a, 'b': b, 'c': c}, F)
    for nm, v in info.items(): print("  ", nm, v)
    print("   law:", law)
    print("   dims I_a, I_b, I_c:", len(ideal_generated(A,[a])), len(ideal_generated(A,[b])), len(ideal_generated(A,[c])))
    forms = frobenius_forms(A)
    for G in forms:
        print("   Frobenius form:", [[str(t) for t in r] for r in G])
    return A

if __name__ == "__main__":
    eta = Q(1,3)
    gs = 1 + eta*(1-eta)/2
    for mu, gamma in [(eta, gs), (eta, Q(1)), (Q(1,2), gs), (eta, Q(1,2))]:
        analyse(eta, mu, gamma, [Q(1), Q(0), eta, Q(mu)])
