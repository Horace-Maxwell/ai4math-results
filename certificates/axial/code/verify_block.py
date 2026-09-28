# Problem 3.8 candidate (round 7, axial task): a decomposable axial block.
# D = span(a, b, x, c, d) over Q:  3C(eta) on (a,b,x);  c^2 = c, ca = cb = 0, cx = d, cd = eta d,
#   d^2 = 0, da = db = dx = 0.   X = {a, b, c}.
import sys
from fractions import Fraction as Q
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from axial_tools import *
from variants import union_law
from modp_ideals import modp_ideals
def D(eta, kappa=None, delta=0):
    if kappa is None: kappa = eta
    n = 5
    T = [[vec(n, {}) for _ in range(n)] for _ in range(n)]
    def setp(i, j, w): T[i][j] = w; T[j][i] = w
    h = Q(eta)/2
    setp(0,0,vec(n,{0:1})); setp(1,1,vec(n,{1:1})); setp(2,2,vec(n,{2:1})); setp(3,3,vec(n,{3:1}))
    setp(0,1,vec(n,{0:h,1:h,2:-h})); setp(0,2,vec(n,{0:h,2:h,1:-h})); setp(1,2,vec(n,{1:h,2:h,0:-h}))
    setp(3,2,vec(n,{4:1})); setp(3,4,vec(n,{4:kappa})); setp(4,4,vec(n,{4:delta}))
    return Alg(T, ['a','b','x','c','d'])
out = []
def rep(*s):
    line = " ".join(str(t) for t in s); print(line); out.append(line)
for eta in [Q(1,3), Q(1,2)]:
    A = D(eta); a,b,x,c,d = A.basis()
    rep(f"===== eta = {eta}")
    F = [Q(1), Q(0), eta]
    for nm, s in [('a',a),('b',b),('c',c)]:
        spaces, full = eigen_decomposition(A, s, F)
        one = spaces.get(Q(1), [])
        rep(f"axis {nm}: idempotent {A.mul(s,s)==s}, semisimple/spectrum in F {full}, primitive {len(one)==1 and in_span(s, one)},",
            {str(l): [A.show(v) for v in vs] for l, vs in spaces.items()})
    info, law = union_law(A, {'a':a,'b':b,'c':c}, F)
    rep("realised law:", law)
    rep("dim <<a,b,c>> =", len(subalgebra_generated(A,[a,b,c])), "of", A.n)
    Ia = ideal_generated(A,[a]); Ib = ideal_generated(A,[b]); Ic = ideal_generated(A,[c])
    rep("I_a:", [A.show(v) for v in Ia], "; I_b == I_a:", same_space(Ia, Ib), "; I_c:", [A.show(v) for v in Ic])
    # I_a as an algebra: J1 = span(a,b,x), J2 = span(d)
    J1 = [a, b, x]; J2 = [d]
    def ideal_of(sub, big):  # sub is an ideal of the algebra 'big' (both spans)
        return all(in_span(A.mul(u, v), sub) for u in sub for v in big)
    rep("I_a == span(a,b,x,d):", same_space(Ia, [a,b,x,d]))
    rep("J1=span(a,b,x) ideal of I_a:", ideal_of(J1, Ia), "; J2=span(d) ideal of I_a:", ideal_of(J2, Ia),
        "; J1 proper:", rank(J1) < rank(Ia), "; J2 proper:", rank(J2) < rank(Ia), "; J1+J2 = I_a:", same_space(J1+J2, Ia))
    rep("J1 is NOT an ideal of A (c*x = d):", not is_ideal(A, J1))
    rep("Delta edges:", [(p,q) for p,q in [('a','b'),('a','c'),('b','c')] if not is_zero(A.mul(dict(a=a,b=b,c=c)[p], dict(a=a,b=b,c=c)[q]))])
with open(__file__.rsplit('/', 2)[0] + '/logs/verify_block.out', 'w') as f:
    f.write("\n".join(out) + "\n")
