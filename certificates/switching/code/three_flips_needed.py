# Exact check (Python integers, Bareiss rank over Q) that the 13-vertex tree below has NO good
# switching with at most 2 switched vertices (up to complementation), but has one with 3.
import itertools, os, sys, sympy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import charpoly, exact_rank, krylov_rows
E=[(0,5),(0,9),(0,12),(1,0),(1,2),(2,3),(3,4),(5,6),(5,8),(6,7),(9,10),(9,11)]
n=13; adj=[[] for _ in range(n)]
for a,b in E: adj[a].append(b); adj[b].append(a)
phi=charpoly(adj,n); x=sympy.Symbol('x')
P=sympy.Poly(list(reversed(phi)),x,domain='ZZ'); g=sympy.gcd(P,P.diff(x)); d=n-g.degree()
print('charpoly factors:', sympy.factor_list(P.as_expr()))
print('d =', d)
def good(U):
    s=[-1 if i in U else 1 for i in range(n)]
    return exact_rank(krylov_rows(adj,s,d))==d
bad_le2=[U for k in range(3) for U in itertools.combinations(range(n),k) if good(U)]
print('good switchings with |U|<=2:', bad_le2)
g3=[U for U in itertools.combinations(range(n),3) if good(U)]
print('number of good 3-sets:', len(g3), 'e.g.', g3[:5])
