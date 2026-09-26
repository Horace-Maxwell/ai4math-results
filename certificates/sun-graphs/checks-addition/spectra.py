import sympy as sp, math, itertools
x=sp.symbols('x')
def adj(b,p,q):
    n=b+sum(p)+2*sum(q); A=sp.zeros(n,n); nxt=b
    for k in range(b): A[k,(k+1)%b]=A[(k+1)%b,k]=1
    for k in range(b):
        for _ in range(p[k]): A[k,nxt]=A[nxt,k]=1; nxt+=1
        for _ in range(q[k]): A[k,nxt]=A[nxt,k]=1; A[nxt,nxt+1]=A[nxt+1,nxt]=1; nxt+=2
    return A
def charpoly_fast(b,p,q):
    # phi_G = x^(P-b) (x^2-1)^(Q-b) F(x), F = det(x(x^2-1)(xI-C) - diag(p(x^2-1)+q x^2))
    M=sp.zeros(b,b)
    for k in range(b):
        M[k,k]=x**2*(x**2-1)-p[k]*(x**2-1)-q[k]*x**2
        M[k,(k+1)%b]+= -x*(x**2-1); M[k,(k-1)%b]+= -x*(x**2-1)
    F=sp.expand(M.det(method='berkowitz'))
    P=sum(p);Q=sum(q)
    return sp.factor(sp.cancel(F*x**(P-b)*(x**2-1)**(Q-b)))
for name,(b,p,q) in {'C41(6,0,3,0)':(4,[6,0,3,0],[0]*4),
                     'C4(5P2,P1,2P2,P1)':(4,[0,1,0,1],[5,0,2,0]),
                     'C42(4,4,0,0)':(4,[0]*4,[4,4,0,0]),
                     'C61(0,6,6,12,6,6)':(6,[0,6,6,12,6,6],[0]*6),
                     'C42(10,10,0,0)':(4,[0]*4,[10,10,0,0])}.items():
    n=b+sum(p)+2*sum(q)
    f=charpoly_fast(b,p,q)
    print(name,'n=',n,f)
# direct check for the small ones
for (b,p,q) in [(4,[6,0,3,0],[0]*4),(4,[0,1,0,1],[5,0,2,0]),(4,[0]*4,[4,4,0,0])]:
    A=adj(b,p,q); print('direct', sp.factor(A.charpoly(x).as_expr()))
# N_{>1}(C_b)
for b in range(3,31):
    cnt=sum(1 for j in range(b) if 2*math.cos(2*math.pi*j/b)>1+1e-12)
    cntm=sum(1 for j in range(b) if 2*math.cos(2*math.pi*j/b)<-1-1e-12)
    print(b,cnt,2*math.ceil(b/6)-1,cntm)
