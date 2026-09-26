# Validate the exact multiplicity routine of sunsearch.c (test mode) against numpy eigenvalues
# of the full adjacency matrix, on random generalized sun graphs (P1/P2 mixed).
import numpy as np, random, subprocess, sys
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def adj(b,p,q):
    n=b+sum(p)+2*sum(q); A=np.zeros((n,n)); nxt=b
    for k in range(b):
        A[k,(k+1)%b]=A[(k+1)%b,k]=1
    for k in range(b):
        for _ in range(p[k]): A[k,nxt]=A[nxt,k]=1; nxt+=1
        for _ in range(q[k]): A[k,nxt]=A[nxt,k]=1; A[nxt,nxt+1]=A[nxt+1,nxt]=1; nxt+=2
    return A
cases=[]
for t in range(3000):
    b=random.randint(3,10)
    mode=random.random()
    p=[random.choice([0,0,1,2,3,4,6,8,12]) if mode<0.5 else random.randint(0,5) for _ in range(b)]
    q=[random.choice([0,0,0,1,2,3,5]) if random.random()<0.6 else 0 for _ in range(b)]
    if sum(p)+2*sum(q)+b>45: continue
    cases.append((b,p,q))
# add structured cases likely to have eigenvalue coincidences
cases += [(6,[0,6,6,12,6,6],[0]*6),(4,[6,0,3,0],[0]*4),(4,[0,16,32,16],[0]*4),(4,[0,1,0,1],[5,0,2,0]),(8,[1]*8,[0]*8),(6,[1,0,1,0,1,0],[0]*6),(10,[0]*10,[1,0]*5),(12,[2]*12,[0]*12)]
inp="".join("%d %s\n"%(b," ".join("%d %d"%(p[k],q[k]) for k in range(b))) for b,p,q in cases)
out=subprocess.run(["./sunsearch","test"],input=inp,capture_output=True,text=True).stdout.split("\n")
bad=0; nint=0
for (b,p,q),line in zip(cases,out):
    v=list(map(int,line.split())); n,tot,mm=v[0],v[1],v[2:]
    ev=np.linalg.eigvalsh(adj(b,p,q))
    num=[int(np.sum(np.abs(ev-m)<1e-6)) for m in range(-9,10)]
    if num!=mm or n!=len(ev): bad+=1; print("MISMATCH",b,p,q,mm,num)
    if tot==n: nint+=1
print("cases",len(cases),"mismatches",bad,"integral among them",nint)
