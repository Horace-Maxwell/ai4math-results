from fractions import Fraction as F
from check_proof import T, d_delta, G_of
for b in [2,4,6]:
    for q in [F(5),F(7),F(11)]:
        p=F(3); db,delb=d_delta(b,q); d2,del2=d_delta(2,p); Th=d2*db-2*del2*delb
        g2=[1,1,-1]; Y=[[F(g2[i]*(-1)**j) for j in range(b+1)] for i in range(3)]
        print('vertical b=%d q=%s: Theta-G=%s  2(d_b-5delta_b)=%s'%(b,q,Th-G_of(Y,p,q,b),2*(db-5*delb)))
for p in [F(5),F(7),F(101)]:
    q=F(3); b=2; db,delb=d_delta(b,q); d2,del2=d_delta(2,p); Th=d2*db-2*del2*delb
    y=[1,1,-1]; s2=[1,-1,1]; Y=[[F(s2[i]*y[j]) for j in range(3)] for i in range(3)]
    print('horizontal p=%s: Theta-G=%s 4(p-3)=%s'%(p,Th-G_of(Y,p,q,b),4*(p-3)))
