import json, sys, os
from verify_bitset import check
W=os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")  # certificate folder (code/ and data/ are siblings); was an absolute path before packaging
tab={int(k):v for k,v in json.load(open(W+"/data/rm714_all_witnesses.json")).items()}
N=16384
KTA=[0,128,192,224,240,248,252,254,256,272,288,296,304,308,312,314,316,318]
U={322,326,330,334,N-322,N-326,N-330,N-334}
claimed=set(KTA)|set(range(320,N-320+1,2))|{N-a for a in KTA}
bad=0
for w,L in sorted(tab.items()):
    wt,deg=check(w,L) if L else (0,0)
    if wt!=w or deg>7: bad+=1; print("FAIL",w,wt,deg)
print("witnesses:",len(tab),"failures:",bad)
print("claimed\\U covered:", (claimed-U)<=set(tab), " witnesses outside claimed:", sorted(set(tab)-claimed))
print("undecided without witness:", sorted(U-set(tab)))
