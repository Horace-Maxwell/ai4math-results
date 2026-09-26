# Exact small-case check of Hak-Kozerenko-Oliynyk (DAM 309 (2022) 278-284, arXiv:2103.10806) open problems 1-3.
# Q3': every triametral triple contains a peripheral vertex.  Q4: every diametral pair extends to a triametral triple.
# P1: Q3' for median graphs? P2: Q4 for median graphs? P3: for DH graphs, Q3' or Q4 holds (per graph)?
import itertools, networkx as nx, random, sys, time
def dist(G):
    return dict(nx.all_pairs_shortest_path_length(G))
def props(G):
    d=dist(G); V=list(G.nodes())
    ecc={v:max(d[v].values()) for v in V}; diam=max(ecc.values())
    per={v for v in V if ecc[v]==diam}
    tr=0; tri=[]
    for a,b,c in itertools.combinations(V,3):
        s=d[a][b]+d[a][c]+d[b][c]
        if s>tr: tr=s; tri=[(a,b,c)]
        elif s==tr: tri.append((a,b,c))
    q3p=all(any(x in per for x in t) for t in tri)
    dpairs=[(x,y) for x,y in itertools.combinations(V,2) if d[x][y]==diam]
    q4=all(any(d[x][y]+d[x][z]+d[y][z]==tr for z in V if z not in (x,y)) for x,y in dpairs)
    q4p=all(any(any(d[x][y]+d[x][z]+d[y][z]==tr for z in V if z not in (x,y)) for y in V if y!=x) for x in per)
    q3=all(any(d[t[i]][t[j]]==diam for i,j in ((0,1),(0,2),(1,2))) for t in tri)
    return dict(q3=q3,q3p=q3p,q4=q4,q4p=q4p,tr=tr,diam=diam)
def canon_add(store,G):
    h=nx.weisfeiler_lehman_graph_hash(G,iterations=4)
    for H in store.setdefault(h,[]):
        if nx.is_isomorphic(G,H): return False
    store[h].append(G); return True
def dh_graphs(nmax):
    layer={}; canon_add(layer,nx.empty_graph(1)); out=[]
    for n in range(2,nmax+1):
        new={}
        for L in layer.values():
            for G in L:
                for v in list(G.nodes()):
                    for op in ('pendant','false','true'):
                        H=G.copy(); u=n-1; H.add_node(u)
                        if op=='pendant': H.add_edge(u,v)
                        else:
                            for w in G.neighbors(v): H.add_edge(u,w)
                            if op=='true': H.add_edge(u,v)
                        if nx.is_connected(H): canon_add(new,H)
        layer=new
        gs=[G for L in layer.values() for G in L]
        out.append((n,gs))
        print('DH n=%d: %d graphs'%(n,len(gs)),file=sys.stderr)
    return out
def is_median(G):
    d=dist(G); V=list(G.nodes())
    for a,b,c in itertools.combinations(V,3):
        m=[x for x in V if d[a][x]+d[x][b]==d[a][b] and d[b][x]+d[x][c]==d[b][c] and d[a][x]+d[x][c]==d[a][c]]
        if len(m)!=1: return False
    return True
def maj(x,y,z): return (x&y)|(y&z)|(x&z)
def median_closure(S):
    S=set(S); ch=True
    while ch:
        ch=False
        for x,y,z in itertools.combinations(list(S),3):
            m=maj(x,y,z)
            if m not in S: S.add(m); ch=True
    return S
if __name__=='__main__':
    t0=time.time(); nmax=int(sys.argv[1]) if len(sys.argv)>1 else 9
    bad3=None
    for n,gs in dh_graphs(nmax):
        cnt={'q3p_fail':0,'q4_fail':0,'both_fail':0}
        for G in gs:
            p=props(G)
            if not p['q3p']: cnt['q3p_fail']+=1
            if not p['q4']: cnt['q4_fail']+=1
            if not p['q3p'] and not p['q4']:
                cnt['both_fail']+=1
                if bad3 is None: bad3=(n,sorted(G.edges()),p); print('P3 COUNTEREXAMPLE (DH, both Q3\' and Q4 fail):',bad3,flush=True)
        print('DH n=%d'%n,cnt,flush=True)
    # median graphs: random median-closed connected subsets of Q_d
    seen={}; stats={'median':0,'q3p_fail':0,'q4_fail':0}; ex1=ex2=None
    random.seed(1)
    for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 3000):
        dd=random.randint(3,6); k=random.randint(3,9)
        S=median_closure(random.sample(range(2**dd),k))
        if len(S)>22: continue
        G=nx.Graph(); G.add_nodes_from(S)
        for x in S:
            for i in range(dd):
                if x^(1<<i) in S: G.add_edge(x,x^(1<<i))
        if not nx.is_connected(G): continue
        G=nx.convert_node_labels_to_integers(G)
        if not canon_add(seen,G): continue
        if not is_median(G): continue
        stats['median']+=1
        p=props(G)
        if not p['q3p']:
            stats['q3p_fail']+=1
            if ex1 is None: ex1=(sorted(G.edges()),p); print('P1 COUNTEREXAMPLE (median, Q3\' fails):',ex1,flush=True)
        if not p['q4']:
            stats['q4_fail']+=1
            if ex2 is None: ex2=(sorted(G.edges()),p); print('P2 COUNTEREXAMPLE (median, Q4 fails):',ex2,flush=True)
    print('median',stats,'time %.1fs'%(time.time()-t0))
