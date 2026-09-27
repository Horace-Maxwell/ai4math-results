# Explicit switchings for T(a) (s_c = +1 always).  Returns (aa, sigma, mu) in the vertex order of ht2.make_s,
# where aa lists branch sizes in NONDECREASING order.
from collections import Counter

def _assemble(groups, per_group):
    aa, sigma, mu = [], [], []
    for b in sorted(groups):
        lam_list, sig_list = per_group[b]
        for lam, sg in zip(lam_list, sig_list):
            aa.append(b); sigma.append(sg); mu.append((b - lam) // 2)
    return tuple(aa), sigma, mu

def construction_I(a):
    """Theorem D1 construction (Target I): intended for trees with no bare leaves and every even
    branch size of even multiplicity. Leaf sums: odd b>=3: -1 (first two branches +1,-3 if k_b>=2);
    b = 1: all -1, except the first branch +1 if k_1 >= 2; even b: alternately 0, -2.
    sigma = +1 everywhere (bare branches, if any: +1)."""
    g = Counter(a); per = {}
    for b, kb in g.items():
        if b == 0: lam = [0] * kb
        elif b % 2 == 1:
            lam = [-1] * kb
            if kb >= 2:
                if b >= 3: lam[0], lam[1] = 1, -3
                else: lam[0] = 1
        else:
            lam = [0 if j % 2 == 0 else -2 for j in range(kb)]
        per[b] = (lam, [1] * kb)
    return _assemble(g, per)

def construction_II(a):
    """Theorem D2 construction (Target II): intended for trees in which every odd branch size has even
    multiplicity. Leaf sums: even b>=2: 0 (first two branches +2,-2 if k_b>=2); odd b (k_b even): alternately +1,-1.
    sigma = +1, except: if all a_i <= 1 and k_0 >= 2, the first bare branch gets sigma = -1."""
    g = Counter(a); per = {}
    all_small = all(b <= 1 for b in g)
    for b, kb in g.items():
        if b == 0:
            lam = [0] * kb
            sig = [1] * kb
            if all_small and kb >= 2: sig[0] = -1
            per[b] = (lam, sig); continue
        if b % 2 == 0:
            lam = [0] * kb
            if kb >= 2: lam[0], lam[1] = 2, -2
        else:
            lam = [1 if j % 2 == 0 else -1 for j in range(kb)]   # sums to 0 if kb even (else +1)
        per[b] = (lam, [1] * kb)
    return _assemble(g, per)

def in_class_D1(a):
    g = Counter(a)
    return g.get(0, 0) == 0 and all(g[b] % 2 == 0 for b in g if b % 2 == 0)

def in_class_D2(a):
    from fractions import Fraction
    g = Counter(a)
    if any(g[b] % 2 == 1 for b in g if b % 2 == 1): return False
    if tuple(sorted(a)) == (0, 0, 0, 0): return False            # K_{1,4}
    if g.get(1, 0) == 0:
        F1 = Fraction(g.get(0, 0)) - sum(Fraction(g[b], b - 1) for b in g if b >= 2)
        if F1 == 1: return False                                  # t = 1 would be a secular root
    return True

def construction_mixed(a, S_all=False, b1_mode='sigma'):
    """Mixed target (s_c = +1): group b goes to Target II (leaf-sum average 0, A_b = k_b) if b is even (incl. 0)
    or [k_b even and (S_all or b == 1)]; otherwise Target I (leaf-sum average -1, A_b = 0).
    Then G = theta + F_II(t) at secular roots (no defects), except for b = 1 with k_1 odd >= 3:
      b1_mode='sigma': leaves all -1, one sigma flipped (Q = 1 - 2/(t-1));
      b1_mode='lambda': leaves -1 except one +1 (P gets +2/(t-1)).
    Within-group variation for (L_b) and a non-constant leaf branch for (Z) are built in where possible."""
    g = Counter(a); per = {}
    all_small = all(b <= 1 for b in g)
    for b, kb in g.items():
        if b == 0:
            sig = [1] * kb
            if all_small and kb >= 2: sig[0] = -1
            per[b] = ([0] * kb, sig); continue
        to_II = (b % 2 == 0) or (kb % 2 == 0 and (S_all or b == 1))
        sig = [1] * kb
        if to_II:
            if b % 2 == 0:
                lam = [0] * kb
                if kb >= 2:
                    if b >= 4 or kb >= 3: lam[0], lam[1] = 2, -2
                    else: lam = [0, 0]; sig = [1, -1]     # b = 2, k_b = 2: vary sigma instead (keeps both branches non-constant)
            else:
                lam = [1 if j % 2 == 0 else -1 for j in range(kb)]
        else:  # Target I, b odd (k_b odd, or even k_b with S_all False and b >= 3)
            lam = [-1] * kb
            if kb >= 2:
                if b >= 3: lam[0], lam[1] = 1, -3
                else:  # b == 1, k_1 odd >= 3
                    if b1_mode == 'sigma': sig[0] = -1
                    else: lam[0] = 1
            if b == 1 and kb % 2 == 0 and kb >= 2:
                pass
        per[b] = (lam, sig)
    return _assemble(g, per)
