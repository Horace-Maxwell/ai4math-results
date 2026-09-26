"""Write the human-readable rho data (Lemma C input) for B_6 rank 2 and B_7 rank 3."""
from diagrams import brauer_elements, halves, sandwich
from construct import proof_triangle, proof_matching, rho_from_triangle_and_matching, quotient_map_odd, sgnbit

def hname(h):
    n = len(h); F = [str(i + 1) for i in range(n) if h[i] == 'F']
    arcs = sorted({tuple(sorted((i + 1, h[i] + 1))) for i in range(n) if h[i] not in ('F', -1)})
    return "free{" + ",".join(F) + "} arcs" + "".join(f"{{{a},{b}}}" for a, b in arcs)

for n, r in [(6, 2), (7, 3)]:
    S = brauer_elements(n); H = halves(S, r); P = sandwich(H)
    tri = proof_triangle(n, r); M = proof_matching(n, r, H, P, tri)
    rho = rho_from_triangle_and_matching(H, P, tri, M); fbar, c = quotient_map_odd(H, P, rho)
    with open(f"../certificates/rho_B{n}_rank{r}.txt", "w") as fh:
        fh.write(f"# B_{n}, rank {r}: N={len(H)} half-diagrams. rho = 3-cycle (negative triangle) + {len(M)} transpositions of compatible pairs.\n")
        fh.write("# columns: half-diagram lambda | rho(lambda) | sign bit of p_{lambda,rho(lambda)} | c(lambda)\n")
        for h in [tri[0], tri[1], tri[2]] + [x for pr in M for x in pr]:
            fh.write(f"{hname(h)} | {hname(rho[h])} | {sgnbit(P[(h, rho[h])])} | {c[h]}\n")
    print(n, r, len(H), "written")
