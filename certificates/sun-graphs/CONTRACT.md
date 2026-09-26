# CONTRACT: integral generalized sun graphs (arXiv:2609.28754v1)

Agent: round-6 research agent `sun-graphs`, 2026-09-26, 18:42–20:10 UTC (`date -u`).

## Source

- R. O. Braga, J. C. Moraes, M. C. Santos, "Pendant paths and integral generalized sun graphs",
  arXiv:2609.28754**v1** (submitted 2026-09-23 19:56:31 UTC; the arXiv API at 18:58 UTC today lists v1 only).
- LaTeX file `ArXiv__1_.tex` from the e-print, downloaded by the scout today
  (`work/round6/scouting/fresh-0926/src/2609.28754/`), SHA-256 `21a822ee…c64f8`.
  Line numbers below refer to that file.

## Verbatim definitions

- Integral (line 78): "We say that a graph is \emph{integral} if the spectrum of its adjacency matrix consists entirely of integers."
- Generalized sun graph (line 85): "The unicyclic graphs considered in that work are obtained by attaching pendant paths to the vertices of a cycle and are referred to as \emph{generalized sun graphs}."
- Attaching (Introduction, notation paragraph after Conjecture 2): "attaching $P_t$ to $v$ means adding $t$ new vertices $u_1,\ldots,u_t$ together with the edges $vu_1$ and $u_iu_{i+1}$ for $1\leq i\leq t-1$." The notation is $C_b(n_1P_{t_1},\ldots,n_bP_{t_b})$: $n_k$ copies of $P_{t_k}$ are attached at $v_k$. $C_{b,1}(n_1,\dots,n_b)$ has only pendant vertices.
- Conjecture 2 (lines 91–92): "If a generalized sun graph that is not a cycle is integral, then the order of the generalized sun graph's cycle is a multiple of 4."
- Girth: a generalized sun graph is unicyclic. Its girth is the length $b$ of its unique cycle, which the paper calls "the order of the generalized sun graph's cycle".

## The two questions (verbatim)

**Q-min** (Section 4, line 805): "In particular, the search does not prove that the graph on $42$ vertices has minimum order among all counterexamples to Conjecture~\ref{conj:two}: a parameter vector with some $n_k>14$ can still define a graph of order below $42$, and generalized sun graphs containing copies of $P_2$ or both types of pendant paths are not included."

**Q-girth** (Section 5, lines 839–841): "The cycle lengths that actually occur are still unknown: the present paper shows that $4$ and $6$ do, and it is natural to ask whether $b$ must be even and whether these are the only possibilities."

## Fixed reading

- **Counterexample to Conjecture 2:** a generalized sun graph $G$ that is integral, is not a cycle, and has cycle length $b\not\equiv 0 \pmod 4$.
- **Smallest counterexample:** a counterexample of minimum order $n=|V(G)|$.
  - The paper exhibits $C_{6,1}(0,6,6,12,6,6)$, with $n=42$.
  - Q-min asks whether some counterexample has $n\le 41$.
- **Strong reading, which we prove:** at each cycle vertex, any finite multiset of pendant paths, with lengths possibly mixed at the same vertex.
  - This contains the paper's notation $C_b(n_1P_{t_1},\dots)$, which has one path length per vertex, and hence every weaker reading.
  - By the paper's Theorem 2.1 (proved there), an integral graph has no pendant path with 3 or more edges. So each cycle vertex $v_k$ carries $p_k$ copies of $P_1$ and $q_k$ copies of $P_2$, with $p_k,q_k\ge0$.
- **Our claim for Q-min:**
  - For every integral generalized sun graph with $n\le 41$ that is not a cycle, $4\mid b$.
  - Hence 42 is the minimum order of a counterexample.
  - Bonus, if the $n=42$ runs finish: $C_{6,1}(0,6,6,12,6,6)$ is the only counterexample of order 42.
- **Q-girth:**
  - Weak form: must $b$ be even?
  - Strong form: is $b\in\{4,6\}$ always?
  - We give partial results only, restricting the possible odd $b$ by a proved necessary condition. See PROOF.md.
- **Normalisations:**
  - The bare cycle is excluded, since the conjecture says "not a cycle".
  - Graphs are counted up to the dihedral symmetry of the cycle. This does not affect the order.
  - $b\ge 3$.
