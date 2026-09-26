# Statement contract: Hak–Kozerenko–Oliynyk, open problems 1–3 (triameter)

Agent: Claude Code subagent (round 6, `hko-triameter`). Written 2026-09-26 (UTC times from `date -u`).

## 1. Source

- A. Hak, S. Kozerenko, B. Oliynyk, *A note on the triameter of graphs*.
  - arXiv:2103.10806. v1 is the only version (2021-03-19).
  - Journal version: Discrete Appl. Math. 309 (2022) 278–284, DOI 10.1016/j.dam.2021.12.011. The journal text was not seen: the scout got HTTP 403 from ScienceDirect.
- LaTeX source:
  - fetched 2026-09-26 06:4x UTC from `https://arxiv.org/e-print/2103.10806`;
  - gzip SHA-256 `058040596e1df86642bbc6571dc5da3cc3d5f6bcc4cef24f46f0e4b0e4d63c8f`;
  - saved as `src/Hak_Kozerenko_Oliynyk.tex`, SHA-256 `edeeaa571cf8564c5058086c8aa30d270e9f89db2c076c364423c06572f7990a`.
- Verbatim text: every item below points to exact line numbers in that file. The file is the verbatim record. This contract restates the items precisely, but not word for word (house rule: at most one short verbatim quote per document).

| Item | Location in `src/Hak_Kozerenko_Oliynyk.tex` |
|---|---|
| Standing assumption: graphs simple and finite; path metric; diameter; diametral pair; **peripheral = belongs to some diametral pair** | Sec. 2, line 101 |
| d(u,v,w) := d(u,v)+d(u,w)+d(v,w); tr(G) := max over u,v,w ∈ V(G) (repetitions not excluded); triametral triple | Sec. 2, lines 103–107 |
| Metric interval [u,v]; **median graph**: connected, and \|[u,v]∩[u,w]∩[v,w]\| = 1 for every triple | Sec. 2, lines 109–111 |
| 2·diam ≤ tr ≤ 3·diam (Kola–Panigrahi) | Sec. 2, line 121 |
| Das's Questions 1–4 (Q3: triametral triple contains a diametral pair; Q4: diametral pair extends to a triametral triple; both stated for trees) | Sec. 1, lines 73–78 |
| Distance-hereditary graphs; HKO's (abbreviated) quotation of the Bandelt–Mulder four-point characterisation; Fig. 1 graphs G, H | Sec. 3.2, line 373 and the Fig. 1 code, lines 375–431 |
| Question 3' and Question 4' (schemata with "..." for a graph class) | Sec. 4, lines 435–441 |
| Q3 fails for median graphs (Fig. 2) | Sec. 4, line 443 |
| **Problem 1** | Sec. 4, lines 443–447 |
| **Problem 2**, with the sentence before it | Sec. 4, lines 474–479 |
| Q3', Q4' fail for modular graphs (Fig. 1 G; K_{2,3}) and for distance-hereditary graphs (Fig. 1) | Sec. 4, lines 481–483 |
| **Problem 3** | Sec. 4, lines 483–488 |

## 2. Definitions fixed for this contract

G is a finite, simple, connected graph with path metric d, D = diam(G), T = tr(G).

- **Triameter.** T = max{d(u,v,w) : u,v,w ∈ V(G)}, where d(u,v,w) = d(u,v)+d(u,w)+d(v,w).
  - Repetitions are allowed, as in the paper's formula.
  - For |V| ≥ 3 this equals the maximum over triples of distinct vertices: a triple with a repeat has sum ≤ 2D, and any diametral pair with a third vertex already reaches ≥ 2D.
- **Triametral triple.** Any u, v, w with d(u,v,w) = T.
- **Diametral pair.** d(u,v) = D.
- **Peripheral vertex.** HKO's definition: u lies in some diametral pair.
  - Equivalent formulation: ecc(u) = D.
  - Lean proves the equivalence for finite connected graphs (`isPeripheral_iff_isPeripheralPair`, using Mathlib's `eccent`/`ediam`).
- **Median graph.** Connected, and |[u,v]∩[u,w]∩[v,w]| = 1 for all u, v, w (repetitions allowed; they are harmless).
- **Distance-hereditary graph** (HKO, after Howorka). Connected, and every connected induced subgraph is isometric.
- **Four-point condition (Bandelt–Mulder 1986).** Used only in the direction DH ⇒ condition. Form used, as stated in Dragan–Leitert, arXiv:1511.05109, Prop. "(4-point condition)":
  - For any four vertices u, v, w, x, at least two of the sums d(u,v)+d(w,x), d(u,w)+d(v,x), d(u,x)+d(v,w) are equal.
  - If the two smaller sums are equal, the largest exceeds them by at most 2.
  - Equivalent symmetric form FP(A,B,C): some two of the three sums are equal, and the third is ≤ their common value + 2.
  - **Note:** HKO line 373 quotes this characterisation without the "+2" clause. We use the full statement.
  - Sanity check: every connected DH graph with n ≤ 10 (all 49,394 of them), and ~6,000 random DH graphs up to n = 14, satisfy FP; see `logs/`.

## 3. The questions (for a graph G)

- **Q3(G)** (Das): every triametral triple contains a diametral pair.
- **Q3'(G)** (HKO): every triametral triple contains a peripheral vertex.
- **Q4(G)** (Das): every diametral pair {x,y} extends to a triametral triple, i.e. some z has d(x,y,z) = T.
  - **Weak reading** (z arbitrary) and **strong reading** (z ∉ {x,y}).
  - For |V| ≥ 3 these are equivalent. If z ∈ {x,y} works, then T = 2D, and every z works.
  - Our refutation (G2) excludes every z, so it refutes both readings.
- For a class 𝒞, "Q holds for 𝒞" means Q(G) for every G ∈ 𝒞.

## 4. The three problems and their readings

1. **Problem 1** (only verbatim quote in this file: "Does Question 3' hold for median graphs?").
   - Claim P1: Q3'(G) for every finite median graph G.
2. **Problem 2.** Does Q4 hold for median graphs?
   - **Reading R1** (the numbered item, the primary one): Q4(G) for every finite median graph.
   - **Reading R2:** the sentence just before the item (line 474) actually describes Q3, not Q4.
     - Q3 for median graphs is already refuted in HKO itself (Fig. 2, line 443).
     - So R2 is read as a typo. We report both readings; our G1 also violates Q3.
3. **Problem 3.** For distance-hereditary graphs, does at least one of Questions 3' and 4 hold?
   - **Per-graph reading** (adopted): for every connected DH graph G, Q3'(G) ∨ Q4(G).
   - **Class reading** ("Q3' holds for all DH graphs, or Q4 holds for all DH graphs"): false by HKO's own Fig. 1, since G violates Q3' and H violates Q4. So it cannot be the intended question.
   - **Stronger variant** (we prove it): Q3(G) ∨ Q4(G) for every connected DH graph. It implies the adopted reading, because Q3 ⇒ Q3'.
   - It also implies the Q4' variant (Q3' ∨ Q4'), because Q4 ⇒ Q4'.

## 5. Strong and weak readings: what each result covers

| Result | Reading covered |
|---|---|
| P1 refuted by G1 | The bad triple {1,5,6} has distinct vertices, so it refutes P1 whether or not repeated triples are allowed, with either definition of "peripheral" (both formalised). G1 also refutes Q3. |
| P2 refuted by G2 | No z (any z, including z ∈ {5,7}) gives d(5,7,z) = tr. Refutes both the weak and strong readings of Q4. G2 also refutes the weaker Q4' ((B') on MathOverflow): the peripheral vertex 5 lies in no triametral triple (Lean `not_problem2ClaimWeak`). R2 (= Q3 for median graphs) is refuted by HKO Fig. 2 and by G1. |
| P3 answered affirmatively | Per-graph reading, strengthened to Q3 ∨ Q4, for all finite connected graphs with the four-point condition. The transfer to "all distance-hereditary graphs" uses the cited Bandelt–Mulder theorem, which is **not formalised**. |

## 6. Literature status of the problems (G1, 2026-09-26 06:43–07:30 UTC; details in `PROOF.md` §1 and `querylog.tsv`)

- **Authors' own later restatement.**
  - Hak and Kozerenko entered the median-graph question in the Lviv Scottish Book, vol. 3, p. 154 (2025-02-10).
  - It was relayed to MathOverflow as question 506431, "Diameter-triameter problem" (2025-12-28). It uses the labels (A) = Q3, (B) = Q4, (A') = Q3', (B') = Q4'. The prize asks whether (B), or at least (B'), holds for median graphs.
  - This confirms reading R1 of Problem 2 (Problem 2 = Q4).
- **Problem 2 is already answered (negatively).**
  - MathOverflow answer 506536 by user rgvalenciaalbornoz, 2025-12-31 20:38 UTC, accepted; the LSB account awarded the prize.
  - It gives an 11-vertex median graph (four squares glued in a tree of squares) violating (B) and (B'). We verified the thread via the StackExchange API.
  - Wikipedia ("Triameter (graph theory)", last revision 2025-10-19) and Kozerenko, Discrete Math. Lett. 18 (2026) 55–62 still describe it as posed or open; they are stale on this point.
- **Problem 1 (A' = TD' for median graphs).** Wikipedia's open-problems section suggests investigating it; the LSB note also invites it. No answer was found in the covered sources.
- **Problem 3 (DH alternative).** Not on Wikipedia, LSB or MO. No answer was found in the covered sources.
- **Wikipedia caption error.** A figure caption calls HKO Fig. 1 G "also a median graph". It is K_{2,3} plus a pendant vertex, which is modular but not median (formal: `F1G_not_median`). So it is not a median counterexample to Problem 1.
