# CONTRACT — weights of the Reed–Muller code RM(7,14)

Agent: Claude Code subagent `rm714`, round 6. Written 2026-09-26 (UTC times from `date -u`).
Folder: `$P/work/round6/rm714/`, where `$P = <project>` (the project root).

## 0. Objects and normalisation

- `RM(7,14)` is the set of truth tables on F_2^14 of polynomials in x1,…,x14 over F_2 of total degree ≤ 7.
- `wt(f)` is the number of points where f = 1.
- `Spec = {wt(f) : f ∈ RM(7,14)}` is the weight spectrum.
- Standard facts:
  - Spec ⊆ 2Z (McEliece);
  - w ∈ Spec ⟺ 2^14 − w ∈ Spec (use f + 1);
  - d = 2^{14−7} = 128.
- Two numbers appear throughout: 2.5d = 320 and 3d = 384.

## 1. Primary sources (verbatim)

### 1.1 arXiv:2606.21425v1

Leuenberger & Albrizzio, "On the Weight Spectrum of Reed-Muller Codes RM(7,14)".

- Access: e-print fetched 2026-09-26T06:38Z. Only v1 exists: the API shows published = updated = 2026-06-19T13:42:30Z, and the G1 agent got a 404 for v2.
- Hashes: source tarball sha256 e82719e6…; PDF (14 pp.) sha256 94bf271b….
- Local copies: `refs/src21425/…tex` and `refs/2606.21425v1.pdf`.

**Proposition 4** (PDF pp. 11–12; tex lines 500–503):
> "Let $W_0 =\{0,128,192,224,240,248,252,254,256,272,288,296,304,308\}$ and $W_f$ be the weight spectrum of $RM(7,14)$.Then $$W_0\cup\{312+2i\}\cup\{2^{14}- w\ | \ w \in W\}\setminus M \subseteq W_f,$$ where i ranges over the set of consecutive integers from 0 to $2^{13}-312$ and the set of missing weights $M = \{322, 326, 330, 334, 354, 8174, 8178, 8182, 8186, 8188, 8190, 8194,8196, 8198, 8202, 8206, 8210, 16030,16050, 16054, 16058, 16062\}.$"

**Text after Proposition 4** (p. 13):
> "We are unsure if Proposition 4 is the total weight spectrum of $RM(7,14)$, given the conjecture from [Carlet 2024] about the weight spectrum of $RM(m-c,m)$."

**Conjecture 1** (p. 13), attributed to "Open question in [2], [3]", i.e. Carlet 2024 and Lou–Wang:
> "Let $c$ be any positive integer. For $m \geq 2c$, is the weight spectrum of $RM(m-c,m)$ of the form: $\{0\} \cup A \cup B \cup C \cup \overline{B} \cup \overline{A} \cup \{2^m\}$ where, $A \subseteq [2^c, 2^{c+1}]$, is given by Kasami and Tokura, $B \subseteq [2^{c+1}, 2^{c+1} + 2^{c-1}]$, is given by Kasami, Tokura, and Azumi, $C \subseteq [2^{c+1} + 2^{c-1}, 2^m - 2^{c+1} - 2^{c-1}]$, consists of all consecutive even integers, …"

**Conclusion and Remark** (p. 14):
> "To satisfy Conjecture 1 for $m = 14$, we are missing a small number of weights in the spectrum of $RM(7,14)$. … **Remark.** Because of the way the weights are constructed, the list of missing weights $M$ could be achieved by finding the following 8 weights: $\{322,326,330,334,354, 4378, 4380, 4382\}$."

### 1.2 Carlet's open question

C. Carlet, "The weight spectrum of the Reed–Muller codes RM(m−5,m)", IEEE Trans. Inf. Theory 70(7):4799–4807 (2024), DOI 10.1109/TIT.2023.3343697.

- The IEEE full text is paywalled. The TechRxiv preprint returned HTTP 403. I quote the author's extended abstract instead, which calls itself "an excerpt of the full paper". It is Discrete Mathematics Days 2024, `https://dmd2024.web.uah.es/files/abstracts/paper_10.pdf`, fetched 06:50Z, sha256 3d63f4a1…, p. 4. The Bergen seminar slides (Jan 2024, sha256 611cfec2…) carry the same text.

> "Open question: Let c be any positive integer. For m ≥ 2c, is the weight spectrum of RM(m − c, m) of the form: {0} ∪ A ∪ B ∪ C ∪ B̄ ∪ Ā ∪ {2^m}? where: • A ⊆ [2^c, 2^{c+1}], is given by Kasami and Tokura [5], • B ⊆ [2^{c+1}, 2^{c+1} + 2^{c−1}], is given by Kasami, Tokura, and Azumi in [6, Page 392 and foll.], • C ⊆ [2^{c+1} + 2^{c−1}, 2^m − 2^{c+1} − 2^{c−1}], consists of all consecutive even integers, • Ā stands for the complement to 2^m of A, and B̄ stands for the complement to 2^m of B."

- **Not verified against the IEEE version itself.** A person with IEEE access should confirm the wording there.

### 1.3 The original conjecture (Carlet–Solé)

Carlet–Solé, Discrete Math. 346 (2023) 113568; arXiv:2301.13497v3, §6. Source fetched 06:49Z, sha256 a01abc3e….

> "**Conjecture**: Let $c$ be any positive integer. Then for $m> 2c-1$, the weight spectrum of $RM(m-c,m)$ is of the form: … $B\subseteq [2^{c+1},2^{c+1}+2^c],$ is given by Kasami, Tokura, and Azumi … $C\subseteq [2^{c+1}+2^c,2^m-2^{c+1}-2^c],$ consists of consecutive even integers"

**Discrepancy.** In the original conjecture, C starts at 3d. Carlet 2024, Lou–Wang and 2606.21425 all start C at 2.5d. The undecided weights 322–334 lie exactly in (2.5d, 3d). They therefore contradict the 2.5d version (Carlet 2024's question) if absent. Under the 3d version they would fall in "B, given by KTA", but KTA only covers weights below 2.5d.

### 1.4 Lou–Wang

arXiv:2406.03803v1, fetched 06:41Z, sha256 7a9b2d88…. Published in DCC 93 (2025) 4925–4936, DOI 10.1007/s10623-025-01708-7, issue 11 according to Crossref.

- **Conjecture 1** (end of §3; "Conjecture of [CP], Open question of [Carlet1]"): the same statement as 1.2, asserted rather than asked. The upper end is misprinted as $2^{m-1}-2^{c+1}-2^{c-1}$.
- **§4, Construction 2 and Conjecture 2:**

> "Let $g_1=x_{1}x_{2}\cdots x_{m}+x_{i_1}x_{i_2}\cdots x_{i_m}+x_{i_{m+1}}\cdots x_{i_{2m}}$ and $g_2=x_{1}x_{2}\cdots x_{m}+x_{i_{2m+1}}\cdots x_{i_{3m}}+x_{i_{3m+1}}\cdots x_{i_{4m}}$, where $g_1,g_2\in B_{2m}$ and $1\le i_1,\ldots,i_{4m}\le 2m$. We then construct $g=0||(g_1+a_1)||g_2||(g_1+g_2+a_2)\in RM(m+1,2m+2)$, where $a_1,a_2\in F_2$."

> "**Conjecture 2.** Let $S$ be the set of all weights generated by Construction 2. Then $\{2^{m+2}+2^m+2i\}\cup\{2^{2m}+2^{m}+2i\}\subseteq S$, where $0\le i<2^{m}$ and $m\ge 4$."

- At m = 6 the construction lives in RM(7,14), and Conjecture 2 asserts {320, 322, …, 446} ⊆ S.
- The authors also write: "Further study may verify the conjecture for $RM(7,14)$ and determine the weight spectrum of $RM(m-7,m)$."

### 1.5 Later work (full detail in `g1/G1-REPORT.md`)

- arXiv:2609.13653 (Shi–Xing–Solé) treats q-ary GRM codes for q = 3, 4, 5, 7 only. It says nothing about RM(7,14).
- **Unread, must be checked by a person:** Y. Lou & Q. Wang, "A note on two conjectures about the weight spectra of the Reed–Muller codes", Discrete Applied Math. 388 (2026) 142–145, DOI 10.1016/j.dam.2026.03.038, online 2026-04-04.
  - It is closed access. Crossref, Semantic Scholar and OpenAlex have no abstract (checked 07:15Z).
  - Its reference list (Crossref) cites RM(3,9), RM(4,9) and RM(4,8) weight distributions and sampling papers.
  - It may be about Conjectures 1/2 above. 2606.21425 (June 2026) does not cite it.

## 2. Fixed reading of the open problem

**Problem.** For each w ∈ U₀ = {322, 326, 330, 334}, decide whether w ∈ Spec. By complementation this is equivalent to deciding 2^14 − w ∈ {16062, 16058, 16054, 16050}.

**Readings, weak to strong:**

- **(R1)** The paper's missing list M has 22 values. Decide each of them.
- **(R2)** The Remark lists 8 weights. Decide each of them.
- **(R3)** Carlet's question at (c, m) = (7, 14). Given Kasami–Tokura and Kasami–Tokura–Azumi for weights below 2.5d, and given witnesses for all other even weights in [320, 16064]:
  - the answer is **positive** iff all of 322, 326, 330, 334 are weights;
  - the answer is **negative** iff at least one of them is not.
- **(R4)** The full spectrum of RM(7,14).
- **(R5)** Lou–Wang Conjecture 2 at m = 6. This is a finite statement about an explicit construction, and it is decidable by computation.

**What is actually open**, per the source's own words: the authors could not reach M, and are "unsure if Proposition 4 is the total weight spectrum".

**Notes.**

- Proposition 4 of 2606.21425 rests on unpublished computer searches (Lemmas 6 and 9). Its correctness is not assumed here. We re-derive every claimed weight with our own witnesses; see PROOF.md §2.
- The **upper-bound part** (no weights below 320 other than W₀ ∪ {312, 314, 316, 318}) is **not** re-proved here. It is the Kasami–Tokura–Azumi theorem as used in 2606.21425 and in Lou–Wang Lemma 2. The KTA paper itself could not be fetched (HTTP 403).

## 3. Session-2 clarifications (2026-09-26, ~14:15Z)

- **R2 and novelty.** The Remark's weights 4378, 4380, 4382 are *not* in M. Proposition 4 of 2606.21425 already asserts them:
  - they lie in {312 + 2i} \ M, and in the sets S2mod4 = {254} ∪ {314 + 4i : 0 ≤ i ≤ 1969} \ M′ and S0mod4 = B ∪ {304 + 4i} (PDF p. 12, txt l. 470–520).
  - The Remark ("the list of missing weights M could be achieved by finding the following 8 weights") refers to seeds of the authors' concatenation, not to weights missing from the spectrum.
  - Hence of the Remark's 8 weights only 354 is a new weight; for 4378–4382 we give independent explicit witnesses.
- **R5, two readings.** Construction 2 is stated with monomials, i.e. g1, g2 are sums of three monomials of degree ≤ m, with indices in [1, 2m]. But the proof of Lou–Wang's Proposition 5 takes "S = the set of all weights of 0‖(g1+a1)‖g2‖(g1+g2+a2) with g1, g2 ∈ RM(m, 2m)". Reading (b) contains reading (a), and Proposition C in PROOF.md covers both.
- **Wording source for Conjecture 2.** arXiv:2406.03803v1, lw.tex l. 382–388. The published DCC version could not be read (Springer login wall). Its reference list gained 2 entries, so the text was revised; whether the wording of Conjecture 2 changed is unknown.
