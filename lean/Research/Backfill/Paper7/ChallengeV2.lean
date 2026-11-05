import Mathlib

/-!
# Paper 7 V2 author candidate: not frozen, not compiled, zero proof credit

The original 25 target propositions and every original mathematical primitive
are retained. Thirteen added targets address explicit coverage gaps and mathematical
background. See COVERAGE.md/json for exact scope, unresolved statistical/wording
choices, and historical run data which are not kernel proofs.

Target toolchain: Lean/Mathlib 4.34.1. This file imports Mathlib only. Its namespace
BackfillPaper7.Challenge is intentionally preserved; import this new module in
isolation rather than importing the old Challenge at the same time.

The original source's Section6Bound/Section6CycleThree names are retained for
compatibility; their paper location is the present Section 7 (Open questions).
No theorem proving a paper target is supplied here. Independent semantic review,
actual statement/test compilation and a new hash freeze must precede proof work.
-/

set_option autoImplicit false

namespace BackfillPaper7.Challenge

open Polynomial Finset SimpleGraph

noncomputable section

/-! ## 1. Spectral vocabulary -/

section Spectral

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Real eigenvalues (with multiplicity) of a real square matrix: the real roots of its
characteristic polynomial.  For a real symmetric matrix this is the whole spectrum. -/
def eigs (M : Matrix n n ℝ) : Multiset ℝ := M.charpoly.roots

/-- `n_+(M)`: number of positive eigenvalues, with multiplicity. -/
def nPos (M : Matrix n n ℝ) : ℕ := ((eigs M).filter (fun x => 0 < x)).card
/-- `n_-(M)`: number of negative eigenvalues, with multiplicity. -/
def nNeg (M : Matrix n n ℝ) : ℕ := ((eigs M).filter (fun x => x < 0)).card
/-- `n_0(M)`: multiplicity of the eigenvalue `0`. -/
def nZero (M : Matrix n n ℝ) : ℕ := (eigs M).count 0

end Spectral

section GraphSpectral

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Spectrum (with multiplicity) of a finite simple graph: eigenvalues of `A(G)` over `ℝ`. -/
def spec (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ := eigs (G.adjMatrix ℝ)

/-- `N_{>t}(G)`. -/
def Ngt (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) : ℕ := ((spec G).filter (fun x => t < x)).card
/-- `N_{≥t}(G)`. -/
def Nge (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) : ℕ := ((spec G).filter (fun x => t ≤ x)).card
/-- `N_{<t}(G)`. -/
def Nlt (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) : ℕ := ((spec G).filter (fun x => x < t)).card
/-- `N_{≤t}(G)`. -/
def Nle (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) : ℕ := ((spec G).filter (fun x => x ≤ t)).card
/-- `mult(x)`: multiplicity of `x` as an eigenvalue of `A(G)` (`0` if `x` is not one). -/
def mult (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℝ) : ℕ := (spec G).count x

/-- A graph is *integral* if every eigenvalue of its adjacency matrix is an integer
(every element of the complex spectrum of `A(G)` is an integer). -/
def IsIntegralGraph (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ μ ∈ spectrum ℂ (G.adjMatrix ℂ), ∃ z : ℤ, μ = (z : ℂ)

/-- `B^+`: the multiset of eigenvalues `≥ 2`. -/
def Bplus (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ := (spec G).filter (fun x => 2 ≤ x)

/-- `S_2 = ∑_{λ ∈ B^+} λ²`. -/
def S2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := ((Bplus G).map (fun x => x ^ 2)).sum

/-- The eigenvalues with `|λ| ≥ 2`, with multiplicity. -/
def bigEigs (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ := (spec G).filter (fun x => 2 ≤ |x|)

end GraphSpectral

/-! ## 2. Cycles of a graph -/

section Cycles

variable {V : Type} [DecidableEq V]

/-- Edge sets of the cycles of length `ℓ` of `G` (a cycle is determined by its edge set). -/
def cycleEdgeSets (G : SimpleGraph V) (ℓ : ℕ) : Set (Finset (Sym2 V)) :=
  {s | ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.length = ℓ ∧ w.edges.toFinset = s}

/-- Number of cycles of length `ℓ` (`c_ℓ` in the paper). -/
def cycleCount (G : SimpleGraph V) (ℓ : ℕ) : ℕ := (cycleEdgeSets G ℓ).ncard

/-- `g` is the length of the shortest odd cycles of `G` (in particular `G` has an odd cycle). -/
def IsOddGirth (G : SimpleGraph V) (g : ℕ) : Prop :=
  Odd g ∧ (∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.length = g) ∧
    ∀ (u : V) (w : G.Walk u u), w.IsCycle → Odd w.length → g ≤ w.length

/-- `G` is unicyclic (connected, exactly one cycle) and its cycle has length `b`. -/
def IsUnicyclicWithCycle (G : SimpleGraph V) (b : ℕ) : Prop :=
  G.Connected ∧ ∃ s ∈ cycleEdgeSets G b, ∀ (ℓ : ℕ), ∀ t ∈ cycleEdgeSets G ℓ, t = s

end Cycles

/-! ## 3. Generalized sun graphs -/

/-- Vertex type of the generalized sun graph with cycle length `b` and pendant-path data `L`:
`Sum.inl k` is the cycle vertex `v_k`; `Sum.inr ⟨k, j, i⟩` is vertex number `i` (`i = 0` is the
vertex joined to `v_k`) of the `j`-th pendant path at `v_k`, which has `(L k).get j` vertices. -/
abbrev SunV (b : ℕ) (L : Fin b → List ℕ) : Type :=
  Fin b ⊕ (Σ k : Fin b, Σ j : Fin (L k).length, Fin ((L k).get j))

/-- Generating relation of the generalized sun graph (symmetrized by `SimpleGraph.fromRel`,
which also discards loops): `v_k → v_{k+1 mod b}`; `v_k →` first vertex of each path at `v_k`;
consecutive vertices of each path. -/
def sunRel (b : ℕ) (L : Fin b → List ℕ) : SunV b L → SunV b L → Prop
  | Sum.inl k, Sum.inl k' => k'.val = (k.val + 1) % b
  | Sum.inl k, Sum.inr x => x.1 = k ∧ x.2.2.val = 0
  | Sum.inr x, Sum.inr y => x.1 = y.1 ∧ x.2.1.val = y.2.1.val ∧ y.2.2.val = x.2.2.val + 1
  | Sum.inr _, Sum.inl _ => False

instance sunRelDec (b : ℕ) (L : Fin b → List ℕ) : DecidableRel (sunRel b L)
  | Sum.inl k, Sum.inl k' => inferInstanceAs (Decidable (k'.val = (k.val + 1) % b))
  | Sum.inl k, Sum.inr x => inferInstanceAs (Decidable (x.1 = k ∧ x.2.2.val = 0))
  | Sum.inr x, Sum.inr y =>
      inferInstanceAs (Decidable (x.1 = y.1 ∧ x.2.1.val = y.2.1.val ∧ y.2.2.val = x.2.2.val + 1))
  | Sum.inr _, Sum.inl _ => inferInstanceAs (Decidable False)

/-- The generalized sun graph: the cycle `C_b` with, at `v_k`, a pendant path on `t` vertices
for every entry `t` of `L k`. -/
def sunGraph (b : ℕ) (L : Fin b → List ℕ) : SimpleGraph (SunV b L) :=
  SimpleGraph.fromRel (sunRel b L)

instance sunGraphDec (b : ℕ) (L : Fin b → List ℕ) : DecidableRel (sunGraph b L).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (sunRel b L)).Adj)

/-- Order `n = |V(G)|`. -/
def order (b : ℕ) (L : Fin b → List ℕ) : ℕ := Fintype.card (SunV b L)

/-- Number of pendant (non-cycle) vertices; the graph is not a cycle iff this is positive. -/
def pendantCount (b : ℕ) (L : Fin b → List ℕ) : ℕ := ∑ k, (L k).sum

/-- A *counterexample* to Conjecture 2: a generalized sun graph that is integral, is not a
cycle, and whose cycle length is not divisible by `4`. -/
def IsCounterexample (b : ℕ) (L : Fin b → List ℕ) : Prop :=
  3 ≤ b ∧ 0 < pendantCount b L ∧ IsIntegralGraph (sunGraph b L) ∧ ¬ 4 ∣ b

/-- `C_{6,1}(0,6,6,12,6,6)` (42 vertices). -/
def C61 : Fin 6 → List ℕ :=
  ![[], List.replicate 6 1, List.replicate 6 1, List.replicate 12 1, List.replicate 6 1,
    List.replicate 6 1]

/-- `C_{4,1}(6,0,3,0)` (13 vertices). -/
def G13 : Fin 4 → List ℕ := ![List.replicate 6 1, [], List.replicate 3 1, []]

/-- `C_4(5P_2, P_1, 2P_2, P_1)` (20 vertices). -/
def G20a : Fin 4 → List ℕ := ![List.replicate 5 2, [1], List.replicate 2 2, [1]]

/-- `C_{4,2}(4,4,0,0)` (20 vertices). -/
def G20b : Fin 4 → List ℕ := ![List.replicate 4 2, List.replicate 4 2, [], []]

/-! ## 4. The main results -/

/-- **Theorem 1.** Up to isomorphism, `C_{6,1}(0,6,6,12,6,6)` is the only counterexample to
Conjecture 2 with at most 42 vertices (and it is a counterexample, with 42 vertices). -/
def Theorem1 : Prop :=
  (IsCounterexample 6 C61 ∧ order 6 C61 = 42) ∧
    ∀ (b : ℕ) (L : Fin b → List ℕ), IsCounterexample b L → order b L ≤ 42 →
      Nonempty (sunGraph b L ≃g sunGraph 6 C61)

/-- **Theorem 1**, "in particular": the minimum order of a counterexample is `42`. -/
def Theorem1MinOrder : Prop :=
  (∃ (b : ℕ) (L : Fin b → List ℕ), IsCounterexample b L ∧ order b L = 42) ∧
    ∀ (b : ℕ) (L : Fin b → List ℕ), IsCounterexample b L → 42 ≤ order b L

/-- **Theorem 2.** Every integral generalized sun graph with at most 41 vertices that is not a
cycle has a cycle of length 4 and is isomorphic to `C_{4,1}(6,0,3,0)`, `C_4(5P_2,P_1,2P_2,P_1)`
or `C_{4,2}(4,4,0,0)`. -/
def Theorem2 : Prop :=
  ∀ (b : ℕ) (L : Fin b → List ℕ), 3 ≤ b → 0 < pendantCount b L →
    IsIntegralGraph (sunGraph b L) → order b L ≤ 41 →
      b = 4 ∧ (Nonempty (sunGraph b L ≃g sunGraph 4 G13) ∨
        Nonempty (sunGraph b L ≃g sunGraph 4 G20a) ∨ Nonempty (sunGraph b L ≃g sunGraph 4 G20b))

/-- Text after Theorem 2 (claim taken from [BRT]): the three graphs have 13, 20, 20 vertices,
are not cycles, and have spectra `{0^[9], ±2, ±3}` and (both) `{0^[2], ±1^[7], ±2, ±3}`
(stated through their characteristic polynomials; in particular they are integral). -/
def Theorem2Graphs : Prop :=
  order 4 G13 = 13 ∧ order 4 G20a = 20 ∧ order 4 G20b = 20 ∧
  0 < pendantCount 4 G13 ∧ 0 < pendantCount 4 G20a ∧ 0 < pendantCount 4 G20b ∧
  ((sunGraph 4 G13).adjMatrix ℤ).charpoly = X ^ 9 * (X ^ 2 - 4) * (X ^ 2 - 9) ∧
  ((sunGraph 4 G20a).adjMatrix ℤ).charpoly = X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) ∧
  ((sunGraph 4 G20b).adjMatrix ℤ).charpoly = X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9)

/-- **Proposition 3.** `G` integral with `e` edges and an odd cycle; `g` the length of its
shortest odd cycles and `c_g` their number.  Every prime `q` with `(q-1) ∣ (g-1)` divides
`2g·c_g`; in particular `3 ∣ g·c_g`.  At least `(g-1)/2` integers `v ≥ 2` satisfy
`mult(v) ≠ mult(-v)`, and `2e ≥ ∑_{v=2}^{(g+1)/2} v²`. -/
def Proposition3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ),
    IsIntegralGraph G → IsOddGirth G g →
      (∀ q : ℕ, q.Prime → (q - 1) ∣ (g - 1) → q ∣ 2 * g * cycleCount G g) ∧
      3 ∣ g * cycleCount G g ∧
      (∃ S : Finset ℤ, (∀ v ∈ S, 2 ≤ v ∧ mult G (v : ℝ) ≠ mult G (-(v : ℝ))) ∧ (g - 1) / 2 ≤ S.card) ∧
      ∑ v ∈ Finset.Icc 2 ((g + 1) / 2), v ^ 2 ≤ 2 * G.edgeFinset.card

/-- `κ_b`: the product of the primes `q` with `(q-1) ∣ (b-1)` (for `b ≥ 2` all such `q` are `≤ b`). -/
def kappa (b : ℕ) : ℕ := ∏ q ∈ (Finset.range (b + 1)).filter (fun q => q.Prime ∧ (q - 1) ∣ (b - 1)), q

/-- **Corollary 3.1.** `G` integral unicyclic with `n` vertices, cycle of odd length `b`:
`κ_b ∣ 2b`, so `3 ∣ b`; the odd `b < 200` (here `3 ≤ b`) with `κ_b ∣ 2b` are exactly the listed
ones; if `b ≠ 3` then `b ≥ 15` and `n ≥ 102`. -/
def Corollary31 : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ),
    IsIntegralGraph G → IsUnicyclicWithCycle G b → Odd b →
      kappa b ∣ 2 * b ∧ 3 ∣ b ∧ (b ≠ 3 → 15 ≤ b ∧ 102 ≤ Fintype.card V)) ∧
  (∀ b : ℕ, 3 ≤ b → b < 200 → Odd b →
      (kappa b ∣ 2 * b ↔
        b ∈ ({3, 15, 27, 39, 63, 75, 87, 99, 123, 135, 147, 159, 183, 195} : Finset ℕ)))

/-- **Remark 3.2** (classical fact quoted there; von Staudt–Clausen): for odd `b ≥ 3`, `κ_b`
is the denominator of the Bernoulli number `B_{b-1}`. -/
def Remark32 : Prop :=
  ∀ b : ℕ, 3 ≤ b → Odd b → (_root_.bernoulli (b - 1)).den = kappa b

/-! ## 5. The cited results of Braga–Moraes–Santos [bms] that the proofs use -/

/-- [bms, Theorem 2.1], in the case used by the paper (generalized sun graphs): a pendant path
with at least three edges (a path on `t ≥ 3` vertices) forces an eigenvalue in `(1, 2cos(π/9)]`
and one in `[-2cos(π/9), -1)`. -/
def BMSTheorem21 : Prop :=
  ∀ (b : ℕ) (L : Fin b → List ℕ), 3 ≤ b → (∃ k, ∃ t ∈ L k, 3 ≤ t) →
    (∃ x ∈ spec (sunGraph b L), 1 < x ∧ x ≤ 2 * Real.cos (Real.pi / 9)) ∧
    (∃ x ∈ spec (sunGraph b L), -(2 * Real.cos (Real.pi / 9)) ≤ x ∧ x < -1)

/-- Consequence used in the proofs of Theorems 1 and 2: an integral generalized sun graph
carries only copies of `P_1` and `P_2`. -/
def OnlyP1P2 : Prop :=
  ∀ (b : ℕ) (L : Fin b → List ℕ), 3 ≤ b → IsIntegralGraph (sunGraph b L) → ∀ k, ∀ t ∈ L k, t ≤ 2

/-- [bms, Proposition 3.2]: the characteristic polynomial of `C_{6,1}(0,6,6,12,6,6)` is
`x^32 (x²-4)² (x²-9)² (x²-16)`, i.e. its spectrum is `{0^[32], ±2^[2], ±3^[2], ±4}`. -/
def BMSProposition32 : Prop :=
  ((sunGraph 6 C61).adjMatrix ℤ).charpoly =
    X ^ 32 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16)

/-! ## 6. Generalized sun graphs with pendant `P_1`, `P_2` only (Section 2 notation) -/

/-- `p_k` pendant vertices and `q_k` pendant paths `v_k w w'` at `v_k`. -/
def pq (b : ℕ) (p q : Fin b → ℕ) : Fin b → List ℕ :=
  fun k => List.replicate (p k) 1 ++ List.replicate (q k) 2

/-- The graph `G` of Section 2. -/
abbrev SG (b : ℕ) (p q : Fin b → ℕ) : SimpleGraph (SunV b (pq b p q)) := sunGraph b (pq b p q)

/-- `n = b + P + 2Q`. -/
def nOf (b : ℕ) (p q : Fin b → ℕ) : ℕ := b + ∑ k, p k + 2 * ∑ k, q k

/-- `K_p = {k : p_k > 0}`. -/
def Kp (b : ℕ) (p : Fin b → ℕ) : Finset (Fin b) := Finset.univ.filter (fun k => 0 < p k)
/-- `K_q = {k : q_k > 0}`. -/
def Kq (b : ℕ) (q : Fin b → ℕ) : Finset (Fin b) := Finset.univ.filter (fun k => 0 < q k)

/-- `θ` of one cycle vertex: `(2+p+q)(1+p+q) + 2q`. -/
def thetaV (p q : ℕ) : ℤ := (2 + p + q) * (1 + p + q) + 2 * q

/-- `A(C_b)` (Mathlib's `cycleGraph b`; for `b ≥ 3` the cycle `0 ~ 1 ~ ⋯ ~ b-1 ~ 0`). -/
def Cyc (b : ℕ) : Matrix (Fin b) (Fin b) ℝ := (SimpleGraph.cycleGraph b).adjMatrix ℝ

/-- `f_k(λ) = p_k/λ + q_k λ/(λ²-1)`. -/
def fk (b : ℕ) (p q : Fin b → ℕ) (x : ℝ) (k : Fin b) : ℝ :=
  (p k : ℝ) / x + (q k : ℝ) * x / (x ^ 2 - 1)

/-- `S(λ) = A(C_b) - λI + diag(f_k(λ))`. -/
def Smat (b : ℕ) (p q : Fin b → ℕ) (x : ℝ) : Matrix (Fin b) (Fin b) ℝ :=
  Cyc b - x • (1 : Matrix (Fin b) (Fin b) ℝ) + Matrix.diagonal (fk b p q x)

/-- `Z = ℤ_b ∖ K_q`, as an index type. -/
abbrev Zq (b : ℕ) (q : Fin b → ℕ) : Type := {k : Fin b // q k = 0}

/-- `R`: principal submatrix of `A(C_b) - I + diag(p_k)` on `Z`. -/
def Rmat (b : ℕ) (p q : Fin b → ℕ) : Matrix (Zq b q) (Zq b q) ℝ :=
  (Cyc b - 1 + Matrix.diagonal (fun k => (p k : ℝ))).submatrix Subtype.val Subtype.val

/-- `R'`: principal submatrix of `A(C_b) + I - diag(p_k)` on `Z`. -/
def R'mat (b : ℕ) (p q : Fin b → ℕ) : Matrix (Zq b q) (Zq b q) ℝ :=
  (Cyc b + 1 - Matrix.diagonal (fun k => (p k : ℝ))).submatrix Subtype.val Subtype.val

/-- `T_k = [[c_k, -1], [1, 0]]` with `c_k = m - f_k(m)`. -/
def Tk (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) (k : Fin b) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m - fk b p q m k, -1; 1, 0]

/-- `M = T_{b-1} ⋯ T_1 T_0`. -/
def Mono (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((List.finRange b).reverse.map (Tk b p q m)).prod

/-- `k ↦ k+1 (mod b)` and `k ↦ k-1 (mod b)`. -/
def nxt (b : ℕ) (k : Fin b) : Fin b := finRotate b k
def prv (b : ℕ) (k : Fin b) : Fin b := (finRotate b).symm k

/-- Gaps: `inGap b K k j` says that `j` lies strictly inside the gap of `K` that starts at
`k ∈ K`, i.e. `j = k + d (mod b)` with `1 ≤ d ≤ b` and none of `k+1, …, k+d` in `K`. -/
def inGap (b : ℕ) (K : Finset (Fin b)) (k j : Fin b) : Prop :=
  ∃ d ∈ Finset.Icc 1 b, ((finRotate b) ^ d) k = j ∧ ∀ d' ∈ Finset.Icc 1 d, ((finRotate b) ^ d') k ∉ K

/-- Number of gaps of `K` of even length: the gap starting at `k ∈ K` ends at the next element
`k + d (mod b)` of `K`, `1 ≤ d ≤ b` (for `|K| = 1` the only gap has length `b`). -/
def evenGaps (b : ℕ) (K : Finset (Fin b)) : ℕ :=
  (K.filter (fun k => ∃ d ∈ Finset.Icc 1 b, Even d ∧ ((finRotate b) ^ d) k ∈ K ∧
      ∀ d' ∈ Finset.Ico 1 d, ((finRotate b) ^ d') k ∉ K)).card

/-- `δ_0`. -/
def delta0 (b : ℕ) (p : Fin b → ℕ) : ℕ :=
  if Kp b p = ∅ then (if 4 ∣ b then 2 else 0) else evenGaps b (Kp b p)

/-- Matrix of the system defining `δ_ε`: `y_k = 0` for `k ∈ K_q`, and
`y_{k-1} + y_{k+1} - ε(1-p_k) y_k = 0` for `k ∉ K_q`. -/
def Wmat (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) : Matrix (Fin b) (Fin b) ℝ := fun k j =>
  if 0 < q k then (if j = k then 1 else 0)
  else (if j = prv b k then 1 else 0) + (if j = nxt b k then 1 else 0)
    - (if j = k then ε * (1 - (p k : ℝ)) else 0)

/-- `δ_ε`: dimension of the solution space of that system. -/
def deltaE (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))

/-- Contribution of the gap of `K_q` starting at `k`: dimension of the restrictions of the
solutions to the interior of that gap. -/
def gapDim (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) (k : Fin b) : ℕ :=
  Module.finrank ℝ ((LinearMap.ker (Matrix.toLin' (Wmat b p q ε))).map
    (LinearMap.funLeft ℝ ℝ (fun j : {j : Fin b // inGap b (Kq b q) k j} => j.val)))

/-- `Θ(G) = ∑_v d_v(d_v - 1)`. -/
def Theta {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  ∑ v, (G.degree v : ℤ) * ((G.degree v : ℤ) - 1)

/-- Setting-up facts of Section 2: `n = b + P + 2Q` vertices, `n` edges,
`Θ(G) = ∑_v d_v(d_v-1) = ∑_k ((2+p_k+q_k)(1+p_k+q_k) + 2q_k)`, and isomorphism classes
correspond to dihedral orbits of the sequences `((p_k,q_k))_k`. -/
def IsDihedral (b : ℕ) (σ : Fin b → Fin b) : Prop :=
  ∃ c : ℕ, (∀ k : Fin b, (σ k).val = (k.val + c) % b) ∨ (∀ k : Fin b, ((σ k).val + k.val) % b = c % b)

def SetupFacts : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    order b (pq b p q) = nOf b p q ∧
    (SG b p q).edgeFinset.card = nOf b p q ∧
    Theta (SG b p q) = ∑ k, thetaV (p k) (q k) ∧
    ∀ p' q' : Fin b → ℕ,
      (Nonempty (SG b p q ≃g SG b p' q') ↔
        ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ p' = p ∘ σ ∧ q' = q ∘ σ)

/-! ## 7. Section 2 lemmas -/

/-- **Lemma 2.1** (Schur reduction). -/
def Lemma21 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    (∀ x : ℝ, 1 < x →
      Ngt (SG b p q) x = nPos (Smat b p q x) ∧
      Nge (SG b p q) x = nPos (Smat b p q x) + nZero (Smat b p q x)) ∧
    (∀ x : ℝ, x < -1 →
      Nlt (SG b p q) x = nNeg (Smat b p q x) ∧
      Nle (SG b p q) x = nNeg (Smat b p q x) + nZero (Smat b p q x)) ∧
    (Kq b q).card + nPos (Rmat b p q) ≤ Ngt (SG b p q) 1 ∧
    (Kq b q).card + nNeg (R'mat b p q) ≤ Nlt (SG b p q) (-1)

/-- **Lemma 2.2** (multiplicities). -/
def Lemma22 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    -- (a)
    (∀ m : ℝ, m ≠ -1 → m ≠ 0 → m ≠ 1 →
      mult (SG b p q) m = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Mono b p q m - 1))) ∧
      mult (SG b p q) m ≤ 2 ∧
      (mult (SG b p q) m = 2 ↔ Mono b p q m = 1) ∧
      (mult (SG b p q) m = 1 ↔ Mono b p q m ≠ 1 ∧ (Mono b p q m).trace = 2)) ∧
    -- (b)
    mult (SG b p q) 0 + (Kp b p).card = ∑ k, p k + delta0 b p ∧
    -- (c)
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      mult (SG b p q) ε + (Kq b q).card = ∑ k, q k + deltaE b p q ε ∧
      ((Kq b q).Nonempty →
        deltaE b p q ε = ∑ k ∈ Kq b q, gapDim b p q ε k ∧ ∀ k ∈ Kq b q, gapDim b p q ε k ≤ 1) ∧
      (Kq b q = ∅ → deltaE b p q ε ≤ 2)) ∧
    -- (d)
    mult (SG b p q) 0 ≤ max (∑ k, p k) 2 ∧
    mult (SG b p q) 1 ≤ max (∑ k, q k) 2 ∧ mult (SG b p q) (-1) ≤ max (∑ k, q k) 2

/-- **Lemma 2.3** (closed walks), for any finite simple graph `H`. -/
def Lemma23 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    ((H.adjMatrix ℤ) ^ 2).trace = 2 * (H.edgeFinset.card : ℤ) ∧
    ((H.adjMatrix ℤ) ^ 4).trace = 2 * (H.edgeFinset.card : ℤ) +
        2 * ∑ v, (H.degree v : ℤ) * ((H.degree v : ℤ) - 1) + 8 * (cycleCount H 4 : ℤ) ∧
    ∀ g : ℕ, IsOddGirth H g →
      (∀ L : ℕ, Odd L → L < g → ((H.adjMatrix ℤ) ^ L).trace = 0) ∧
      ((H.adjMatrix ℤ) ^ g).trace = 2 * (g : ℤ) * (cycleCount H g : ℤ)

/-- Displayed identities (1) and (2), for integral `G` (P₁/P₂ data). -/
def Identities12 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → IsIntegralGraph (SG b p q) →
    ((spec (SG b p q)).map (fun x => x ^ 2)).sum = 2 * (nOf b p q : ℝ) ∧
    ((bigEigs (SG b p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
      2 * ((Theta (SG b p q) : ℤ) : ℝ) + 8 * (if b = 4 then (1 : ℝ) else 0) ∧
    (∀ L : ℕ, Odd L → 3 ≤ L → L < b → ((bigEigs (SG b p q)).map (fun x => x ^ L - x)).sum = 0) ∧
    (Odd b → ((bigEigs (SG b p q)).map (fun x => x ^ b - x)).sum = 2 * (b : ℝ))

/-- **Lemma 2.4** (admissible spectra). `G` integral and not a cycle. -/
def Lemma24 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → 0 < ∑ k, (p k + q k) → IsIntegralGraph (SG b p q) →
    -- (a)
    (∃ ρ ∈ spec (SG b p q), mult (SG b p q) ρ = 1 ∧ 3 ≤ ρ ∧
      ∀ x ∈ spec (SG b p q), |x| ≤ ρ ∧ x ^ 2 ≤ 2 * (nOf b p q : ℝ) ∧ (Odd b → -ρ < x)) ∧
    -- (b)
    (∀ x : ℝ, 2 ≤ |x| → mult (SG b p q) x ≤ 2) ∧
    -- (c)
    (Even b →
      (∀ x : ℝ, mult (SG b p q) x = mult (SG b p q) (-x)) ∧
      S2 (SG b p q) = (nOf b p q : ℝ) - mult (SG b p q) 1 ∧
      ((∑ k, p k + ∑ k, q k : ℕ) : ℝ) ≤ S2 (SG b p q) - b + 2) ∧
    (Odd b →
      ((∑ k, p k + ∑ k, q k : ℕ) : ℝ) ≤
        (1 / 2) * ((bigEigs (SG b p q)).map (fun x => x ^ 2)).sum - b + 2) ∧
    -- (d)
    (Even b →
      (nOf b p q ≤ 41 → Multiset.card (Bplus (SG b p q)) ≤ 4) ∧
      (nOf b p q ≤ 42 → Multiset.card (Bplus (SG b p q)) ≤ 5 ∧
        (Multiset.card (Bplus (SG b p q)) = 5 → Bplus (SG b p q) = {4, 3, 3, 2, 2})))

/-! ## 8. Section 4 lemmas -/

/-- **Lemma 4.1** (interlacing with the cycle). -/
def Lemma41 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    Ngt (SimpleGraph.cycleGraph b) 1 = 2 * ((b + 5) / 6) - 1 ∧
    Ngt (SimpleGraph.cycleGraph b) 1 ≤ Ngt (SG b p q) 1 ∧
    Nlt (SimpleGraph.cycleGraph b) (-1) ≤ Nlt (SG b p q) (-1) ∧
    (IsIntegralGraph (SG b p q) → 0 < ∑ k, (p k + q k) →
      2 * ((b + 5) / 6) - 1 ≤ Multiset.card (Bplus (SG b p q)) ∧
      (Even b →
        (nOf b p q ≤ 41 → b ≤ 12) ∧ (nOf b p q ≤ 42 → b ≤ 18) ∧
        (nOf b p q ≤ 42 → (b = 14 ∨ b = 16 ∨ b = 18) → Bplus (SG b p q) = {4, 3, 3, 2, 2})) ∧
      (nOf b p q ≤ 42 → b % 4 = 2 → b = 6 ∨ b = 10 ∨ b = 14 ∨ b = 18))

/-- **Lemma 4.2** (counting), `G` integral, `b` even, `s = |B^+|`. -/
def Lemma42 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → Even b → IsIntegralGraph (SG b p q) →
    (mult (SG b p q) 1 : ℝ) = nOf b p q - S2 (SG b p q) ∧
    (mult (SG b p q) (-1) : ℝ) = nOf b p q - S2 (SG b p q) ∧
    (mult (SG b p q) 0 : ℝ) = 2 * S2 (SG b p q) - nOf b p q - 2 * Multiset.card (Bplus (SG b p q)) ∧
    S2 (SG b p q) ≤ nOf b p q ∧
    (nOf b p q : ℝ) ≤ 2 * S2 (SG b p q) - 2 * Multiset.card (Bplus (SG b p q)) ∧
    2 * S2 (SG b p q) - nOf b p q - 2 * Multiset.card (Bplus (SG b p q)) ≤
      (max (∑ k, p k) 2 : ℕ)

/-- **Corollary 4.3.** No integral generalized sun graph with cycle length 14 or 18 has at
most 42 vertices (stated for arbitrary pendant paths, cycles included). -/
def Corollary43 : Prop :=
  ∀ (b : ℕ) (L : Fin b → List ℕ), (b = 14 ∨ b = 18) → IsIntegralGraph (sunGraph b L) →
    42 < order b L

/-- `σ(t)`: sum of the first `t` terms of `4,4,4,4,9,9,9,9,16,…`; `σ(t) = 0` for `t ≤ 0`. -/
def sigmaSq (t : ℤ) : ℕ := ∑ i ∈ Finset.range t.toNat, (i / 4 + 2) ^ 2

/-- **Lemma 4.4** (the rank bound). `G` integral and not a cycle, `r = #{λ : |λ| ≥ 2}`,
`r_0 = b + |K_p| - δ_0`. -/
def Lemma44 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → 0 < ∑ k, (p k + q k) → IsIntegralGraph (SG b p q) →
    let r : ℤ := Multiset.card (bigEigs (SG b p q))
    let r0 : ℤ := (b : ℤ) + (Kp b p).card - delta0 b p
    let n : ℤ := nOf b p q
    r = r0 + 2 * (Kq b q).card - deltaE b p q 1 - deltaE b p q (-1) ∧
    (b : ℤ) - 4 ≤ r ∧
    (sigmaSq r : ℤ) ≤ 2 * n ∧
    ((Kq b q).Nonempty → (sigmaSq r0 : ℤ) ≤ 2 * n - 2 * (Kq b q).card) ∧
    (Kq b q = ∅ → (sigmaSq (r0 - 4) : ℤ) ≤ 2 * n - 4) ∧
    (nOf b p q ≤ 42 → b ≤ 13)

/-! ## 9. Section 5 lemmas (soundness of the pruning) -/

/-- `X = {0, …, b-2}`. -/
def Xset (b : ℕ) : Finset (Fin b) := Finset.univ.filter (fun k => k.val + 2 ≤ b)

/-- Tridiagonal matrix indexed by `Y ⊆ X`: diagonal `t`, off-diagonal `1` at `(k, k+1)` and
`(k+1, k)` when both indices lie in `Y`, `0` elsewhere. -/
def tridiag {b : ℕ} (Y : Finset (Fin b)) (t : Fin b → ℝ) : Matrix Y Y ℝ := fun i j =>
  if i = j then t i.val
  else if i.val.val + 1 = j.val.val ∨ j.val.val + 1 = i.val.val then 1 else 0

/-- **Lemma 5.1** (monotone inertia bounds). -/
def Lemma51 : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    (∀ (m : ℝ) (t : Fin b → ℝ), 2 ≤ m → (∀ k ∈ Xset b, t k ≤ fk b p q m k - m) →
      nPos (tridiag (Xset b) t) ≤ Ngt (SG b p q) m ∧
      nPos (tridiag (Xset b) t) ≤ Nlt (SG b p q) (-m) ∧
      nPos (tridiag (Xset b) t) + nZero (tridiag (Xset b) t) ≤ Nge (SG b p q) m ∧
      nPos (tridiag (Xset b) t) + nZero (tridiag (Xset b) t) ≤ Nle (SG b p q) (-m)) ∧
    (∀ (Y : Finset (Fin b)) (t' : Fin b → ℝ), Y ⊆ Kq b q ∩ Xset b →
      (∀ k ∈ Xset b \ Y, t' k ≤ (p k : ℝ) - 1) →
      Y.card + nPos (tridiag (Xset b \ Y) t') ≤ Ngt (SG b p q) 1 ∧
      Y.card + nPos (tridiag (Xset b \ Y) t') ≤ Nlt (SG b p q) (-1))

/-- General symmetric tridiagonal `N × N` matrix with diagonal `t` and off-diagonal `a`
(`a k` in positions `(k, k+1)` and `(k+1, k)`). -/
def tridiagGen (N : ℕ) (t a : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if i = j then t i.val
  else if i.val + 1 = j.val then a i.val
  else if j.val + 1 = i.val then a j.val else 0

/-- The pivot recurrence of Lemma 5.2, counting the pivots of one sign (`pos = true`: positive
pivots; `pos = false`: negative pivots, "signs exchanged").  Entries are `(t_k, a_{k-1}²)`;
`prev = none` means the recurrence (re)starts, `d_k = t_k`; otherwise
`d_k = t_k - a_{k-1}²/d_{k-1}`.  A zero pivot is counted with the opposite sign, the next index
with the counted sign (no pivot computed), and the recurrence restarts two indices later. -/
def pivCount (pos : Bool) : List (ℝ × ℝ) → Option ℝ → ℕ
  | [], _ => 0
  | (t, a2) :: rest, prev =>
    let d : ℝ := match prev with
      | none => t
      | some dp => t - a2 / dp
    if d = 0 then
      match rest with
      | [] => 0
      | _ :: rest' => 1 + pivCount pos rest' none
    else
      (if (pos = true ∧ 0 < d) ∨ (pos = false ∧ d < 0) then 1 else 0) + pivCount pos rest (some d)

/-- **Lemma 5.2** (pivots with the zero-pivot rule give the inertia). -/
def Lemma52 : Prop :=
  ∀ (N : ℕ) (t a : ℕ → ℝ), (∀ k, k + 1 < N → a k ≠ 0) →
    pivCount true ((List.range N).map (fun k => (t k, if k = 0 then 0 else a (k - 1) ^ 2))) none =
        nPos (tridiagGen N t a) ∧
    pivCount false ((List.range N).map (fun k => (t k, if k = 0 then 0 else a (k - 1) ^ 2))) none =
        nNeg (tridiagGen N t a)

/-- `g(w) = (2+w)(1+w)`. -/
def gW (w : ℤ) : ℤ := (2 + w) * (1 + w)

/-- **Lemma 5.3** (the window).  `v_0, …, v_{d-1}` assigned (contributing `Θ_d` and `W`),
`r = b - d`; every completion with `n ≤ N` has
`Θ_d + 2r ≤ Θ(G) ≤ Θ_d + g(N - b - W) + 2(r - 1)`. -/
def Lemma53 : Prop :=
  ∀ (b d N : ℕ) (p q : Fin b → ℕ), d ≤ b → nOf b p q ≤ N →
    let thd : ℤ := ∑ k ∈ Finset.univ.filter (fun k : Fin b => k.val < d), thetaV (p k) (q k)
    let W : ℤ := ∑ k ∈ Finset.univ.filter (fun k : Fin b => k.val < d), ((p k : ℤ) + 2 * q k)
    let r : ℤ := (b : ℤ) - d
    let th : ℤ := ∑ k, thetaV (p k) (q k)
    thd + 2 * r ≤ th ∧ th ≤ thd + gW ((N : ℤ) - b - W) + 2 * (r - 1)

/-! ## 10. Un-numbered claims of Section 6 -/

/-- Section 6: with `r_max(n)` the largest `t` with `σ(t) ≤ 2n`, every integral generalized
sun graph (P₁/P₂ data) that is not a cycle has `b ≤ r_max(n) + 4` and `b ≤ (96n)^{1/3} + 7`. -/
def Section6Bound : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → 0 < ∑ k, (p k + q k) → IsIntegralGraph (SG b p q) →
    (∀ t : ℕ, 2 * nOf b p q < sigmaSq t → b < t + 4) ∧
    (b : ℝ) ≤ (96 * (nOf b p q : ℝ)) ^ ((1 : ℝ) / 3) + 7

/-- Section 6: an integral generalized sun graph that is not a cycle and has cycle length `3`
has at least `50` vertices ("by the searches of Section 5"). -/
def Section6CycleThree : Prop :=
  ∀ L : Fin 3 → List ℕ, 0 < pendantCount 3 L → IsIntegralGraph (sunGraph 3 L) → 50 ≤ order 3 L

/-! ## V2 coverage additions — author candidate, not frozen and not proved

These definitions supplement, and do not replace, the original 25 target Props.
The accompanying COVERAGE files distinguish paper mathematics from historical
run counters and flag every unresolved editorial/statement decision.
-/

/-- The three named representatives are pairwise non-isomorphic. -/
def Theorem2GraphsDistinct : Prop :=
  IsEmpty (sunGraph 4 G13 ≃g sunGraph 4 G20a) ∧
  IsEmpty (sunGraph 4 G13 ≃g sunGraph 4 G20b) ∧
  IsEmpty (sunGraph 4 G20a ≃g sunGraph 4 G20b)

/-- The 44-vertex positive control in Section 5.3. -/
def C42Ten : Fin 4 → List ℕ :=
  ![List.replicate 10 2, List.replicate 10 2, [], []]

/-- Complete integer characteristic polynomial and real spectrum, including
both multiplicities 19; this is a mathematical target, not a reported test run. -/
def ControlC42Ten : Prop :=
  order 4 C42Ten = 44 ∧ 0 < pendantCount 4 C42Ten ∧
  IsIntegralGraph (sunGraph 4 C42Ten) ∧
  ((sunGraph 4 C42Ten).adjMatrix ℤ).charpoly =
    X ^ 2 * (X ^ 2 - 1) ^ 19 * (X ^ 2 - 9) * (X ^ 2 - 16) ∧
  spec (sunGraph 4 C42Ten) =
    2 • ({0} : Multiset ℝ) + 19 • {1} + 19 • {-1} + {3, -3, 4, -4} ∧
  mult (sunGraph 4 C42Ten) 1 = 19 ∧ mult (sunGraph 4 C42Ten) (-1) = 19

/-- The integer-matrix congruence quoted in Remark 3.2. No symmetry,
integrality-of-spectrum or positive-dimension hypothesis is added. -/
def TracePowerPrime : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Matrix V V ℤ) (q : ℕ),
    q.Prime → (q : ℤ) ∣ ((A ^ q).trace - A.trace)

/-- Pendant-vertex data of the named 42-vertex example. -/
def C61P : Fin 6 → ℕ := ![0, 6, 6, 12, 6, 6]

/-- Six rotations; cardinality and the inclusion of all reflections are targets,
not properties assumed in this definition. -/
def C61Rotations : Finset (Fin 6 → ℕ) :=
  Finset.univ.image (fun c : Fin 6 => fun k : Fin 6 =>
    C61P (((finRotate 6) ^ c.val) k))

/-- The exact dihedral orbit and the full labeled parameter conclusion quoted
in the controls. The latter quantifies over arbitrary nonnegative p and q. -/
def C61OrbitSix : Prop :=
  C61 = pq 6 C61P (fun _ => 0) ∧
  (∀ p : Fin 6 → ℕ,
    (∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ p = C61P ∘ σ) ↔
      p ∈ C61Rotations) ∧
  C61Rotations.card = 6 ∧
  (∀ p q : Fin 6 → ℕ, 0 < ∑ k, (p k + q k) → nOf 6 p q ≤ 42 →
    (IsIntegralGraph (SG 6 p q) ↔ q = (fun _ => 0) ∧ p ∈ C61Rotations))

/-- Precise mathematical interpretation of the b=4, N=49 "same list" control:
the historical logs identify exactly these four isomorphism classes. -/
def ControlB4N49 : Prop :=
  ∀ L : Fin 4 → List ℕ, 0 < pendantCount 4 L → order 4 L ≤ 49 →
    (IsIntegralGraph (sunGraph 4 L) ↔
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten))

/-- Introduction background, over all finite unicyclic graphs, not just sun
graphs. Retention of this extra broad background contract needs independent review. -/
def IntroUnicyclic21 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V ≤ 21 → (∃ b : ℕ, IsUnicyclicWithCycle G b) →
    (IsIntegralGraph G ↔
      Nonempty (G ≃g SimpleGraph.cycleGraph 3) ∨
      Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨
      Nonempty (G ≃g SimpleGraph.cycleGraph 6) ∨
      Nonempty (G ≃g sunGraph 4 G13) ∨
      Nonempty (G ≃g sunGraph 4 G20a) ∨
      Nonempty (G ≃g sunGraph 4 G20b))

/-- Mathematical content of the introductory existence of infinite families:
unbounded orders ensure infinitely many isomorphism classes. Attribution to BDR
is bibliographic and is not encoded as a mathematical predicate. -/
def IntroInfiniteFamilies : Prop :=
  ∀ N : ℕ, ∃ (b : ℕ) (L : Fin b → List ℕ),
    3 ≤ b ∧ 0 < pendantCount b L ∧ N < order b L ∧
    IsUnicyclicWithCycle (sunGraph b L) b ∧ IsIntegralGraph (sunGraph b L)

/-- The particular BMS hexagonal family named by the introduction. -/
def HexagonFamily (a : ℕ) : Fin 6 → List ℕ :=
  ![[], List.replicate a 1, List.replicate a 1, List.replicate (2 * a) 1,
    List.replicate a 1, List.replicate a 1]

/-- Infinitely many genuine members of the cited hexagonal family, and 42 is
its attained minimum order. The a=0 bare cycle is explicitly outside this claim. -/
def IntroHexagonInfiniteFamily : Prop :=
  HexagonFamily 6 = C61 ∧ IsCounterexample 6 (HexagonFamily 6) ∧
  order 6 (HexagonFamily 6) = 42 ∧
  (∀ N : ℕ, ∃ a : ℕ, 1 ≤ a ∧ N < order 6 (HexagonFamily a) ∧
    IsUnicyclicWithCycle (sunGraph 6 (HexagonFamily a)) 6 ∧
    IsCounterexample 6 (HexagonFamily a)) ∧
  (∀ a : ℕ, 1 ≤ a → IsIntegralGraph (sunGraph 6 (HexagonFamily a)) →
    42 ≤ order 6 (HexagonFamily a))

/-- The square family mentioned with Veras's 68-vertex example. -/
def VerasSquare (a : ℕ) : Fin 4 → List ℕ :=
  ![[], List.replicate a 1, List.replicate (2 * a) 1, List.replicate a 1]

/-- The named graph is integral of order 68, and every genuine integral member
of its explicitly named family has at least 68 vertices. -/
def IntroVeras68 : Prop :=
  order 4 (VerasSquare 16) = 68 ∧
  IsIntegralGraph (sunGraph 4 (VerasSquare 16)) ∧
  (∀ a : ℕ, 1 ≤ a → IsIntegralGraph (sunGraph 4 (VerasSquare a)) →
    68 ≤ order 4 (VerasSquare a))

/-- A pendant path of t edges in an arbitrary graph. Vertex 0 is the attachment
vertex; every other path vertex has exactly its indicated path neighbors.
There is no connectedness requirement on the ambient graph. -/
def HasPendantPath {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ v : Fin (t + 1) → V, Function.Injective v ∧
    (∀ i : Fin t, G.Adj (v i.castSucc) (v i.succ)) ∧
    (∀ i : Fin (t + 1), 0 < i.val → ∀ w : V,
      (G.Adj (v i) w ↔ ∃ j : Fin (t + 1),
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ w = v j))

/-- Full general-graph background quotation from BMS Theorem 2.1, separate
from the unchanged sun-graph-specific BMSTheorem21 used by the main results. -/
def BMSTheorem21General : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ), 3 ≤ t → HasPendantPath G t →
    (∃ x ∈ spec G, 1 < x ∧ x ≤ 2 * Real.cos (Real.pi / 9)) ∧
    (∃ x ∈ spec G, -(2 * Real.cos (Real.pi / 9)) ≤ x ∧ x < -1) ∧
    ¬ IsIntegralGraph G

/-- Explicit safe form of the partial-assignment counting inequality described
for A v6. P and Q in the hypothesis/conclusion are genuinely partial sums. -/
def PartialAssignmentCounting : Prop :=
  ∀ (b d N : ℕ) (p q : Fin b → ℕ), 3 ≤ b → Even b → d ≤ b →
    IsIntegralGraph (SG b p q) → nOf b p q ≤ N →
    let I := Finset.univ.filter (fun k : Fin b => k.val < d)
    let Ppart : ℕ := ∑ k ∈ I, p k
    let Qpart : ℕ := ∑ k ∈ I, q k
    let s : ℝ := Multiset.card (Bplus (SG b p q))
    let nmax : ℝ := min (N : ℝ) (2 * S2 (SG b p q) - 2 * s)
    2 ≤ Ppart →
      2 * (Qpart : ℝ) ≤ 2 * nmax - b - 2 * S2 (SG b p q) + 2 * s

/-- Small exact arithmetic constants stated in the paper's hand arguments. -/
def ArithmeticConstants : Prop :=
  sigmaSq 9 = 68 ∧ sigmaSq 10 = 84 ∧ sigmaSq 11 = 100 ∧ sigmaSq 14 = 166 ∧
  kappa 5 = 30 ∧ kappa 7 = 42 ∧ kappa 9 = 30 ∧ kappa 11 = 66 ∧ kappa 13 = 2730 ∧
  (∑ v ∈ (Finset.Icc 2 8 : Finset ℕ), v ^ 2) = 203 ∧
  (4 ^ 2 + 2 * 3 ^ 2 + 2 * 2 ^ 2 : ℕ) = 42 ∧
  (5 ^ 2 + 4 ^ 2 + 2 * 3 ^ 2 + 2 * 2 ^ 2 : ℕ) = 67

/-- All labeled noncycle P1/P2 parameter sequences under the order budget.
No pruning, rotation rule, spectral test, or implementation counter is used. -/
def budgetPQ (b N : ℕ) : Set ((Fin b → ℕ) × (Fin b → ℕ)) :=
  {d | 0 < ∑ k, (d.1 k + d.2 k) ∧ nOf b d.1 d.2 ≤ N}

/-- Mathematical interpretation of the two explicitly exhaustive, unpruned,
unreduced triangular parameter counts, not the number of DFS nodes. -/
def LabeledBudgetCounts : Prop :=
  (budgetPQ 3 49).ncard = 3031469 ∧ (budgetPQ 3 42).ncard = 1246783


end

end BackfillPaper7.Challenge
