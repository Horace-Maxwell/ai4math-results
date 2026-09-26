import Mathlib

set_option autoImplicit false

/-!
# Negative answers to Problems 1 and 2 of Hak–Kozerenko–Oliynyk (median graphs)

A. Hak, S. Kozerenko, B. Oliynyk, "A note on the triameter of graphs",
Discrete Appl. Math. 309 (2022) 278–284, arXiv:2103.10806v1, Section 4 ("Open questions").

Definitions (HKO, Section 2), for a finite connected simple graph `G` with path metric `d`:
* `d(u,v,w) = d(u,v) + d(u,w) + d(v,w)`; `tr(G) = max {d(u,v,w) : u,v,w ∈ V(G)}`;
  a triple is *triametral* if `d(u,v,w) = tr(G)`;
* a pair is *diametral* if `d(u,v) = diam(G)`; a vertex is *peripheral* if it belongs to some
  diametral pair, i.e. its eccentricity equals the diameter;
* `[u,v] = {x : d(u,x) + d(x,v) = d(u,v)}`; `G` is *median* if it is connected and
  `|[u,v] ∩ [u,w] ∩ [v,w]| = 1` for every triple `u,v,w`.

Questions (HKO, Section 4, schemata for a graph class; paraphrased, see the LaTeX source
lines 435-488 for the exact wording):
* Question 3': must every triametral triple of vertices contain a peripheral vertex?
* Question 4 (Das): can every diametral pair of vertices be extended to a triametral triple?
* Problem 1: does Question 3' hold for median graphs?  Problem 2: does Question 4 hold for median
  graphs?

We use Mathlib's `SimpleGraph.dist`, `SimpleGraph.diam`, `SimpleGraph.eccent`,
`SimpleGraph.ediam` directly. Distances of the two concrete graphs are identified with explicit
tables through a general certificate lemma (`dist_eq_of_certificate`); every finite check is
done by `decide` / `decide +kernel` (kernel reduction, no `native_decide`).

Main results:
* `not_problem1Claim : ¬ Problem1Claim` — the 8-vertex median graph `G1` (three 4-cycles glued
  in a fan) has the triametral triple `{1,5,6}` with no peripheral vertex;
* `not_problem2Claim : ¬ Problem2Claim` — the 8-vertex median graph `G2` has the diametral pair
  `{5,7}` that extends to no triametral triple (not even with `z ∈ {5,7}` allowed);
* `not_problem2ClaimWeak` — `G2` also violates the weaker Question 4' (its peripheral vertex `5`
  lies in no triametral triple);
* also: the same `G1` refutes Question 3' with the pair-based definition of "peripheral"
  (`not_problem1ClaimPair`; the two definitions of "peripheral" agree on finite connected graphs,
  `isPeripheral_iff_isPeripheralPair`), and the alternative reading of the sentence before
  Problem 2 (Question 3 for median graphs, already refuted by HKO's Figure 2)
  (`not_question3_G1`).
-/

namespace HKOTriameter

open SimpleGraph Finset

section Defs

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- `d_G(u,v,w) = d_G(u,v) + d_G(u,w) + d_G(v,w)` (HKO, Section 2). -/
noncomputable def triDist (u v w : V) : ℕ :=
  G.dist u v + G.dist u w + G.dist v w

/-- The triameter `tr(G) = max {d_G(u,v,w) : u,v,w ∈ V(G)}` (HKO, Section 2): the maximum over
all ordered triples of vertices (repetitions allowed). -/
noncomputable def triameter : ℕ :=
  (univ : Finset (V × V × V)).sup fun t => triDist G t.1 t.2.1 t.2.2

/-- A triple is triametral if `d_G(u,v,w) = tr(G)`. -/
def IsTriametral (u v w : V) : Prop :=
  triDist G u v w = triameter G

/-- A pair is diametral if `d_G(u,v) = diam(G)` (Mathlib's `SimpleGraph.diam`). -/
def IsDiametral (u v : V) : Prop :=
  G.dist u v = G.diam

/-- A vertex is peripheral if its eccentricity equals the diameter
(Mathlib's `SimpleGraph.eccent` and `SimpleGraph.ediam`). -/
def IsPeripheral (u : V) : Prop :=
  G.eccent u = G.ediam

/-- HKO's literal wording: a vertex is peripheral if it belongs to some diametral pair. -/
def IsPeripheralPair (u : V) : Prop :=
  ∃ v, IsDiametral G u v

/-- `x ∈ [u,v]_G`, i.e. `d_G(u,x) + d_G(x,v) = d_G(u,v)`. -/
def InInterval (u v x : V) : Prop :=
  G.dist u x + G.dist x v = G.dist u v

/-- Median graph (HKO, Section 2, after Mulder): `G` is connected and
`|[u,v] ∩ [u,w] ∩ [v,w]| = 1` for every triple of vertices `u, v, w`. -/
def IsMedian : Prop :=
  G.Connected ∧
    ∀ u v w : V, ∃! x, InInterval G u v x ∧ InInterval G u w x ∧ InInterval G v w x

/-- Question 3' for the graph `G`: every triametral triple contains a peripheral vertex. -/
def Question3' : Prop :=
  ∀ a b c : V, IsTriametral G a b c → IsPeripheral G a ∨ IsPeripheral G b ∨ IsPeripheral G c

/-- Question 3' for `G` with HKO's pair-based definition of "peripheral". -/
def Question3'Pair : Prop :=
  ∀ a b c : V, IsTriametral G a b c →
    IsPeripheralPair G a ∨ IsPeripheralPair G b ∨ IsPeripheralPair G c

/-- Question 3 (Das) for `G`: every triametral triple contains a diametral pair. -/
def Question3 : Prop :=
  ∀ a b c : V, IsTriametral G a b c → IsDiametral G a b ∨ IsDiametral G a c ∨ IsDiametral G b c

/-- Question 4 (Das) for `G`: every diametral pair extends to a triametral triple. The third
vertex `z` is unrestricted (the weakest reading, hence the strongest refutation). -/
def Question4 : Prop :=
  ∀ x y : V, IsDiametral G x y → ∃ z, IsTriametral G x y z

/-- Question 4' for `G`: every peripheral vertex extends to a triametral triple (`y, z`
unrestricted: the weakest reading, hence the strongest refutation). -/
def Question4' : Prop :=
  ∀ x : V, IsPeripheral G x → ∃ y z, IsTriametral G x y z

end Defs

/-- The claim of HKO Problem 1: Question 3' holds for (finite) median graphs. -/
def Problem1Claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3' G

/-- Problem 1 with HKO's pair-based definition of "peripheral". -/
def Problem1ClaimPair : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3'Pair G

/-- The claim of HKO Problem 2: Question 4 holds for (finite) median graphs. -/
def Problem2Claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question4 G

/-! ## Distances from a certificate -/

section Certificate

variable {V : Type*} (G : SimpleGraph V)

/-- If `D` vanishes exactly on the diagonal, every off-diagonal value `D x y` drops by one
along some edge `x ~ z`, and `D` is 1-Lipschitz along edges in its first argument, then
`D` is the graph distance. -/
theorem dist_eq_of_certificate (D : V → V → ℕ)
    (hself : ∀ x, D x x = 0)
    (hzero : ∀ x y, D x y = 0 → x = y)
    (hstep : ∀ x y, D x y ≠ 0 → ∃ z, G.Adj x z ∧ D z y + 1 = D x y)
    (hlip : ∀ u v w, G.Adj u v → D u w ≤ D v w + 1) :
    ∀ x y, G.dist x y = D x y := by
  have hwalk : ∀ n : ℕ, ∀ x y, D x y = n → ∃ p : G.Walk x y, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro x y h
      obtain rfl := hzero x y h
      exact ⟨Walk.nil, rfl⟩
    | succ n ih =>
      intro x y h
      obtain ⟨z, hxz, hz⟩ := hstep x y (by omega)
      obtain ⟨p, hp⟩ := ih z y (by omega)
      exact ⟨Walk.cons hxz p, by simp [hp]⟩
  have hlow : ∀ x y (p : G.Walk x y), D x y ≤ p.length := by
    intro x y p
    induction p with
    | nil => simp [hself]
    | @cons u v w h p ih =>
      have := hlip u v w h
      simp only [Walk.length_cons]
      omega
  intro x y
  obtain ⟨p, hp⟩ := hwalk _ x y rfl
  apply le_antisymm
  · exact (dist_le p).trans hp.le
  · have hr : G.Reachable x y := ⟨p⟩
    obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    exact hq ▸ hlow x y q

theorem connected_of_dist [Nonempty V] (h : ∀ x y, x ≠ y → G.dist x y ≠ 0) : G.Connected := by
  refine ⟨fun x y => ?_⟩
  by_cases hxy : x = y
  · exact hxy ▸ Reachable.refl _
  · exact Reachable.of_dist_ne_zero (h x y hxy)

theorem edist_eq_dist (hc : G.Connected) (u v : V) : G.edist u v = G.dist u v :=
  ((hc.preconnected u v).coe_dist_eq_edist).symm

/-- For a finite connected graph, `diam = k` follows from "all distances `≤ k`" and "some
distance `= k`". -/
theorem diam_eq_of_bounds [Fintype V] [Nonempty V] (hc : G.Connected) (k : ℕ)
    (hle : ∀ u v, G.dist u v ≤ k) (a b : V) (hab : G.dist a b = k) : G.diam = k := by
  have hne : G.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp hc
  apply le_antisymm
  · obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    exact huv ▸ hle u v
  · exact hab ▸ dist_le_diam hne

theorem ediam_eq_diam [Fintype V] [Nonempty V] (hc : G.Connected) :
    G.ediam = (G.diam : ℕ∞) := by
  have hne : G.ediam ≠ ⊤ := (connected_iff_ediam_ne_top).mp hc
  rw [diam, ENat.natCast_toNat hne]

/-- On a finite connected graph the two definitions of "peripheral" agree: eccentricity equal to
the diameter iff the vertex belongs to a diametral pair (HKO's wording). -/
theorem isPeripheral_iff_isPeripheralPair [Fintype V] [Nonempty V] (hc : G.Connected) (u : V) :
    IsPeripheral G u ↔ IsPeripheralPair G u := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
    refine ⟨v, ?_⟩
    rw [h, ediam_eq_diam G hc, edist_eq_dist G hc] at hv
    exact_mod_cast hv
  · rintro ⟨v, hv⟩
    have hv' : G.dist u v = G.diam := hv
    apply le_antisymm eccent_le_ediam
    rw [ediam_eq_diam G hc, ← hv', ← edist_eq_dist G hc]
    exact edist_le_eccent

/-- A vertex all of whose distances are `< diam` is not peripheral (eccentricity version). -/
theorem not_isPeripheral_of_lt [Fintype V] [Nonempty V] (hc : G.Connected) (u : V)
    (h : ∀ v, G.dist u v < G.diam) : ¬ IsPeripheral G u := by
  intro hp
  have hd : 0 < G.diam := lt_of_le_of_lt (Nat.zero_le _) (h u)
  have h1 : G.eccent u ≤ ((G.diam - 1 : ℕ) : ℕ∞) := by
    rw [eccent_le_iff]
    intro v
    rw [edist_eq_dist G hc]
    exact Nat.cast_le.mpr (by have := h v; omega)
  rw [hp, ediam_eq_diam G hc] at h1
  have := Nat.cast_le.mp h1
  omega

end Certificate

/-! ## The graph `G1` (Problem 1) -/

/-- Edge list of `G1`: the 4-cycles `0-1-3-2`, `0-2-5-4`, `0-4-7-6` glued in a fan at `0`. -/
def g1Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 4), (0, 6), (1, 3), (2, 3), (2, 5), (4, 5), (4, 7), (6, 7)]

/-- The graph `G1` on `Fin 8`. -/
def G1 : SimpleGraph (Fin 8) where
  Adj i j := (i.val, j.val) ∈ g1Edges ∨ (j.val, i.val) ∈ g1Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G1.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ g1Edges ∨ (j.val, i.val) ∈ g1Edges))

/-- Distance table of `G1` (row `i`, column `j`). -/
def d1Table : List (List ℕ) :=
  [[0, 1, 1, 2, 1, 2, 1, 2],
   [1, 0, 2, 1, 2, 3, 2, 3],
   [1, 2, 0, 1, 2, 1, 2, 3],
   [2, 1, 1, 0, 3, 2, 3, 4],
   [1, 2, 2, 3, 0, 1, 2, 1],
   [2, 3, 1, 2, 1, 0, 3, 2],
   [1, 2, 2, 3, 2, 3, 0, 1],
   [2, 3, 3, 4, 1, 2, 1, 0]]

def D1 (i j : Fin 8) : ℕ := (d1Table.getD i.val []).getD j.val 0

theorem G1_dist : ∀ x y, G1.dist x y = D1 x y :=
  dist_eq_of_certificate G1 D1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem G1_connected : G1.Connected :=
  connected_of_dist G1 fun x y hxy => by
    rw [G1_dist]
    revert x y
    decide

theorem G1_median : IsMedian G1 := by
  refine ⟨G1_connected, ?_⟩
  have key : ∀ u v w : Fin 8, ∃ x,
      (D1 u x + D1 x v = D1 u v ∧ D1 u x + D1 x w = D1 u w ∧ D1 v x + D1 x w = D1 v w) ∧
      ∀ y, (D1 u y + D1 y v = D1 u v ∧ D1 u y + D1 y w = D1 u w ∧ D1 v y + D1 y w = D1 v w) →
        y = x := by
    decide +kernel
  intro u v w
  simp only [InInterval, G1_dist]
  exact key u v w

theorem G1_diam : G1.diam = 4 :=
  diam_eq_of_bounds G1 G1_connected 4
    (fun u v => by rw [G1_dist]; revert u v; decide) 3 7 (by rw [G1_dist]; decide)

theorem G1_triDist (u v w : Fin 8) : triDist G1 u v w = D1 u v + D1 u w + D1 v w := by
  simp only [triDist, G1_dist]

theorem G1_triameter : triameter G1 = 8 := by
  have hle : ∀ a b c : Fin 8, D1 a b + D1 a c + D1 b c ≤ 8 := by decide +kernel
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    rw [G1_triDist]
    exact hle a b c
  · have h : triDist G1 1 5 6 = 8 := by rw [G1_triDist]; decide
    calc (8 : ℕ) = triDist G1 1 5 6 := h.symm
      _ ≤ triameter G1 :=
        Finset.le_sup (f := fun t : Fin 8 × Fin 8 × Fin 8 => triDist G1 t.1 t.2.1 t.2.2)
          (Finset.mem_univ ((1, 5, 6) : Fin 8 × Fin 8 × Fin 8))

/-- `{1,5,6}` is a triametral triple of `G1` (pairwise distances `3, 3, 2`). -/
theorem G1_triametral_156 : IsTriametral G1 1 5 6 := by
  rw [IsTriametral, G1_triameter, G1_triDist]
  decide

/-- None of `1, 5, 6` is peripheral in `G1` (their eccentricities are `3 < 4 = diam`). -/
theorem G1_not_peripheral_156 :
    ¬ IsPeripheral G1 1 ∧ ¬ IsPeripheral G1 5 ∧ ¬ IsPeripheral G1 6 := by
  have h : ∀ u : Fin 8, u = 1 ∨ u = 5 ∨ u = 6 → ∀ v, D1 u v < 4 := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply not_isPeripheral_of_lt G1 G1_connected
    intro v
    rw [G1_dist, G1_diam]
    exact h _ (by decide) v

theorem G1_not_peripheralPair_156 :
    ¬ IsPeripheralPair G1 1 ∧ ¬ IsPeripheralPair G1 5 ∧ ¬ IsPeripheralPair G1 6 := by
  have h : ∀ u : Fin 8, u = 1 ∨ u = 5 ∨ u = 6 → ∀ v, D1 u v ≠ 4 := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
  · rintro ⟨v, hv⟩
    rw [IsDiametral, G1_dist, G1_diam] at hv
    exact h _ (by decide) v hv

/-- Question 3' fails for `G1`, witnessed by the triple `{1,5,6}` of distinct vertices. -/
theorem G1_counterexample :
    IsMedian G1 ∧ (1 : Fin 8) ≠ 5 ∧ (1 : Fin 8) ≠ 6 ∧ (5 : Fin 8) ≠ 6 ∧
      IsTriametral G1 1 5 6 ∧ ¬ IsPeripheral G1 1 ∧ ¬ IsPeripheral G1 5 ∧
        ¬ IsPeripheral G1 6 :=
  ⟨G1_median, by decide, by decide, by decide, G1_triametral_156, G1_not_peripheral_156⟩

theorem not_question3'_G1 : ¬ Question3' G1 := by
  intro h
  obtain ⟨h1, h5, h6⟩ := G1_not_peripheral_156
  rcases h 1 5 6 G1_triametral_156 with h' | h' | h'
  · exact h1 h'
  · exact h5 h'
  · exact h6 h'

theorem not_question3'Pair_G1 : ¬ Question3'Pair G1 := by
  intro h
  obtain ⟨h1, h5, h6⟩ := G1_not_peripheralPair_156
  rcases h 1 5 6 G1_triametral_156 with h' | h' | h'
  · exact h1 h'
  · exact h5 h'
  · exact h6 h'

/-- `G1` also violates Question 3 (the triple `{1,5,6}` contains no diametral pair). -/
theorem not_question3_G1 : ¬ Question3 G1 := by
  intro h
  have hd : ∀ u v : Fin 8, IsDiametral G1 u v ↔ D1 u v = 4 := by
    intro u v; rw [IsDiametral, G1_dist, G1_diam]
  rcases h 1 5 6 G1_triametral_156 with h' | h' | h' <;>
  · rw [hd] at h'
    revert h'
    decide

/-- **HKO Problem 1 has a negative answer**: Question 3' fails for median graphs. -/
theorem not_problem1Claim : ¬ Problem1Claim := fun h => not_question3'_G1 (h (Fin 8) G1 G1_median)

theorem not_problem1ClaimPair : ¬ Problem1ClaimPair := fun h =>
  not_question3'Pair_G1 (h (Fin 8) G1 G1_median)

/-! ### Sanity checks on the definitions (non-vacuity) -/

/-- The peripheral vertices `3, 7` of `G1` are recognised as peripheral by both definitions. -/
example : IsPeripheral G1 3 ∧ IsPeripheral G1 7 ∧ IsPeripheralPair G1 3 := by
  have h37 : IsDiametral G1 3 7 := by rw [IsDiametral, G1_dist, G1_diam]; decide
  have h73 : IsDiametral G1 7 3 := by rw [IsDiametral, G1_dist, G1_diam]; decide
  exact ⟨(isPeripheral_iff_isPeripheralPair G1 G1_connected 3).mpr ⟨7, h37⟩,
    (isPeripheral_iff_isPeripheralPair G1 G1_connected 7).mpr ⟨3, h73⟩, ⟨7, h37⟩⟩

/-- `C6` (the 6-cycle `0-1-2-3-4-5-0`) is not median: the triple `0, 2, 4` has no median.
This checks that `IsMedian` is not vacuous. -/
def c6Edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]

def C6 : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ c6Edges ∨ (j.val, i.val) ∈ c6Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel C6.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ c6Edges ∨ (j.val, i.val) ∈ c6Edges))

def D6 (i j : Fin 6) : ℕ := min ((i.val + 6 - j.val) % 6) ((j.val + 6 - i.val) % 6)

theorem C6_dist : ∀ x y, C6.dist x y = D6 x y :=
  dist_eq_of_certificate C6 D6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem C6_not_median : ¬ IsMedian C6 := by
  rintro ⟨_, h⟩
  obtain ⟨x, hx, -⟩ := h 0 2 4
  simp only [InInterval, C6_dist] at hx
  revert x
  decide

/-! ## The graph `G2` (Problem 2) -/

/-- Edge list of `G2`: the 4-cycle `0-2-5-3`, a leaf `1` at `2`, a leaf `4` at `3`, and the
path `0-6-7`. -/
def g2Edges : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 6), (1, 2), (2, 5), (3, 4), (3, 5), (6, 7)]

/-- The graph `G2` on `Fin 8`. -/
def G2 : SimpleGraph (Fin 8) where
  Adj i j := (i.val, j.val) ∈ g2Edges ∨ (j.val, i.val) ∈ g2Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ g2Edges ∨ (j.val, i.val) ∈ g2Edges))

/-- Distance table of `G2` (row `i`, column `j`). -/
def d2Table : List (List ℕ) :=
  [[0, 2, 1, 1, 2, 2, 1, 2],
   [2, 0, 1, 3, 4, 2, 3, 4],
   [1, 1, 0, 2, 3, 1, 2, 3],
   [1, 3, 2, 0, 1, 1, 2, 3],
   [2, 4, 3, 1, 0, 2, 3, 4],
   [2, 2, 1, 1, 2, 0, 3, 4],
   [1, 3, 2, 2, 3, 3, 0, 1],
   [2, 4, 3, 3, 4, 4, 1, 0]]

def D2 (i j : Fin 8) : ℕ := (d2Table.getD i.val []).getD j.val 0

theorem G2_dist : ∀ x y, G2.dist x y = D2 x y :=
  dist_eq_of_certificate G2 D2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem G2_connected : G2.Connected :=
  connected_of_dist G2 fun x y hxy => by
    rw [G2_dist]
    revert x y
    decide

theorem G2_median : IsMedian G2 := by
  refine ⟨G2_connected, ?_⟩
  have key : ∀ u v w : Fin 8, ∃ x,
      (D2 u x + D2 x v = D2 u v ∧ D2 u x + D2 x w = D2 u w ∧ D2 v x + D2 x w = D2 v w) ∧
      ∀ y, (D2 u y + D2 y v = D2 u v ∧ D2 u y + D2 y w = D2 u w ∧ D2 v y + D2 y w = D2 v w) →
        y = x := by
    decide +kernel
  intro u v w
  simp only [InInterval, G2_dist]
  exact key u v w

theorem G2_diam : G2.diam = 4 :=
  diam_eq_of_bounds G2 G2_connected 4
    (fun u v => by rw [G2_dist]; revert u v; decide) 5 7 (by rw [G2_dist]; decide)

theorem G2_triDist (u v w : Fin 8) : triDist G2 u v w = D2 u v + D2 u w + D2 v w := by
  simp only [triDist, G2_dist]

theorem G2_triameter : triameter G2 = 12 := by
  have hle : ∀ a b c : Fin 8, D2 a b + D2 a c + D2 b c ≤ 12 := by decide +kernel
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    rw [G2_triDist]
    exact hle a b c
  · have h : triDist G2 1 4 7 = 12 := by rw [G2_triDist]; decide
    calc (12 : ℕ) = triDist G2 1 4 7 := h.symm
      _ ≤ triameter G2 :=
        Finset.le_sup (f := fun t : Fin 8 × Fin 8 × Fin 8 => triDist G2 t.1 t.2.1 t.2.2)
          (Finset.mem_univ ((1, 4, 7) : Fin 8 × Fin 8 × Fin 8))

/-- `{5,7}` is a diametral pair of `G2`. -/
theorem G2_diametral_57 : IsDiametral G2 5 7 := by
  rw [IsDiametral, G2_diam, G2_dist]
  decide

/-- No vertex `z` (including `z = 5` or `z = 7`) makes `{5,7,z}` triametral in `G2`:
`d(5,7,z) ≤ 10 < 12 = tr(G2)`. -/
theorem G2_not_extendable_57 : ∀ z, ¬ IsTriametral G2 5 7 z := by
  have h : ∀ z : Fin 8, D2 5 7 + D2 5 z + D2 7 z ≤ 10 := by decide
  intro z hz
  rw [IsTriametral, G2_triameter, G2_triDist] at hz
  have := h z
  omega

theorem G2_counterexample :
    IsMedian G2 ∧ IsDiametral G2 5 7 ∧ ∀ z, ¬ IsTriametral G2 5 7 z :=
  ⟨G2_median, G2_diametral_57, G2_not_extendable_57⟩

theorem not_question4_G2 : ¬ Question4 G2 := fun h => by
  obtain ⟨z, hz⟩ := h 5 7 G2_diametral_57
  exact G2_not_extendable_57 z hz

/-- **HKO Problem 2 has a negative answer**: Question 4 fails for median graphs. -/
theorem not_problem2Claim : ¬ Problem2Claim := fun h => not_question4_G2 (h (Fin 8) G2 G2_median)

/-- `G2` also violates the weaker Question 4': the peripheral vertex `5` (with `d(5,7) = 4`) lies in
no triametral triple (every triple through `5` has sum `≤ 10 < 12`). -/
theorem not_question4'_G2 : ¬ Question4' G2 := by
  intro h
  have hp : IsPeripheral G2 5 :=
    (isPeripheral_iff_isPeripheralPair G2 G2_connected 5).mpr ⟨7, G2_diametral_57⟩
  obtain ⟨y, z, hyz⟩ := h 5 hp
  have hb : ∀ y z : Fin 8, D2 5 y + D2 5 z + D2 y z ≤ 10 := by decide
  rw [IsTriametral, G2_triameter, G2_triDist] at hyz
  have := hb y z
  omega

/-- The weaker form of Problem 2 (Question 4' for median graphs) also fails. -/
def Problem2ClaimWeak : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question4' G

theorem not_problem2ClaimWeak : ¬ Problem2ClaimWeak := fun h =>
  not_question4'_G2 (h (Fin 8) G2 G2_median)

end HKOTriameter

#print axioms HKOTriameter.not_problem1Claim
#print axioms HKOTriameter.not_problem1ClaimPair
#print axioms HKOTriameter.not_problem2Claim
#print axioms HKOTriameter.not_problem2ClaimWeak
#print axioms HKOTriameter.G1_counterexample
#print axioms HKOTriameter.G2_counterexample
#print axioms HKOTriameter.not_question3_G1
#print axioms HKOTriameter.isPeripheral_iff_isPeripheralPair
#print axioms HKOTriameter.dist_eq_of_certificate
#print axioms HKOTriameter.C6_not_median
