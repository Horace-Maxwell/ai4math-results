import Research.HKOTriameter

set_option autoImplicit false

/-!
# HKO Problem 3 (distance-hereditary graphs): an affirmative answer, via the four-point condition

Hak–Kozerenko–Oliynyk (arXiv:2103.10806v1, Section 4), Problem 3 (paraphrased): for a
distance-hereditary graph, does at least one of Questions 3' and 4 hold?

Bandelt and Mulder (J. Combin. Theory Ser. B 41 (1986) 182–208; statement as quoted e.g. in
Dragan–Leitert, arXiv:1511.05109, Proposition "(4-point condition)") characterise the connected
distance-hereditary graphs by the **four-point condition**: for any four vertices `u, v, w, x`, at
least two of the sums `d(u,v)+d(w,x)`, `d(u,w)+d(v,x)`, `d(u,x)+d(v,w)` are equal, and if the two
smaller sums are equal then the largest exceeds them by at most `2`. Equivalently (`FP` below):
some two of the three sums are equal and the third is at most their common value plus `2`.

We do **not** formalise the Bandelt–Mulder theorem; we take the four-point condition as the
hypothesis (`FourPointBM`). Only its "distance-hereditary ⇒ four-point" direction is needed to
transfer the result to distance-hereditary graphs.

Main results (for every finite connected graph satisfying the four-point condition):
* `extends_of_no_diametral`: if `{a,b,c}` is triametral and contains no diametral pair, then every
  diametral pair `{x,y}` extends to a triametral triple by one of `a, b, c`;
* `question3_or_question4`: Question 3 or Question 4 holds;
* `problem3_fourPoint`: Question 3' or Question 4 holds (HKO Problem 3, affirmative).
The combinatorial core `core` is a statement about ten natural numbers, proved by `omega`.
Sanity checks: HKO's Figure 1 graphs `G` and `H` satisfy the four-point condition; `G` violates
Question 3' (and 3) but satisfies Question 4, `H` violates Question 4 but satisfies Question 3.
-/

namespace HKOTriameter

open SimpleGraph Finset

/-- The sharp four-point relation for three sums: two of them are equal and the third is at most
their common value plus `2`. -/
def FP (A B C : ℕ) : Prop :=
  (A = B ∧ C ≤ A + 2) ∨ (A = C ∧ B ≤ A + 2) ∨ (B = C ∧ A ≤ B + 2)

instance (A B C : ℕ) : Decidable (FP A B C) := by unfold FP; infer_instance

/-- The Bandelt–Mulder four-point condition for the path metric of `G`. -/
def FourPointBM {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w x : V,
    FP (G.dist u v + G.dist w x) (G.dist u w + G.dist v x) (G.dist u x + G.dist v w)

/-- **Combinatorial core.** `D` is the diameter, `e_{uv}` the distances inside the triple (all
`< D`), `p_u = d(x,u)`, `q_u = d(y,u)` for a diametral pair `x, y`. The three four-point relations
on `{x,y,u,v}` are incompatible with `d(u,x,y) < e_ab + e_ac + e_bc` for all three `u`. -/
theorem core (D eab eac ebc pa pb pc qa qb qc : ℕ)
    (hab : eab + 1 ≤ D) (hac : eac + 1 ≤ D) (hbc : ebc + 1 ≤ D)
    (fab : FP (D + eab) (pa + qb) (pb + qa))
    (fac : FP (D + eac) (pa + qc) (pc + qa))
    (fbc : FP (D + ebc) (pb + qc) (pc + qb))
    (na : D + pa + qa + 1 ≤ eab + eac + ebc)
    (nb : D + pb + qb + 1 ≤ eab + eac + ebc)
    (nc : D + pc + qc + 1 ≤ eab + eac + ebc) : False := by
  unfold FP at fab fac fbc
  rcases fab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases fac with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases fbc with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  omega

section General

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem triDist_le_triameter (u v w : V) : triDist G u v w ≤ triameter G :=
  Finset.le_sup (f := fun t : V × V × V => triDist G t.1 t.2.1 t.2.2)
    (Finset.mem_univ (u, v, w))

/-- **Theorem B.** In a finite connected graph with the four-point condition, if the triametral
triple `{a,b,c}` contains no diametral pair, then every diametral pair `{x,y}` is extended to a
triametral triple by `a`, `b` or `c`. -/
theorem extends_of_no_diametral (hfp : FourPointBM G)
    (a b c : V) (htri : IsTriametral G a b c)
    (hab : G.dist a b < G.diam) (hac : G.dist a c < G.diam) (hbc : G.dist b c < G.diam)
    (x y : V) (hxy : IsDiametral G x y) :
    IsTriametral G x y a ∨ IsTriametral G x y b ∨ IsTriametral G x y c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨na, nb, nc⟩ := hcon
  have ha := triDist_le_triameter G x y a
  have hb := triDist_le_triameter G x y b
  have hc := triDist_le_triameter G x y c
  simp only [IsTriametral, triDist] at na nb nc htri ha hb hc
  unfold IsDiametral at hxy
  have f1 := hfp x y a b
  have f2 := hfp x y a c
  have f3 := hfp x y b c
  rw [hxy] at f1 f2 f3 na nb nc ha hb hc
  exact core G.diam (G.dist a b) (G.dist a c) (G.dist b c) (G.dist x a) (G.dist x b)
    (G.dist x c) (G.dist y a) (G.dist y b) (G.dist y c) (by omega) (by omega) (by omega)
    f1 f2 f3 (by omega) (by omega) (by omega)

/-- **Corollary B1.** A finite connected graph with the four-point condition satisfies Question 3
or Question 4. -/
theorem question3_or_question4 (hconn : G.Connected) (hfp : FourPointBM G) :
    Question3 G ∨ Question4 G := by
  have := hconn.nonempty
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  by_cases h3 : Question3 G
  · exact Or.inl h3
  · right
    intro x y hxy
    unfold Question3 at h3
    push Not at h3
    obtain ⟨a, b, c, htri, hab, hac, hbc⟩ := h3
    have lab : G.dist a b < G.diam := lt_of_le_of_ne (dist_le_diam hne) hab
    have lac : G.dist a c < G.diam := lt_of_le_of_ne (dist_le_diam hne) hac
    have lbc : G.dist b c < G.diam := lt_of_le_of_ne (dist_le_diam hne) hbc
    rcases extends_of_no_diametral G hfp a b c htri lab lac lbc x y hxy with h | h | h
    · exact ⟨a, h⟩
    · exact ⟨b, h⟩
    · exact ⟨c, h⟩

/-- Question 3 implies Question 3' (a vertex of a diametral pair is peripheral). -/
theorem question3'_of_question3 (hconn : G.Connected) (h : Question3 G) : Question3' G := by
  have := hconn.nonempty
  intro a b c habc
  rcases h a b c habc with h1 | h1 | h1
  · exact Or.inl ((isPeripheral_iff_isPeripheralPair G hconn a).mpr ⟨b, h1⟩)
  · exact Or.inl ((isPeripheral_iff_isPeripheralPair G hconn a).mpr ⟨c, h1⟩)
  · exact Or.inr (Or.inl ((isPeripheral_iff_isPeripheralPair G hconn b).mpr ⟨c, h1⟩))

/-- **Corollary B2 (HKO Problem 3, affirmative).** Every finite connected graph satisfying the
Bandelt–Mulder four-point condition (by Bandelt–Mulder: every connected distance-hereditary
graph) satisfies Question 3' or Question 4. -/
theorem problem3_fourPoint (hconn : G.Connected) (hfp : FourPointBM G) :
    Question3' G ∨ Question4 G :=
  (question3_or_question4 G hconn hfp).imp (question3'_of_question3 G hconn) id

end General

/-- HKO Problem 3, for the class of finite connected graphs with the four-point condition. -/
def Problem3ClaimFP : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.Connected → FourPointBM G → Question3' G ∨ Question4 G

theorem problem3ClaimFP : Problem3ClaimFP := fun _ _ G hconn hfp =>
  problem3_fourPoint G hconn hfp

/-! ## Sanity checks: HKO's Figure 1 graphs -/

/-- HKO Figure 1, graph `G`: `y=0, m=1, a=2, b=3, c=4, x=5`; edges `y–m`, `m–a,b,c`, `x–a,b,c`. -/
def f1gEdges : List (ℕ × ℕ) := [(0, 1), (1, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]

def F1G : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ f1gEdges ∨ (j.val, i.val) ∈ f1gEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel F1G.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ f1gEdges ∨ (j.val, i.val) ∈ f1gEdges))

def dF1GTable : List (List ℕ) :=
  [[0, 1, 2, 2, 2, 3],
   [1, 0, 1, 1, 1, 2],
   [2, 1, 0, 2, 2, 1],
   [2, 1, 2, 0, 2, 1],
   [2, 1, 2, 2, 0, 1],
   [3, 2, 1, 1, 1, 0]]

def DF1G (i j : Fin 6) : ℕ := (dF1GTable.getD i.val []).getD j.val 0

theorem F1G_dist : ∀ x y, F1G.dist x y = DF1G x y :=
  dist_eq_of_certificate F1G DF1G (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem F1G_connected : F1G.Connected :=
  connected_of_dist F1G fun x y hxy => by rw [F1G_dist]; revert x y; decide

theorem F1G_fourPoint : FourPointBM F1G := by
  intro u v w x
  simp only [F1G_dist]
  revert u v w x
  decide +kernel

theorem F1G_diam : F1G.diam = 3 :=
  diam_eq_of_bounds F1G F1G_connected 3 (fun u v => by rw [F1G_dist]; revert u v; decide)
    0 5 (by rw [F1G_dist]; decide)

theorem F1G_triameter : triameter F1G = 6 := by
  have hle : ∀ a b c : Fin 6, DF1G a b + DF1G a c + DF1G b c ≤ 6 := by decide +kernel
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    simp only [triDist, F1G_dist]
    exact hle a b c
  · have h : triDist F1G 2 3 4 = 6 := by simp only [triDist, F1G_dist]; decide
    calc (6 : ℕ) = triDist F1G 2 3 4 := h.symm
      _ ≤ triameter F1G := triDist_le_triameter F1G 2 3 4

/-- HKO: in Figure 1 `G`, the triametral triple `a,b,c` contains no peripheral vertex. -/
theorem F1G_not_question3' : ¬ Question3' F1G := by
  intro h
  have ht : IsTriametral F1G 2 3 4 := by
    rw [IsTriametral, F1G_triameter]; simp only [triDist, F1G_dist]; decide
  have hnp : ∀ u : Fin 6, (u = 2 ∨ u = 3 ∨ u = 4) → ¬ IsPeripheral F1G u := by
    intro u hu
    apply not_isPeripheral_of_lt F1G F1G_connected
    intro v
    rw [F1G_dist, F1G_diam]
    revert v
    rcases hu with rfl | rfl | rfl <;> decide
  rcases h 2 3 4 ht with h' | h' | h'
  · exact hnp 2 (by decide) h'
  · exact hnp 3 (by decide) h'
  · exact hnp 4 (by decide) h'

/-- HKO Figure 1 `G` (`K_{2,3}` plus a pendant vertex) is **not** a median graph: the triple
`a, b, c` has the two medians `m` and `x`. (A Wikipedia figure caption calls this graph median; it
is modular but not median, so it is not a median counterexample to Problem 1.) -/
theorem F1G_not_median : ¬ IsMedian F1G := by
  rintro ⟨_, h⟩
  obtain ⟨x, -, hu⟩ := h 2 3 4
  have h1 : (1 : Fin 6) = x := hu 1 (by simp only [InInterval, F1G_dist]; decide)
  have h5 : (5 : Fin 6) = x := hu 5 (by simp only [InInterval, F1G_dist]; decide)
  exact absurd (h1.trans h5.symm) (by decide)

/-- HKO Figure 1, graph `H`: `a=0, b=1, c=2, x=3, m=4, y=5`; `a,b,c` adjacent to `x,m,y`,
plus `x–m`, `m–y`. -/
def f1hEdges : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

def F1H : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ f1hEdges ∨ (j.val, i.val) ∈ f1hEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel F1H.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ f1hEdges ∨ (j.val, i.val) ∈ f1hEdges))

def dF1HTable : List (List ℕ) :=
  [[0, 2, 2, 1, 1, 1],
   [2, 0, 2, 1, 1, 1],
   [2, 2, 0, 1, 1, 1],
   [1, 1, 1, 0, 1, 2],
   [1, 1, 1, 1, 0, 1],
   [1, 1, 1, 2, 1, 0]]

def DF1H (i j : Fin 6) : ℕ := (dF1HTable.getD i.val []).getD j.val 0

theorem F1H_dist : ∀ x y, F1H.dist x y = DF1H x y :=
  dist_eq_of_certificate F1H DF1H (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem F1H_connected : F1H.Connected :=
  connected_of_dist F1H fun x y hxy => by rw [F1H_dist]; revert x y; decide

theorem F1H_fourPoint : FourPointBM F1H := by
  intro u v w x
  simp only [F1H_dist]
  revert u v w x
  decide +kernel

theorem F1H_diam : F1H.diam = 2 :=
  diam_eq_of_bounds F1H F1H_connected 2 (fun u v => by rw [F1H_dist]; revert u v; decide)
    3 5 (by rw [F1H_dist]; decide)

theorem F1H_triameter : triameter F1H = 6 := by
  have hle : ∀ a b c : Fin 6, DF1H a b + DF1H a c + DF1H b c ≤ 6 := by decide +kernel
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    simp only [triDist, F1H_dist]
    exact hle a b c
  · have h : triDist F1H 0 1 2 = 6 := by simp only [triDist, F1H_dist]; decide
    calc (6 : ℕ) = triDist F1H 0 1 2 := h.symm
      _ ≤ triameter F1H := triDist_le_triameter F1H 0 1 2

/-- HKO: in Figure 1 `H`, the diametral pair `x,y` does not extend to a triametral triple. -/
theorem F1H_not_question4 : ¬ Question4 F1H := by
  intro h
  have hd : IsDiametral F1H 3 5 := by rw [IsDiametral, F1H_diam, F1H_dist]; decide
  obtain ⟨z, hz⟩ := h 3 5 hd
  rw [IsTriametral, F1H_triameter] at hz
  simp only [triDist, F1H_dist] at hz
  revert z
  decide

/-- Consistent with Corollary B1: each Figure 1 graph satisfies Question 3 or Question 4. -/
example : (Question3 F1G ∨ Question4 F1G) ∧ (Question3 F1H ∨ Question4 F1H) :=
  ⟨question3_or_question4 F1G F1G_connected F1G_fourPoint,
    question3_or_question4 F1H F1H_connected F1H_fourPoint⟩

/-- The Problem-1 counterexample `G1` violates the four-point condition (it contains a domino,
so it is not distance-hereditary): for `1, 3, 4, 5` the three sums are `2, 4, 6`. -/
theorem G1_not_fourPoint : ¬ FourPointBM G1 := by
  intro h
  have := h 1 3 4 5
  simp only [G1_dist] at this
  revert this
  decide

/-- The Problem-2 counterexample `G2` (a 4-cycle with pendant trees) satisfies the four-point
condition: it is median *and* distance-hereditary. It violates Question 4 but satisfies
Question 3, as Corollary B1 requires. -/
theorem G2_fourPoint : FourPointBM G2 := by
  intro u v w x
  simp only [G2_dist]
  revert u v w x
  decide +kernel

example : Question3 G2 :=
  (question3_or_question4 G2 G2_connected G2_fourPoint).resolve_right not_question4_G2

end HKOTriameter

#print axioms HKOTriameter.core
#print axioms HKOTriameter.extends_of_no_diametral
#print axioms HKOTriameter.question3_or_question4
#print axioms HKOTriameter.problem3_fourPoint
#print axioms HKOTriameter.problem3ClaimFP
#print axioms HKOTriameter.F1G_fourPoint
#print axioms HKOTriameter.F1G_not_question3'
#print axioms HKOTriameter.F1H_fourPoint
#print axioms HKOTriameter.F1H_not_question4
#print axioms HKOTriameter.G1_not_fourPoint
#print axioms HKOTriameter.G2_fourPoint
#print axioms HKOTriameter.F1G_not_median
