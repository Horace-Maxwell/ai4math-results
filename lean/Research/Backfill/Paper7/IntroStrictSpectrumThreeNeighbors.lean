import Research.Backfill.Paper7.IntroDegreeThreshold

/-! Local neighbor restrictions below spectral radius two, without a tree or
classification hypothesis. These helpers do not classify the original graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStrictNeighbors
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7IntroHighBranch

theorem positive_eigenvector_edge_degree_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ) (f : V → ℝ)
    (hf : ∀ i, 0 < f i) (he : G.adjMatrix ℝ *ᵥ f = r • f)
    (i j : V) (hij : G.Adj i j) :
    r * f j + ((G.degree i : ℝ) - 1) * f i ≤ r ^ 2 * f i := by
  have hrow (a : V) : (∑ b ∈ G.neighborFinset a, f b) = r * f a := by
    simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun he a
  have hj : j ∈ G.neighborFinset i := (G.mem_neighborFinset i j).mpr hij
  have hneighbor (k : V) (hk : k ∈ (G.neighborFinset i).erase j) :
      f i ≤ r * f k := by
    have hik : G.Adj i k :=
      (G.mem_neighborFinset i k).mp (Finset.mem_erase.mp hk).2
    have hi : i ∈ G.neighborFinset k := (G.mem_neighborFinset k i).mpr hik.symm
    have h := Finset.single_le_sum (fun a _ => (hf a).le) hi
    rwa [hrow k] at h
  have hsum := Finset.sum_le_sum hneighbor
  have hcardNat : ((G.neighborFinset i).erase j).card + 1 = G.degree i := by
    rw [Finset.card_erase_add_one hj, G.card_neighborFinset_eq_degree]
  have hcardReal : (((G.neighborFinset i).erase j).card : ℝ) + 1 =
      (G.degree i : ℝ) := by exact_mod_cast hcardNat
  have hcard : (((G.neighborFinset i).erase j).card : ℝ) =
      (G.degree i : ℝ) - 1 := by linarith
  have hsplit : (∑ k ∈ (G.neighborFinset i).erase j, f k) + f j = r * f i := by
    rw [Finset.sum_erase_add _ _ hj, hrow i]
  have hbound : ((G.degree i : ℝ) - 1) * f i ≤
      r * (∑ k ∈ (G.neighborFinset i).erase j, f k) := by
    calc
      ((G.degree i : ℝ) - 1) * f i =
          ∑ k ∈ (G.neighborFinset i).erase j, f i := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ k ∈ (G.neighborFinset i).erase j, r * f k := hsum
      _ = r * (∑ k ∈ (G.neighborFinset i).erase j, f k) :=
        (Finset.mul_sum _ _ _).symm
  nlinarith [congrArg (fun t : ℝ => r * t) hsplit]
#print axioms Paper7IntroStrictNeighbors.positive_eigenvector_edge_degree_bound

theorem spectrum_lt_two_no_adjacent_high_degrees
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hspec : ∀ t ∈ spec G, t < 2)
    (i j : V) (hij : G.Adj i j) (hi : 3 ≤ G.degree i) (hj : 3 ≤ G.degree j) :
    False := by
  let : Nonempty V := hG.nonempty
  obtain ⟨r, hr, f, hf, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron G hG
  have hr2 := hspec r hr
  have hiR : (3 : ℝ) ≤ G.degree i := by exact_mod_cast hi
  have hjR : (3 : ℝ) ≤ G.degree j := by exact_mod_cast hj
  have hleft := positive_eigenvector_edge_degree_bound G r f hf he i j hij
  have hright := positive_eigenvector_edge_degree_bound G r f hf he j i hij.symm
  have hiExtra : 0 ≤ ((G.degree i : ℝ) - 3) * f i :=
    mul_nonneg (by linarith) (hf i).le
  have hjExtra : 0 ≤ ((G.degree j : ℝ) - 3) * f j :=
    mul_nonneg (by linarith) (hf j).le
  have hnonneg : 0 ≤ (r ^ 2 - r - 2) * (f i + f j) := by
    nlinarith [hleft, hright, hiExtra, hjExtra]
  have hneg : (r - 2) * (r + 1) * (f i + f j) < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (add_pos (hf i) (hf j))
  nlinarith
#print axioms Paper7IntroStrictNeighbors.spectrum_lt_two_no_adjacent_high_degrees

theorem spectrum_lt_two_degree_three_has_leaf_neighbor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hspec : ∀ t ∈ spec G, t < 2) (i : V) (hi : G.degree i = 3) :
    ∃ j, G.Adj i j ∧ G.degree j = 1 := by
  by_contra hnone
  have hdeg (j : V) (hij : G.Adj i j) : 2 ≤ G.degree j := by
    have hjpos := hij.degree_pos_right
    have hjne : G.degree j ≠ 1 := fun hj => hnone ⟨j, hij, hj⟩
    omega
  let : Nonempty V := hG.nonempty
  obtain ⟨r, hr, f, hf, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron G hG
  have hr2 := hspec r hr
  have hiSq := positive_eigenvector_degree_le_square G r f hf he i
  rw [hi] at hiSq
  have hrpos : 0 < r := by norm_num at hiSq; nlinarith
  have hrow : (∑ j ∈ G.neighborFinset i, f j) = r * f i := by
    simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun he i
  have hneighbor (j : V) (hj : j ∈ G.neighborFinset i) :
      r * f i ≤ (r ^ 2 - 1) * f j := by
    have hij := (G.mem_neighborFinset i j).mp hj
    have h := positive_eigenvector_edge_degree_bound G r f hf he j i hij.symm
    have hjR : (2 : ℝ) ≤ G.degree j := by exact_mod_cast hdeg j hij
    have hExtra : 0 ≤ ((G.degree j : ℝ) - 2) * f j :=
      mul_nonneg (by linarith) (hf j).le
    nlinarith
  have hsum := Finset.sum_le_sum hneighbor
  have hsum' : 3 * (r * f i) ≤ (r ^ 2 - 1) * (r * f i) := by
    calc
      3 * (r * f i) = ∑ j ∈ G.neighborFinset i, r * f i := by
        simp only [Finset.sum_const, G.card_neighborFinset_eq_degree, hi,
          nsmul_eq_mul, Nat.cast_ofNat]
      _ ≤ ∑ j ∈ G.neighborFinset i, (r ^ 2 - 1) * f j := hsum
      _ = (r ^ 2 - 1) * (∑ j ∈ G.neighborFinset i, f j) :=
        (Finset.mul_sum _ _ _).symm
      _ = (r ^ 2 - 1) * (r * f i) := by rw [hrow]
  have hcancel : (3 : ℝ) ≤ r ^ 2 - 1 :=
    (mul_le_mul_iff_left₀ (mul_pos hrpos (hf i))).mp hsum'
  nlinarith
#print axioms Paper7IntroStrictNeighbors.spectrum_lt_two_degree_three_has_leaf_neighbor

end Paper7IntroStrictNeighbors
