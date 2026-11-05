import Research.Backfill.Paper7.IntroSubdividedStarPerronWeights

/-! Actual complete leaf neighborhoods transport a fixed real Perron column
into star weights. The original graph must separately supply these structural
and column hypotheses; no original classification is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourCycleWeights
open SimpleGraph Matrix Paper7IntroStarWeights

theorem actual_leaf_square_entry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (y x c : V)
    (hN : ∀ v, G.Adj y v ↔ v = x) :
    G.degree y = 1 ∧
      ((G.adjMatrix ℝ) ^ 2) y c = if G.Adj x c then 1 else 0 := by
  have hyN : G.neighborFinset y = {x} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact hN v
  constructor
  · rw [← G.card_neighborFinset_eq_degree, hyN, Finset.card_singleton]
  · rw [pow_two, G.adjMatrix_mul_apply, hyN, Finset.sum_singleton,
      G.adjMatrix_apply]
#print axioms Paper7IntroFourCycleWeights.actual_leaf_square_entry

theorem pure_star_column_at_c
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f) (c x : V) (Y : Finset V)
    (hcY : c ∉ Y) (hNx : G.neighborFinset x = insert c Y)
    (hNy : ∀ y ∈ Y, ∀ v, G.Adj y v ↔ v = x)
    (hfc : f c = 5)
    (hcol : ∀ v, eps v = eps c → v ≠ c → ((G.adjMatrix ℝ) ^ 2) v c = f v) :
    (Y.card = 0 ∧ f x = 5 / 3) ∨ (Y.card = 4 ∧ f x = 3) := by
  have hxc : G.Adj x c := by
    apply (G.mem_neighborFinset x c).mp
    rw [hNx]
    exact Finset.mem_insert_self c Y
  by_cases hY : Y.Nonempty
  · obtain ⟨y, hy⟩ := hY
    have hweights : ∀ j ∈ Y, f j = 1 := by
      intro j hj
      have hjc : j ≠ c := fun he => hcY (he ▸ hj)
      have hjx : G.Adj j x := (hNy j hj x).mpr rfl
      have hsign : eps j = eps c := by linarith only [hflip j x hjx, hflip x c hxc]
      have he := (actual_leaf_square_entry G j x c (hNy j hj)).2
      rw [hcol j hsign hjc] at he
      simpa only [hxc, ↓reduceIte] using he
    have hx : f x = 3 := by
      have he := eigen_three_at_single_neighbor G f hAf y x (hNy y hy)
      simpa only [hweights y hy, mul_one] using he
    have hsum : ∑ j ∈ Y, f j = (Y.card : ℝ) := by
      calc
        _ = ∑ _j ∈ Y, (1 : ℝ) := Finset.sum_congr rfl (fun j hj => hweights j hj)
        _ = _ := by simp
    have hrow : f c + (Y.card : ℝ) = 3 * f x := by
      simpa only [G.adjMatrix_mulVec_apply, hNx, Finset.sum_insert hcY,
        hsum, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
    have hcardR : (Y.card : ℝ) = 4 := by linarith only [hrow, hfc, hx]
    have hcard : Y.card = 4 := by exact_mod_cast hcardR
    exact Or.inr ⟨hcard, hx⟩
  · have hYempty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    have hNx' : G.neighborFinset x = {c} := by simpa only [hYempty, Finset.insert_empty] using hNx
    have hrow : f c = 3 * f x := by
      simpa only [G.adjMatrix_mulVec_apply, hNx', Finset.sum_singleton,
        Pi.smul_apply, smul_eq_mul] using congrFun hAf x
    have hx : f x = 5 / 3 := by linarith only [hrow, hfc]
    exact Or.inl ⟨by simp only [hYempty, Finset.card_empty], hx⟩
#print axioms Paper7IntroFourCycleWeights.pure_star_column_at_c

theorem pure_star_column_at_opposite
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hf : ∀ v, 0 < f v) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (c w x : V) (Y : Finset V)
    (hwc : eps w = eps c) (hdc : G.degree c ≠ 1)
    (hNx : G.neighborFinset x = insert w Y)
    (hNy : ∀ y ∈ Y, ∀ v, G.Adj y v ↔ v = x)
    (hxc : ¬ G.Adj x c) (hfw : f w = 2)
    (hcol : ∀ v, eps v = eps c → v ≠ c → ((G.adjMatrix ℝ) ^ 2) v c = f v) :
    Y = ∅ ∧ f x = 2 / 3 := by
  have hxw : G.Adj x w := by
    apply (G.mem_neighborFinset x w).mp
    rw [hNx]
    exact Finset.mem_insert_self w Y
  have hYempty : Y = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    obtain ⟨hdy, he⟩ := actual_leaf_square_entry G y x c (hNy y hy)
    have hyc : y ≠ c := by
      intro hyc
      apply hdc
      rw [hyc] at hdy
      exact hdy
    have hyx : G.Adj y x := (hNy y hy x).mpr rfl
    have hsign : eps y = eps c := by
      linarith only [hflip y x hyx, hflip x w hxw, hwc]
    rw [hcol y hsign hyc] at he
    have hyzero : f y = 0 := by simpa only [hxc, ↓reduceIte] using he
    have hypos := hf y
    linarith only [hyzero, hypos]
  have hNx' : G.neighborFinset x = {w} := by
    simpa only [hYempty, Finset.insert_empty] using hNx
  have hrow : f w = 3 * f x := by
    simpa only [G.adjMatrix_mulVec_apply, hNx', Finset.sum_singleton,
      Pi.smul_apply, smul_eq_mul] using congrFun hAf x
  have hx : f x = 2 / 3 := by linarith only [hrow, hfw]
  exact ⟨hYempty, hx⟩
#print axioms Paper7IntroFourCycleWeights.pure_star_column_at_opposite

end Paper7IntroFourCycleWeights
