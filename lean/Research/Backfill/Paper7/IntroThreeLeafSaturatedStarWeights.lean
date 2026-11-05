import Research.Backfill.Paper7.IntroFourCycleColumnStarWeights

/-! True complete star neighborhoods transport the saturated column.
All structural and column hypotheses are explicit only in these generic
interfaces; the original-graph wrapper supplies them from actual805/806. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafStarWeights
open SimpleGraph Matrix Paper7IntroStarWeights Paper7IntroFourCycleWeights

theorem actual_star_square_entry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x u c : V) (Z : Finset V)
    (hu : u ∉ Z) (hNx : G.neighborFinset x = insert u Z)
    (hNz : ∀ z ∈ Z, ∀ v, G.Adj z v ↔ v = x) (hxc : x ≠ c) :
    ((G.adjMatrix ℝ) ^ 2) x c = if G.Adj u c then 1 else 0 := by
  have hzsum : ∑ z ∈ Z, (G.adjMatrix ℝ) z c = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hzc : ¬ G.Adj z c := by
      intro he
      exact hxc ((hNz z hz c).mp he).symm
    simp only [G.adjMatrix_apply, hzc, ↓reduceIte]
  rw [pow_two, G.adjMatrix_mul_apply, hNx, Finset.sum_insert hu, hzsum,
    add_zero, G.adjMatrix_apply]
#print axioms Paper7IntroThreeLeafStarWeights.actual_star_square_entry

theorem saturated_other_star_at_c
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (a c x : V) (Y Z : Finset V)
    (hY : ∀ y ∈ Y, ∀ v, G.Adj y v ↔ v = a)
    (hxa : x ≠ a) (hcZ : c ∉ Z)
    (hNx : G.neighborFinset x = insert c Z)
    (hNz : ∀ z ∈ Z, ∀ v, G.Adj z v ↔ v = x)
    (hcount : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 3)
    (hfc : f c = 6)
    (hcol : ∀ v, eps v = eps c → v ≠ c → v ∉ Y →
      f v = 3 * ((G.adjMatrix ℝ) ^ 2) v c) :
    Z = ∅ ∧ G.neighborFinset x = {c} ∧ G.degree x = 1 ∧ f x = 2 := by
  have hxc : G.Adj x c := by
    apply (G.mem_neighborFinset x c).mp
    rw [hNx]
    exact Finset.mem_insert_self c Z
  have hZempty : Z = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    have hweights : ∀ j ∈ Z, f j = 3 := by
      intro j hj
      have hjx : G.Adj j x := (hNz j hj x).mpr rfl
      have hjc : j ≠ c := fun he => hcZ (he ▸ hj)
      have hjY : j ∉ Y := by
        intro he
        exact hxa ((hY j he x).mp hjx)
      have hs : eps j = eps c := by
        linarith only [hflip j x hjx, hflip x c hxc]
      have he := (actual_leaf_square_entry G j x c (hNz j hj)).2
      have hentry : ((G.adjMatrix ℝ) ^ 2) j c = 1 := by
        simpa only [hxc, ↓reduceIte] using he
      have hf := hcol j hs hjc hjY
      rw [hentry, mul_one] at hf
      exact hf
    have hx : f x = 9 := by
      have he := eigen_three_at_single_neighbor G f hAf z x (hNz z hz)
      rw [hweights z hz] at he
      norm_num at he
      exact he
    have hsum : ∑ j ∈ Z, f j = (Z.card : ℝ) * 3 := by
      calc
        _ = ∑ _j ∈ Z, (3 : ℝ) := Finset.sum_congr rfl (fun j hj => hweights j hj)
        _ = _ := by simp
    have hrow : f c + (Z.card : ℝ) * 3 = 3 * f x := by
      simpa only [G.adjMatrix_mulVec_apply, hNx, Finset.sum_insert hcZ,
        hsum, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
    have hcardR : (Z.card : ℝ) = 7 := by linarith only [hrow, hfc, hx]
    have hcard : Z.card = 7 := by exact_mod_cast hcardR
    rcases hcount with h0 | h1 | h3 <;> omega
  have hsingle : G.neighborFinset x = {c} := by
    simpa only [hZempty, Finset.insert_empty] using hNx
  have hdegree : G.degree x = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hsingle, Finset.card_singleton]
  have hrow : f c = 3 * f x := by
    simpa only [G.adjMatrix_mulVec_apply, hsingle, Finset.sum_singleton,
      Pi.smul_apply, smul_eq_mul] using congrFun hAf x
  have hx : f x = 2 := by linarith only [hrow, hfc]
  exact ⟨hZempty, hsingle, hdegree, hx⟩
#print axioms Paper7IntroThreeLeafStarWeights.saturated_other_star_at_c

theorem saturated_star_at_cycle_neighbor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (c u x : V) (Y Z : Finset V)
    (huc : G.Adj u c) (hxc : x ≠ c) (hxY : x ∉ Y)
    (huZ : u ∉ Z) (hNx : G.neighborFinset x = insert u Z)
    (hNz : ∀ z ∈ Z, ∀ v, G.Adj z v ↔ v = x)
    (hcount : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 3)
    (hcol : ∀ v, eps v = eps c → v ≠ c → v ∉ Y →
      f v = 3 * ((G.adjMatrix ℝ) ^ 2) v c) :
    f x = 3 ∧ (∀ z ∈ Z, f z = 1) ∧
      f u = 9 - (Z.card : ℝ) ∧ (f u = 9 ∨ f u = 8 ∨ f u = 6) := by
  have hxu : G.Adj x u := by
    apply (G.mem_neighborFinset x u).mp
    rw [hNx]
    exact Finset.mem_insert_self u Z
  have hs : eps x = eps c := by
    linarith only [hflip x u hxu, hflip u c huc]
  have he := actual_star_square_entry G x u c Z huZ hNx hNz hxc
  have hentry : ((G.adjMatrix ℝ) ^ 2) x c = 1 := by
    simpa only [huc, ↓reduceIte] using he
  have hx : f x = 3 := by
    have hv := hcol x hs hxc hxY
    rw [hentry, mul_one] at hv
    exact hv
  have hz : ∀ z ∈ Z, f z = 1 := by
    intro z hz
    have he := eigen_three_at_single_neighbor G f hAf z x (hNz z hz)
    linarith only [he, hx]
  have hsum : ∑ z ∈ Z, f z = (Z.card : ℝ) := by
    calc
      _ = ∑ _z ∈ Z, (1 : ℝ) := Finset.sum_congr rfl (fun z hzZ => hz z hzZ)
      _ = _ := by simp
  have hrow : f u + (Z.card : ℝ) = 3 * f x := by
    simpa only [G.adjMatrix_mulVec_apply, hNx, Finset.sum_insert huZ,
      hsum, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
  have hu : f u = 9 - (Z.card : ℝ) := by linarith only [hrow, hx]
  refine ⟨hx, hz, hu, ?_⟩
  rcases hcount with h0 | h1 | h3
  · left
    simpa only [h0, Nat.cast_zero, sub_zero] using hu
  · right; left
    norm_num [h1] at hu
    exact hu
  · right; right
    norm_num [h3] at hu
    exact hu
#print axioms Paper7IntroThreeLeafStarWeights.saturated_star_at_cycle_neighbor

end Paper7IntroThreeLeafStarWeights
