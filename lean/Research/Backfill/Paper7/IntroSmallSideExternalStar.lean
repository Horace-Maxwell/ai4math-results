import Research.Backfill.Paper7.IntroIntegerSideLeafBudget
import Research.Backfill.Paper7.IntroSubdividedStarPerronWeights

/-! One fixed eigenvector and sign coloring are used throughout.
The full star and integer-side budget are explicit intermediate inputs;
the next module obtains them from the original graph hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafExternal
open SimpleGraph Matrix Paper7IntroStarWeights

theorem small_integer_side_external_star_is_leaf
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (z : V → ℤ) (o v x : V) (Y : Finset V)
    (hflip : ∀ u t, G.Adj u t → eps u = -eps t)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (hz : ∀ t, 0 < z t)
    (hside : ∀ t, eps t = -eps o → f t = 3 * (z t : ℝ))
    (hsum : (∑ t, if eps t = -eps o then z t ^ 2 else 0) = 20)
    (hv : eps v = -eps o) (hxc : G.Adj x v)
    (hvY : v ∉ Y) (hNx : G.neighborFinset x = insert v Y)
    (hNy : ∀ y ∈ Y, ∀ t, G.Adj y t ↔ t = x)
    (hcard : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 3) :
    Y = ∅ ∧ G.neighborFinset x = {v} ∧
      (∀ t, G.Adj x t ↔ t = v) ∧ G.degree x = 1 ∧ f x = (z v : ℝ) := by
  have hbound := integer_square_budget_twenty_bound
    (fun t => eps t = -eps o) z hz hsum v hv
  have hzv : (z v : ℝ) ≤ 4 := by exact_mod_cast hbound.2
  have hfv : f v ≤ 12 := by rw [hside v hv]; linarith only [hzv]
  have hYempty : Y = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    have hyx : G.Adj y x := (hNy y hy x).mpr rfl
    have hyW : eps y = -eps o := by
      linarith only [hflip y x hyx, hflip x v hxc, hv]
    have hzy : (1 : ℤ) ≤ z y := by have hp := hz y; omega
    have hzyR : (1 : ℝ) ≤ (z y : ℝ) := by exact_mod_cast hzy
    have hfy : 3 ≤ f y := by rw [hside y hyW]; linarith only [hzyR]
    have hx : f x = 3 * f y :=
      eigen_three_at_single_neighbor G f hAf y x (hNy y hy)
    have hall : ∀ j ∈ Y, f j = f y := by
      intro j hj
      have he := eigen_three_at_single_neighbor G f hAf j x (hNy j hj)
      linarith only [he, hx]
    have hleafsum : (∑ j ∈ Y, f j) = (Y.card : ℝ) * f y := by
      calc
        _ = ∑ _j ∈ Y, f y := Finset.sum_congr rfl (fun j hj => hall j hj)
        _ = _ := by simp
    have hrow : f v + (Y.card : ℝ) * f y = 3 * f x := by
      simpa only [G.adjMatrix_mulVec_apply, hNx, Finset.sum_insert hvY,
        hleafsum, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
    rcases hcard with hc | hc | hc
    · have he : Y = ∅ := Finset.card_eq_zero.mp hc
      simp only [he, Finset.notMem_empty] at hy
    · rw [hc] at hrow
      norm_num only [Nat.cast_one, one_mul] at hrow
      linarith only [hrow, hx, hfy, hfv]
    · rw [hc] at hrow
      norm_num only [Nat.cast_ofNat] at hrow
      linarith only [hrow, hx, hfy, hfv]
  have hsingle : G.neighborFinset x = {v} := by
    simpa only [hYempty, Finset.insert_empty] using hNx
  have hneighbor : ∀ t, G.Adj x t ↔ t = v := by
    intro t
    rw [← G.mem_neighborFinset x t, hsingle, Finset.mem_singleton]
  have hdegree : G.degree x = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hsingle, Finset.card_singleton]
  have hrow := eigen_three_at_single_neighbor G f hAf x v hneighbor
  have hweight : f x = (z v : ℝ) := by
    rw [hside v hv] at hrow
    linarith only [hrow]
  exact ⟨hYempty, hsingle, hneighbor, hdegree, hweight⟩
#print axioms Paper7IntroThreeLeafExternal.small_integer_side_external_star_is_leaf

end Paper7IntroThreeLeafExternal
