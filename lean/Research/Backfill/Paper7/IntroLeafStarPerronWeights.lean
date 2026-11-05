import Research.Backfill.Paper7.IntroSubdividedStarPerronWeights

/-! Pure-leaf-star weights from the real adjacency equations.
The normalized positive eigenvector and exact neighborhoods are explicit
intermediate data; the next source derives them under original graph hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLeafStarWeights
open SimpleGraph Matrix Paper7IntroStarWeights

theorem leaf_star_normalized_perron_weights
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (a c : V) (i₀ : Y) (hc : c ∉ Y)
    (hNa : ∀ z, G.Adj a z ↔ z = c ∨ ∃ i : Y, z = i.val)
    (hNl : ∀ (i : Y) z, G.Adj i.val z ↔ z = a)
    (f : V → ℝ) (hf : ∀ v, 0 < f v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (h₀ : f i₀.val = 1) :
    (∀ i : Y, f i.val = 1) ∧ f a = 3 ∧
      f c = 9 - (Y.card : ℝ) ∧ Y.card < 9 := by
  have hbase := eigen_three_at_single_neighbor G f hAf i₀.val a (hNl i₀)
  have ha : f a = 3 := by linarith
  have hall : ∀ i : Y, f i.val = 1 := by
    intro i
    have he := eigen_three_at_single_neighbor G f hAf i.val a (hNl i)
    linarith
  have hNa' : G.neighborFinset a = insert c Y := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [hNa z]
    constructor
    · rintro (hzc | ⟨i, hzi⟩)
      · exact Or.inl hzc
      · exact Or.inr (hzi.symm ▸ i.property)
    · rintro (hzc | hzY)
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, hzY⟩, rfl⟩
  have hsum : ∑ z ∈ Y, f z = (Y.card : ℝ) := by
    calc
      (∑ z ∈ Y, f z) = ∑ _z ∈ Y, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hall ⟨z, hz⟩
      _ = (Y.card : ℝ) := by simp
  have hea := congrFun hAf a
  have he : f c + (Y.card : ℝ) = 3 * f a := by
    simpa only [G.adjMatrix_mulVec_apply, hNa', Finset.sum_insert hc,
      hsum, Pi.smul_apply, smul_eq_mul] using hea
  have hcw : f c = 9 - (Y.card : ℝ) := by linarith
  have hm : (Y.card : ℝ) < 9 := by linarith [hf c]
  refine ⟨hall, ha, hcw, ?_⟩
  exact_mod_cast hm
#print axioms Paper7IntroLeafStarWeights.leaf_star_normalized_perron_weights

end Paper7IntroLeafStarWeights
