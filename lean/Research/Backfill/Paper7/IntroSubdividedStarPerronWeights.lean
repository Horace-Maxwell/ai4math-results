import Research.Backfill.Paper7.IntroRadiusThreeProjectors

/-! Perron weights from actual graph neighborhoods. The finite index and
all three neighborhood identities are supplied by the actual component
shape theorem in the next file; no local matrix moment is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarWeights
open SimpleGraph Matrix Paper7IntroProjectors

theorem eigen_three_at_single_neighbor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (x y : V) (hN : ∀ z, G.Adj x z ↔ z = y) :
    f y = 3 * f x := by
  have hn : G.neighborFinset x = {y} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact hN z
  have he := congrFun hAf x
  simpa only [G.adjMatrix_mulVec_apply, hn, Finset.sum_singleton,
    Pi.smul_apply, smul_eq_mul] using he
#print axioms Paper7IntroStarWeights.eigen_three_at_single_neighbor

theorem eigen_three_at_two_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (x a l : V) (hal : a ≠ l)
    (hN : ∀ z, G.Adj x z ↔ z = a ∨ z = l) :
    f a + f l = 3 * f x := by
  have hn : G.neighborFinset x = {a, l} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    exact hN z
  have he := congrFun hAf x
  simpa only [G.adjMatrix_mulVec_apply, hn, Finset.sum_pair hal,
    Pi.smul_apply, smul_eq_mul] using he
#print axioms Paper7IntroStarWeights.eigen_three_at_two_neighbors

theorem subdivided_star_normalized_perron_weights
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (leaf : Y → V) (a c : V) (i₀ : Y)
    (hc : c ∉ Y) (hal : ∀ i, a ≠ leaf i)
    (hNa : ∀ z, G.Adj a z ↔ z = c ∨ ∃ i : Y, z = i.val)
    (hNy : ∀ i : Y, ∀ z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ i : Y, ∀ z, G.Adj (leaf i) z ↔ z = i.val)
    (f : V → ℝ) (hf : ∀ v, 0 < f v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (h₀ : f (leaf i₀) = 1) :
    (∀ i : Y, f (leaf i) = 1 ∧ f i.val = 3) ∧
    f a = 8 ∧ f c = 3 * (8 - (Y.card : ℝ)) ∧ Y.card < 8 := by
  have hbaseL := eigen_three_at_single_neighbor G f hAf (leaf i₀) i₀.val (hNl i₀)
  have hbaseY := eigen_three_at_two_neighbors G f hAf i₀.val a (leaf i₀)
    (hal i₀) (hNy i₀)
  have ha : f a = 8 := by linarith
  have hall : ∀ i : Y, f (leaf i) = 1 ∧ f i.val = 3 := by
    intro i
    have hl := eigen_three_at_single_neighbor G f hAf (leaf i) i.val (hNl i)
    have hy := eigen_three_at_two_neighbors G f hAf i.val a (leaf i) (hal i) (hNy i)
    constructor
    · linarith
    · linarith
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
  have hsum : ∑ z ∈ Y, f z = (Y.card : ℝ) * 3 := by
    calc
      (∑ z ∈ Y, f z) = ∑ _z ∈ Y, (3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (hall ⟨z, hz⟩).2
      _ = (Y.card : ℝ) * 3 := by simp
  have hea := congrFun hAf a
  have he : f c + (Y.card : ℝ) * 3 = 3 * f a := by
    simpa only [G.adjMatrix_mulVec_apply, hNa', Finset.sum_insert hc,
      hsum, Pi.smul_apply, smul_eq_mul] using hea
  have hcw : f c = 3 * (8 - (Y.card : ℝ)) := by linarith
  have hm : (Y.card : ℝ) < 8 := by linarith [hf c]
  refine ⟨hall, ha, hcw, ?_⟩
  exact_mod_cast hm
#print axioms Paper7IntroStarWeights.subdivided_star_normalized_perron_weights

theorem subdivided_star_bipartite_signs
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (leaf : Y → V) (a c : V)
    (hNa : ∀ z, G.Adj a z ↔ z = c ∨ ∃ i : Y, z = i.val)
    (hNy : ∀ i : Y, ∀ z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (eps : V → ℝ) (hflip : ∀ u v, G.Adj u v → eps u = -eps v) :
    (∀ i : Y, eps (leaf i) = eps a ∧ eps i.val = -eps a) ∧
    eps c = -eps a := by
  have hac := hflip a c ((hNa c).mpr (Or.inl rfl))
  constructor
  · intro i
    have hai := hflip a i.val ((hNa i.val).mpr (Or.inr ⟨i, rfl⟩))
    have hil := hflip i.val (leaf i) ((hNy i (leaf i)).mpr (Or.inr rfl))
    constructor
    · linarith
    · linarith
  · linarith
#print axioms Paper7IntroStarWeights.subdivided_star_bipartite_signs

end Paper7IntroStarWeights
