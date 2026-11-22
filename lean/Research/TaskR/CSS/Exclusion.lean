import Research.TaskR.CSS.Geometry
import Research.TaskR.CSS.ExclusionFinite

namespace TaskR.CSS.Exclusion

open Challenge TaskR.CSS.Geometry Set
open scoped BigOperators

theorem lattice_point {z : Lattice} (hz : embed z ∈ P) : z ∈ points := by
  let s : ℤ := z 0 + z 1 + z 2 + z 3
  obtain ⟨hs, hc⟩ := constraints hz
  have hsum : total (embed z) = (s : ℝ) := by simp [total, embed, s]
  simp only [slack, hsum] at hs
  have hi (i : Fin 4) := hc i
  apply finite_classification z s rfl
  · exact_mod_cast (show (s : ℝ) ≤ 1 by linarith)
  · have h := hi 0
    norm_num [coeff, slack, hsum, embed, weight] at h
    exact_mod_cast (show 0 ≤ 6*(z 0 : ℝ)+2*(1-(s:ℝ)) by linarith)
  · have h := hi 1
    norm_num [coeff, slack, hsum, embed, weight] at h
    exact_mod_cast (show 0 ≤ 6*(z 1 : ℝ)+1-(s:ℝ) by linarith)
  · have h := hi 2
    norm_num [coeff, slack, hsum, embed, weight] at h
    exact_mod_cast (show 0 ≤ 6*(z 2 : ℝ)+1-(s:ℝ) by linarith)
  · have h := hi 3
    norm_num [coeff, slack, hsum, embed, weight] at h
    exact_mod_cast (show 0 ≤ 6*(z 3 : ℝ)+1-(s:ℝ) by linarith)

/-- Every construction has a translated zero-sum leaf still inside its final hull. -/
private theorem contains_leaf {K : Set Space} (h : Generated K) :
    ∃ (s : Finset Lattice) (t : Lattice), 2 ≤ s.card ∧
      (∑ z ∈ s, z = 0) ∧ ∀ z ∈ s, embed (t+z) ∈ K := by
  induction h with
  | leaf s hc hs =>
      refine ⟨s, 0, hc, hs, ?_⟩
      intro z hz
      rw [zero_add]
      exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩
  | translate _ v ih =>
      obtain ⟨s, t, hc, hs, inside⟩ := ih
      refine ⟨s, v+t, hc, hs, ?_⟩
      intro z hz
      refine ⟨embed (t+z), inside z hz, ?_⟩
      ext i
      simp [embed, add_assoc]
  | join _ _ ih _ =>
      obtain ⟨s, t, hc, hs, inside⟩ := ih
      exact ⟨s, t, hc, hs, fun z hz => subset_convexHull ℝ _ (Or.inl (inside z hz))⟩

end TaskR.CSS.Exclusion

namespace TaskR.CSS.Proof

open Challenge Exclusion

theorem OutsideList : Challenge.OutsideList := by
  intro h
  obtain ⟨s, t, hc, hs, hp⟩ := contains_leaf h
  exact no_translated_leaf s t hc hs fun z hz => lattice_point (hp z hz)

#print axioms OutsideList

end TaskR.CSS.Proof
