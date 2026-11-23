import Research.TaskT.HellyFive.Challenge

namespace TaskT.HellyFive

/-- Deleting one extreme point per convex set forces any preserving subfamily
to retain every index. The argument includes polytopes of lower affine dimension. -/
theorem attainableCount_le_preservingBound {n t b : ℕ}
    (ht : t ∈ attainableCounts n) (hb : PreservesFive n b) : t ≤ b := by
  classical
  by_cases hpos : 0 < t
  · obtain ⟨V, hcount, hf⟩ := ht
    let P := convexHull ℝ (embed '' (V : Set (Grid n)))
    let E := P.extremePoints ℝ
    let X := {z : Grid n | embed z ∈ P ∧ embed z ∉ E}
    change E.encard = (t : ℕ∞) at hcount
    change X.encard = 5 at hf
    let : Fintype E := (Set.finite_of_encard_eq_coe hcount).fintype
    have hcE : Fintype.card E = t := by
      exact_mod_cast (Set.coe_fintypeCard E).trans hcount
    let e : Fin t ≃ E := (Fintype.equivFinOfCardEq hcE).symm
    let C (i : Fin t) : Set (Space n) := P \ {(e i).val}
    have cv : Convex ℝ P := convex_convexHull ℝ _
    have hconv (i : Fin t) : Convex ℝ (C i) :=
      (cv.mem_extremePoints_iff_convex_sdiff.mp (e i).property).2
    have base_sub (s : Finset (Fin t)) : X ⊆ commonGrid C s := by
      intro z hz i _
      refine ⟨hz.1, ?_⟩
      intro heq
      exact hz.2 ((Set.mem_singleton_iff.mp heq) ▸ (e i).property)
    have full : commonGrid C Finset.univ = X := by
      refine Set.Subset.antisymm ?_ (base_sub _)
      intro z hz
      refine ⟨(hz ⟨0, hpos⟩ (Finset.mem_univ _)).1, ?_⟩
      intro he
      let i := e.symm ⟨embed z, he⟩
      have heq : (e i).val = embed z := congrArg Subtype.val (e.apply_symm_apply _)
      exact (hz i (Finset.mem_univ _)).2 (Set.mem_singleton_iff.mpr heq.symm)
    obtain ⟨s, hcard, hs⟩ := hb t hpos C hconv (full ▸ hf)
    have finX : X.Finite := Set.finite_of_encard_eq_coe (k := 5) hf
    have heq : X = commonGrid C s :=
      finX.eq_of_subset_of_encard_le (base_sub s) (hs.trans hf.symm).le
    have hsall : s = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      obtain ⟨z, _, hzi⟩ := extremePoints_convexHull_subset (e i).property
      have hz : z ∈ commonGrid C s := by
        intro j hj
        refine ⟨hzi.symm ▸ (e i).property.1, ?_⟩
        intro h
        have hij : e i = e j := Subtype.ext (hzi.symm.trans (Set.mem_singleton_iff.mp h))
        exact hi (e.injective hij ▸ hj)
      have hx : z ∈ X := heq.symm ▸ hz
      exact hx.2 (hzi.symm ▸ (e i).property)
    simpa [hsall] using hcard
  · omega

end TaskT.HellyFive
