import Research.TaskV.Stanley.AnchorOrder

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- Subtracting the masses of the proper descendants recovers the weight at each vertex. -/
theorem weights_of_record_sums (tg : G.IsTree) (th : H.IsTree) (r : V) (q : W)
    (w : V → ℕ) (z : W → ℕ) (e : RootedRecords G r ≃ RootedRecords H q)
    (order : ∀ s t, s.val ⊆ t.val ↔ (e s).val ⊆ (e t).val)
    (mass : ∀ s, (∑ y ∈ (e s).val, z y) = ∑ x ∈ s.val, w x) :
    ∀ x, w x = z (liftRecordEquiv tg th r q e x) := by
  classical
  let f := liftRecordEquiv tg th r q e
  have mapped (s : RootedRecords G r) : s.val.map f.toEmbedding = (e s).val := by
    ext y
    obtain ⟨x,rfl⟩ := f.surjective y
    exact (Finset.mem_map' f.toEmbedding).trans (liftRecordEquiv_mem tg th r q e order x s)
  have sums (s : RootedRecords G r) : (∑ x ∈ s.val, w x) = ∑ x ∈ s.val, z (f x) := by
    have h := (mass s).symm
    rw [← mapped, Finset.sum_map] at h
    exact h
  have allWeights (k : ℕ) : ∀ x, (vertexRecord tg r x).val.card = k → w x = z (f x) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx
      let s := vertexRecord tg r x
      have xin : x ∈ s.val := mem_vertexRecord tg r x
      have rest : (∑ y ∈ s.val.erase x, w y) = ∑ y ∈ s.val.erase x, z (f y) := by
        apply sum_congr rfl
        intro y hy
        obtain ⟨ne,mem⟩ := mem_erase.mp hy
        have sub := (mem_iff_vertexRecord_subset tg r y s).mp mem
        have diff : (vertexRecord tg r y).val ≠ s.val :=
          fun eq => ne ((vertexRecord_bijective tg r).injective (Subtype.ext eq))
        have lt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,diff⟩)
        exact ih _ (lt_of_lt_of_eq lt hx) y rfl
      have left := sum_erase_add s.val w xin
      have right := sum_erase_add s.val (fun y => z (f y)) xin
      have both := sums s
      omega
  exact fun x => allWeights _ x rfl

end
end StanleyContinuation
