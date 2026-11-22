import Research.TaskP.RectangleDefect.RowSplit

namespace TaskP.RectangleDefect

open Set MeasureTheory
open scoped BigOperators

/-- On the side x=0, closed projections cover the full width, while the interiors of
the projections are disjoint because every tile touching that side reaches x=1/2. -/
theorem boundary_widths {T : Type*} [Fintype T] [DecidableEq T] (a b h w : T → ℝ) (n : ℕ)
    (hh : ∀ t, 1 ≤ h t) (hw : ∀ t, 0 ≤ w t)
    (cover : (⋃ t, Icc (a t) (a t+h t) ×ˢ Icc (b t) (b t+w t)) =
      Icc 0 2 ×ˢ Icc 0 (n : ℝ))
    (disj : ∀ t u, t ≠ u → Disjoint
      (Ioo (a t) (a t+h t) ×ˢ Ioo (b t) (b t+w t))
      (Ioo (a u) (a u+h u) ×ˢ Ioo (b u) (b u+w u))) :
    (∀ t, 0 ≤ a t ∧ a t + h t ≤ 2) ∧
    ∑ t ∈ Finset.univ.filter (fun t => a t = 0), w t = n := by
  classical
  have bounds (t : T) : 0 ≤ a t ∧ a t + h t ≤ 2 := by
    have inc := (Set.subset_iUnion
      (fun t => Icc (a t) (a t+h t) ×ˢ Icc (b t) (b t+w t)) t)
    rw [cover] at inc
    have hx : a t ≤ a t+h t := by linarith [hh t]
    have hy : b t ≤ b t+w t := by linarith [hw t]
    exact ⟨(inc (show (a t,b t) ∈ _ from ⟨⟨le_rfl,hx⟩,le_rfl,hy⟩)).1.1,
      (inc (show (a t+h t,b t) ∈ _ from ⟨⟨hx,le_rfl⟩,le_rfl,hy⟩)).1.2⟩
  refine ⟨bounds, ?_⟩
  let s := Finset.univ.filter (fun t => a t = 0)
  let J := fun t => Icc (b t) (b t+w t)
  have unions : (⋃ t ∈ s, J t) = Icc 0 (n : ℝ) := by
    ext y
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨t, ht, hty⟩
      have ha := (Finset.mem_filter.mp ht).2
      have hb : (0,y) ∈ ⋃ t, Icc (a t) (a t+h t) ×ˢ Icc (b t) (b t+w t) :=
        Set.mem_iUnion.mpr ⟨t, ⟨⟨by linarith, by linarith [hh t]⟩, hty⟩⟩
      rw [cover] at hb
      exact hb.2
    · intro hy
      have hz : ((0 : ℝ), y) ∈ Icc 0 2 ×ˢ Icc 0 (n : ℝ) := ⟨⟨le_rfl, by norm_num⟩, hy⟩
      rw [← cover] at hz
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm ht.1.1 (bounds _).1⟩,ht.2⟩
  have hd : Set.Pairwise (s : Set T) (fun t u => AEDisjoint volume (J t) (J u)) := by
    intro t ht u hu ne
    have ht0 := (Finset.mem_filter.mp ht).2
    have hu0 := (Finset.mem_filter.mp hu).2
    have ho : Disjoint (Ioo (b t) (b t+w t)) (Ioo (b u) (b u+w u)) := by
      apply Set.disjoint_left.mpr
      intro y hty huy
      apply (Set.disjoint_left.mp (disj t u ne)) (a := ((1/2 : ℝ), y))
      · exact ⟨⟨by linarith, by linarith [hh t]⟩, hty⟩
      · exact ⟨⟨by linarith, by linarith [hh u]⟩, huy⟩
    exact ho.aedisjoint.congr Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm
  have widths (t : T) : volume.real (J t) = w t := by
    rw [show J t = Icc (b t) (b t+w t) from rfl, Real.volume_real_Icc_of_le (by linarith [hw t])]
    ring
  have ht := measureReal_biUnion_finset₀ hd (fun t _ => measurableSet_Icc.nullMeasurableSet)
    (fun t _ => by exact ne_of_lt measure_Icc_lt_top)
  rw [unions, Real.volume_real_Icc_of_le (Nat.cast_nonneg _), sub_zero] at ht
  simpa only [widths] using ht.symm

end TaskP.RectangleDefect
