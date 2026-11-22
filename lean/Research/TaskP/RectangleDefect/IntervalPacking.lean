import Research.TaskP.RectangleDefect.RowSplit

namespace TaskP.RectangleDefect

open Set

/-- Lay any finite set of positive widths side by side. The closed intervals cover
both endpoints when the set is nonempty. -/
theorem pack_intervals {T : Type*} [DecidableEq T] (s : Finset T) (w : T → ℝ)
    (hw : ∀ t, 0 < w t) :
    ∃ b : T → ℝ,
      (∀ t ∈ s, 0 ≤ b t ∧ b t + w t ≤ ∑ u ∈ s, w u) ∧
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u → Disjoint (Ioo (b t) (b t+w t)) (Ioo (b u) (b u+w u))) ∧
      (s.Nonempty → ∀ y ∈ Icc 0 (∑ u ∈ s, w u), ∃ t ∈ s, y ∈ Icc (b t) (b t+w t)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨b, hb, hdis, hc⟩ := ih
    let L := ∑ u ∈ s, w u
    have hL : 0 ≤ L := Finset.sum_nonneg (fun u _ => (hw u).le)
    let c := fun t => if t = a then L else b t
    have cA : c a = L := by simp [c]
    have cS {t : T} (ht : t ∈ s) : c t = b t := by
      have ne : t ≠ a := fun he => ha (he ▸ ht)
      simp [c, ne]
    refine ⟨c, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.sum_insert ha]
      rcases Finset.mem_insert.mp ht with rfl | ht
      · rw [cA]
        exact ⟨hL, le_of_eq (add_comm _ _)⟩
      · rw [cS ht]
        exact ⟨(hb _ ht).1, (hb _ ht).2.trans (le_add_of_nonneg_left (hw a).le)⟩
    · intro t ht u hu hne
      apply Set.disjoint_left.mpr
      intro y htY huY
      by_cases hta : t = a
      · subst t
        have hu := (Finset.mem_insert.mp hu).resolve_left hne.symm
        rw [cA] at htY
        rw [cS hu] at huY
        exact (not_lt_of_ge ((huY.2.le.trans (hb u hu).2))) htY.1
      · have ht := (Finset.mem_insert.mp ht).resolve_left hta
        rw [cS ht] at htY
        by_cases hua : u = a
        · subst u
          rw [cA] at huY
          exact (not_lt_of_ge ((htY.2.le.trans (hb t ht).2))) huY.1
        · have hu := (Finset.mem_insert.mp hu).resolve_left hua
          rw [cS hu] at huY
          exact Set.disjoint_left.mp (hdis _ ht _ hu hne) htY huY
    · intro _ y hy
      rw [Finset.sum_insert ha] at hy
      by_cases h : L ≤ y
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        rw [cA, add_comm]
        exact ⟨h,hy.2⟩
      · have hs : s.Nonempty := by
          by_contra! he
          have hz : L = 0 := by simp [L, he]
          exact h (hz ▸ hy.1)
        obtain ⟨t, ht, htY⟩ := hc hs y ⟨hy.1,(lt_of_not_ge h).le⟩
        exact ⟨t, Finset.mem_insert_of_mem ht, (cS ht).symm ▸ htY⟩

end TaskP.RectangleDefect
