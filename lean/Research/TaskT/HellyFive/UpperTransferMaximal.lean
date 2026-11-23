import Research.TaskT.HellyFive.UpperTransferGeometry

namespace TaskT.HellyFive.UpperTransfer
open Set FiniteGeometry

/-- Maximal enlargement inside a finite grid box. Each active constraint admits a
single exterior contact point lying in all the other enlarged constraints. -/
theorem maximalContacts {n : ℕ} {ι : Type*} [Fintype ι] {box X : Finset (Grid n)}
    (A : ι → Finset (Grid n)) (hAc : ∀ i, ClosedIn box (A i))
    (hAX : ∀ z ∈ box, (∀ i, z ∈ A i) ↔ z ∈ X)
    (witness : ∀ i, ∃ z ∈ box, z ∉ X ∧ ∀ j, j ≠ i → z ∈ A j) :
    ∃ E : ι → Finset (Grid n),
      (∀ i, ClosedIn box (E i)) ∧ (∀ z ∈ box, (∀ i, z ∈ E i) ↔ z ∈ X) ∧
      ∃ w : ι → Grid n, ∀ i, w i ∈ box ∧ w i ∉ E i ∧
        (∀ j, j ≠ i → w i ∈ E j) ∧ ClosedIn box (insert (w i) (E i)) ∧
        embed (w i) ∈ (poly (insert (w i) (E i))).extremePoints ℝ := by
  classical
  let good (E : ι → Finset (Grid n)) :=
    (∀ i, A i ⊆ E i ∧ ClosedIn box (E i)) ∧
    ∀ z ∈ box, (∀ i, z ∈ E i) ↔ z ∈ X
  let opts := (Fintype.piFinset fun _ : ι => box.powerset).filter good
  have hopt {E : ι → Finset (Grid n)} (h : good E) : E ∈ opts := by
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_powerset.mpr (h.1 i).2.1),h⟩
  have start : good A := ⟨fun i => ⟨Subset.rfl,hAc i⟩, hAX⟩
  obtain ⟨E,hE,hmax⟩ := opts.exists_max_image (fun T => ∑ i, (T i).card) ⟨A,hopt start⟩
  have hgood : good E := (Finset.mem_filter.mp hE).2
  have hchoose (i : ι) : ∃ z ∈ box, z ∉ E i ∧ (∀ j, j ≠ i → z ∈ E j) ∧
      ClosedIn box (insert z (E i)) ∧ embed z ∈ (poly (insert z (E i))).extremePoints ℝ := by
    have hproper : E i ≠ box := by
      obtain ⟨u, hub, hux, hua⟩ := witness i
      intro h
      apply hux ((hgood.2 u hub).mp ?_)
      intro j
      by_cases hj : j = i
      · simpa [hj,h] using hub
      · exact (hgood.1 j).1 (hua j hj)
    obtain ⟨z,hzb,hzE,hins,hext⟩ := extend_closed (hgood.1 i).2 hproper
    refine ⟨z,hzb,hzE,?_,hins,hext⟩
    intro j hji
    by_contra hzj
    let T := Function.update E i (insert z (E i))
    have step (k : ι) : E k ⊆ T k := by
      by_cases h : k = i
      · subst k; simp [T]
      · simp [T, Function.update_of_ne h]
    have hT : good T := by
      refine ⟨fun k => ⟨(hgood.1 k).1.trans (step k), ?_⟩, ?_⟩
      · by_cases h : k = i
        · simpa [T,h] using hins
        · simpa [T,Function.update_of_ne h] using (hgood.1 k).2
      · intro u hu
        refine ⟨fun hall => (hgood.2 u hu).mp (fun k => ?_), fun h k =>
          step k ((hgood.2 u hu).mpr h k)⟩
        by_cases hk : k = i
        · subst k
          have hi : u = z ∨ u ∈ E i := by simpa [T] using hall i
          rcases hi with rfl | hi
          · exact (hzj (by simpa [T,Function.update_of_ne hji] using hall j)).elim
          · exact hi
        · simpa [T,Function.update_of_ne hk] using hall k
    have greater : (∑ k, (E k).card) < ∑ k, (T k).card := by
      apply Finset.sum_lt_sum (fun k _ => Finset.card_le_card (step k))
      exact ⟨i,Finset.mem_univ _, by simp [T, hzE]⟩
    exact greater.not_ge (hmax T (hopt hT))
  choose w hw using hchoose
  exact ⟨E, fun i => (hgood.1 i).2, hgood.2, w, hw⟩

end TaskT.HellyFive.UpperTransfer
