import Research.TaskH.Five.ColorWordsStrict

/-!
The one-direction color-order multiplier bound for a closed proper five-color
word. Closure forces equality in endpoint capacity. The first five ranks then
cycle through every color, and a good order is determined by its starting rank.
No rainbow condition is assumed; it is proved from the actual word conditions.
-/

set_option autoImplicit false

namespace TaskH.Five.ColorWords

open TaskH.ColorWords

theorem five_step_eq_add_one (x y : Fin 5)
    (he : 1 + x.val = y.val + 5 * (if y < x then 1 else 0)) : y = x + 1 := by
  fin_cases x <;> fin_cases y <;> norm_num at he <;> decide +kernel

theorem five_successor_cover (x z : Fin 5) :
    z = x ∨ z = x + 1 ∨ z = (x + 1) + 1 ∨ z = ((x + 1) + 1) + 1 ∨ z = (((x + 1) + 1) + 1) + 1 := by
  fin_cases x <;> fin_cases z <;> decide +kernel

theorem five_closed_tight (w : ℕ → Fin 5) (L a : ℕ)
    (hlen : L = 5 * a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    descents w L = a ∧ L + (w 0).val = (w L).val + 5 * descents w L := by
  have hc := endpoint_capacity w L hne
  rw [hclosed] at hc
  have he : descents w L = a := by omega
  exact ⟨he, by rw [hclosed, he, hlen]; omega⟩

theorem five_tight_step_next (w : ℕ → Fin 5) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + 5 * descents w L)
    (j : ℕ) (hj : j < L) : w (j + 1) = w j + 1 := by
  exact five_step_eq_add_one (w j) (w (j + 1)) (tight_step w L hne htight j hj)

/-- The first five entries of a good closed word contain all five colors. -/
theorem five_closed_prefix_surjective (w : ℕ → Fin 5) (L a : ℕ)
    (hlen : L = 5 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    Function.Surjective (fun i : Fin 5 => w i.val) := by
  have ht := (five_closed_tight w L a hlen hne hclosed hcount).2
  have h01 := five_tight_step_next w L hne ht 0 (by omega)
  have h12 := five_tight_step_next w L hne ht 1 (by omega)
  have h23 := five_tight_step_next w L hne ht 2 (by omega)
  have h34 := five_tight_step_next w L hne ht 3 (by omega)
  have h02 : w 2 = (w 0 + 1) + 1 := by rw [h12, h01]
  have h03 : w 3 = ((w 0 + 1) + 1) + 1 := by rw [h23, h02]
  have h04 : w 4 = (((w 0 + 1) + 1) + 1) + 1 := by rw [h34, h03]
  intro z
  rcases five_successor_cover (w 0) z with hz | hz | hz | hz | hz
  · refine ⟨0, ?_⟩
    change w 0 = z
    exact hz.symm
  · refine ⟨1, ?_⟩
    change w 1 = z
    exact h01.trans hz.symm
  · refine ⟨2, ?_⟩
    change w 2 = z
    exact h02.trans hz.symm
  · refine ⟨3, ?_⟩
    change w 3 = z
    exact h03.trans hz.symm
  · refine ⟨4, ?_⟩
    change w 4 = z
    exact h04.trans hz.symm

/-- Two good color orders with the same starting rank agree everywhere. -/
theorem five_closed_orders_eq_of_start (w : ℕ → Fin 5) (L a : ℕ)
    (hlen : L = 5 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0)
    (π ρ : Equiv.Perm (Fin 5))
    (hπ : descents (fun i => π (w i)) L ≤ a)
    (hρ : descents (fun i => ρ (w i)) L ≤ a) (hstart : π (w 0) = ρ (w 0)) :
    π = ρ := by
  have hpne : ∀ i : ℕ, i < L → π (w i) ≠ π (w (i + 1)) :=
    fun i hi => π.injective.ne (hne i hi)
  have hrne : ∀ i : ℕ, i < L → ρ (w i) ≠ ρ (w (i + 1)) :=
    fun i hi => ρ.injective.ne (hne i hi)
  have hpclosed : π (w L) = π (w 0) := congrArg π hclosed
  have hrclosed : ρ (w L) = ρ (w 0) := congrArg ρ hclosed
  have hpt := (five_closed_tight (fun i => π (w i)) L a hlen hpne hpclosed hπ).2
  have hrt := (five_closed_tight (fun i => ρ (w i)) L a hlen hrne hrclosed hρ).2
  have hpnext := five_tight_step_next (fun i => π (w i)) L hpne hpt
  have hrnext := five_tight_step_next (fun i => ρ (w i)) L hrne hrt
  have h1 : π (w 1) = ρ (w 1) := by
    calc
      π (w 1) = π (w 0) + 1 := hpnext 0 (by omega)
      _ = ρ (w 0) + 1 := congrArg (fun x : Fin 5 => x + 1) hstart
      _ = ρ (w 1) := (hrnext 0 (by omega)).symm
  have h2 : π (w 2) = ρ (w 2) := by
    calc
      π (w 2) = π (w 1) + 1 := hpnext 1 (by omega)
      _ = ρ (w 1) + 1 := congrArg (fun x : Fin 5 => x + 1) h1
      _ = ρ (w 2) := (hrnext 1 (by omega)).symm
  have h3 : π (w 3) = ρ (w 3) := by
    calc
      π (w 3) = π (w 2) + 1 := hpnext 2 (by omega)
      _ = ρ (w 2) + 1 := congrArg (fun x : Fin 5 => x + 1) h2
      _ = ρ (w 3) := (hrnext 2 (by omega)).symm
  have h4 : π (w 4) = ρ (w 4) := by
    calc
      π (w 4) = π (w 3) + 1 := hpnext 3 (by omega)
      _ = ρ (w 3) + 1 := congrArg (fun x : Fin 5 => x + 1) h3
      _ = ρ (w 4) := (hrnext 3 (by omega)).symm
  have hpref : ∀ i : Fin 5, π (w i.val) = ρ (w i.val) := by
    intro i
    fin_cases i
    · exact hstart
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hpsurj := five_closed_prefix_surjective (fun i => π (w i)) L a
    hlen ha hpne hpclosed hπ
  apply Equiv.ext
  intro c
  obtain ⟨i, hi⟩ := hpsurj (π c)
  have hw : w i.val = c := π.injective hi
  rw [← hw]
  exact hpref i

/-- The actual one-direction multiplier bound for closed proper words. -/
theorem closed_low_descent_orders_card_le5 (w : ℕ → Fin 5) (L a : ℕ)
    (hlen : L = 5 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 5) =>
      descents (fun i => π (w i)) L ≤ a)).card ≤ 5 := by
  classical
  calc
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 5) =>
        descents (fun i => π (w i)) L ≤ a)).card ≤
        (Finset.univ : Finset (Fin 5)).card := by
      apply Finset.card_le_card_of_injOn (fun π : Equiv.Perm (Fin 5) => π (w 0))
      · intro π _
        exact Finset.mem_univ _
      · intro π hπ ρ hρ he
        exact five_closed_orders_eq_of_start w L a hlen ha hne hclosed π ρ
          (Finset.mem_filter.mp hπ).2 (Finset.mem_filter.mp hρ).2 he
    _ = 5 := by simp

end TaskH.Five.ColorWords

#print axioms TaskH.Five.ColorWords.five_step_eq_add_one
#print axioms TaskH.Five.ColorWords.five_successor_cover
#print axioms TaskH.Five.ColorWords.five_tight_step_next
#print axioms TaskH.Five.ColorWords.five_closed_tight
#print axioms TaskH.Five.ColorWords.five_closed_prefix_surjective
#print axioms TaskH.Five.ColorWords.five_closed_orders_eq_of_start
#print axioms TaskH.Five.ColorWords.closed_low_descent_orders_card_le5
