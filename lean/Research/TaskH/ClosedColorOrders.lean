import Research.TaskH.ColorWordsStrict

/-!
The one-direction color-order multiplier bound for a closed proper four-color
word. Closure forces equality in endpoint capacity. The first four ranks then
cycle through every color, and a good order is determined by its starting rank.
No rainbow condition is assumed; it is proved from the actual word conditions.
-/

set_option autoImplicit false

namespace TaskH.ColorWords

theorem four_step_eq_add_one (x y : Fin 4)
    (he : 1 + x.val = y.val + 4 * (if y < x then 1 else 0)) : y = x + 1 := by
  fin_cases x <;> fin_cases y <;> norm_num at he <;> decide +kernel

theorem four_successor_cover (x z : Fin 4) :
    z = x ∨ z = x + 1 ∨ z = (x + 1) + 1 ∨ z = ((x + 1) + 1) + 1 := by
  fin_cases x <;> fin_cases z <;> decide +kernel

theorem four_closed_tight (w : ℕ → Fin 4) (L a : ℕ)
    (hlen : L = 4 * a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    descents w L = a ∧ L + (w 0).val = (w L).val + 4 * descents w L := by
  have hc := endpoint_capacity w L hne
  rw [hclosed] at hc
  have he : descents w L = a := by omega
  exact ⟨he, by rw [hclosed, he, hlen]; omega⟩

theorem four_tight_step_next (w : ℕ → Fin 4) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + 4 * descents w L)
    (j : ℕ) (hj : j < L) : w (j + 1) = w j + 1 := by
  exact four_step_eq_add_one (w j) (w (j + 1)) (tight_step w L hne htight j hj)

/-- The first four entries of a good closed word contain all four colors. -/
theorem four_closed_prefix_surjective (w : ℕ → Fin 4) (L a : ℕ)
    (hlen : L = 4 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    Function.Surjective (fun i : Fin 4 => w i.val) := by
  have ht := (four_closed_tight w L a hlen hne hclosed hcount).2
  have h01 := four_tight_step_next w L hne ht 0 (by omega)
  have h12 := four_tight_step_next w L hne ht 1 (by omega)
  have h23 := four_tight_step_next w L hne ht 2 (by omega)
  have h02 : w 2 = (w 0 + 1) + 1 := by rw [h12, h01]
  have h03 : w 3 = ((w 0 + 1) + 1) + 1 := by rw [h23, h02]
  intro z
  rcases four_successor_cover (w 0) z with hz | hz | hz | hz
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

/-- Two good color orders with the same starting rank agree everywhere. -/
theorem four_closed_orders_eq_of_start (w : ℕ → Fin 4) (L a : ℕ)
    (hlen : L = 4 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0)
    (π ρ : Equiv.Perm (Fin 4))
    (hπ : descents (fun i => π (w i)) L ≤ a)
    (hρ : descents (fun i => ρ (w i)) L ≤ a) (hstart : π (w 0) = ρ (w 0)) :
    π = ρ := by
  have hpne : ∀ i : ℕ, i < L → π (w i) ≠ π (w (i + 1)) :=
    fun i hi => π.injective.ne (hne i hi)
  have hrne : ∀ i : ℕ, i < L → ρ (w i) ≠ ρ (w (i + 1)) :=
    fun i hi => ρ.injective.ne (hne i hi)
  have hpclosed : π (w L) = π (w 0) := congrArg π hclosed
  have hrclosed : ρ (w L) = ρ (w 0) := congrArg ρ hclosed
  have hpt := (four_closed_tight (fun i => π (w i)) L a hlen hpne hpclosed hπ).2
  have hrt := (four_closed_tight (fun i => ρ (w i)) L a hlen hrne hrclosed hρ).2
  have hpnext := four_tight_step_next (fun i => π (w i)) L hpne hpt
  have hrnext := four_tight_step_next (fun i => ρ (w i)) L hrne hrt
  have h1 : π (w 1) = ρ (w 1) := by
    calc
      π (w 1) = π (w 0) + 1 := hpnext 0 (by omega)
      _ = ρ (w 0) + 1 := congrArg (fun x : Fin 4 => x + 1) hstart
      _ = ρ (w 1) := (hrnext 0 (by omega)).symm
  have h2 : π (w 2) = ρ (w 2) := by
    calc
      π (w 2) = π (w 1) + 1 := hpnext 1 (by omega)
      _ = ρ (w 1) + 1 := congrArg (fun x : Fin 4 => x + 1) h1
      _ = ρ (w 2) := (hrnext 1 (by omega)).symm
  have h3 : π (w 3) = ρ (w 3) := by
    calc
      π (w 3) = π (w 2) + 1 := hpnext 2 (by omega)
      _ = ρ (w 2) + 1 := congrArg (fun x : Fin 4 => x + 1) h2
      _ = ρ (w 3) := (hrnext 2 (by omega)).symm
  have hpref : ∀ i : Fin 4, π (w i.val) = ρ (w i.val) := by
    intro i
    fin_cases i
    · exact hstart
    · exact h1
    · exact h2
    · exact h3
  have hpsurj := four_closed_prefix_surjective (fun i => π (w i)) L a
    hlen ha hpne hpclosed hπ
  apply Equiv.ext
  intro c
  obtain ⟨i, hi⟩ := hpsurj (π c)
  have hw : w i.val = c := π.injective hi
  rw [← hw]
  exact hpref i

/-- The actual one-direction multiplier bound for closed proper words. -/
theorem closed_low_descent_orders_card_le4 (w : ℕ → Fin 4) (L a : ℕ)
    (hlen : L = 4 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      descents (fun i => π (w i)) L ≤ a)).card ≤ 4 := by
  classical
  calc
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
        descents (fun i => π (w i)) L ≤ a)).card ≤
        (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_le_card_of_injOn (fun π : Equiv.Perm (Fin 4) => π (w 0))
      · intro π _
        exact Finset.mem_univ _
      · intro π hπ ρ hρ he
        exact four_closed_orders_eq_of_start w L a hlen ha hne hclosed π ρ
          (Finset.mem_filter.mp hπ).2 (Finset.mem_filter.mp hρ).2 he
    _ = 4 := by simp

end TaskH.ColorWords

#print axioms TaskH.ColorWords.four_closed_tight
#print axioms TaskH.ColorWords.four_closed_prefix_surjective
#print axioms TaskH.ColorWords.four_closed_orders_eq_of_start
#print axioms TaskH.ColorWords.closed_low_descent_orders_card_le4
