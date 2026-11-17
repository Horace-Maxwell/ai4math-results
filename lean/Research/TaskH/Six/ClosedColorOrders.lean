import Research.TaskH.Six.ColorWordsStrict

/-!
The one-direction color-order multiplier bound for a closed proper six-color
word. Closure forces equality in endpoint capacity. The first six ranks then
cycle through every color, and a good order is determined by its starting rank.
No rainbow condition is assumed; it is proved from the actual word conditions.
-/

set_option autoImplicit false

namespace TaskH.Six.ColorWords

open _root_.TaskH.ColorWords

theorem six_step_eq_add_one (x y : Fin 6)
    (he : 1 + x.val = y.val + 6 * (if y < x then 1 else 0)) : y = x + 1 := by
  fin_cases x <;> fin_cases y <;> norm_num at he <;> decide +kernel

theorem six_successor_cover (x z : Fin 6) :
    z = x ∨ z = x + 1 ∨ z = (x + 1) + 1 ∨ z = ((x + 1) + 1) + 1 ∨
      z = (((x + 1) + 1) + 1) + 1 ∨ z = ((((x + 1) + 1) + 1) + 1) + 1 := by
  fin_cases x <;> fin_cases z <;> decide +kernel

theorem six_closed_tight (w : ℕ → Fin 6) (L a : ℕ)
    (hlen : L = 6 * a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    descents w L = a ∧ L + (w 0).val = (w L).val + 6 * descents w L := by
  have hc := endpoint_capacity w L hne
  rw [hclosed] at hc
  have he : descents w L = a := by omega
  exact ⟨he, by rw [hclosed, he, hlen]; omega⟩

theorem six_tight_step_next (w : ℕ → Fin 6) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + 6 * descents w L)
    (j : ℕ) (hj : j < L) : w (j + 1) = w j + 1 := by
  exact six_step_eq_add_one (w j) (w (j + 1)) (tight_step w L hne htight j hj)

/-- The first six entries of a good closed word contain all six colors. -/
theorem six_closed_prefix_surjective (w : ℕ → Fin 6) (L a : ℕ)
    (hlen : L = 6 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    Function.Surjective (fun i : Fin 6 => w i.val) := by
  have ht := (six_closed_tight w L a hlen hne hclosed hcount).2
  have h01 := six_tight_step_next w L hne ht 0 (by omega)
  have h12 := six_tight_step_next w L hne ht 1 (by omega)
  have h23 := six_tight_step_next w L hne ht 2 (by omega)
  have h34 := six_tight_step_next w L hne ht 3 (by omega)
  have h45 := six_tight_step_next w L hne ht 4 (by omega)
  have h02 : w 2 = (w 0 + 1) + 1 := by rw [h12, h01]
  have h03 : w 3 = ((w 0 + 1) + 1) + 1 := by rw [h23, h02]
  have h04 : w 4 = (((w 0 + 1) + 1) + 1) + 1 := by rw [h34, h03]
  have h05 : w 5 = ((((w 0 + 1) + 1) + 1) + 1) + 1 := by rw [h45, h04]
  intro z
  rcases six_successor_cover (w 0) z with hz | hz | hz | hz | hz | hz
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
  · refine ⟨5, ?_⟩
    change w 5 = z
    exact h05.trans hz.symm

/-- Two good color orders with the same starting rank agree everywhere. -/
theorem six_closed_orders_eq_of_start (w : ℕ → Fin 6) (L a : ℕ)
    (hlen : L = 6 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0)
    (π ρ : Equiv.Perm (Fin 6))
    (hπ : descents (fun i => π (w i)) L ≤ a)
    (hρ : descents (fun i => ρ (w i)) L ≤ a) (hstart : π (w 0) = ρ (w 0)) :
    π = ρ := by
  have hpne : ∀ i : ℕ, i < L → π (w i) ≠ π (w (i + 1)) :=
    fun i hi => π.injective.ne (hne i hi)
  have hrne : ∀ i : ℕ, i < L → ρ (w i) ≠ ρ (w (i + 1)) :=
    fun i hi => ρ.injective.ne (hne i hi)
  have hpclosed : π (w L) = π (w 0) := congrArg π hclosed
  have hrclosed : ρ (w L) = ρ (w 0) := congrArg ρ hclosed
  have hpt := (six_closed_tight (fun i => π (w i)) L a hlen hpne hpclosed hπ).2
  have hrt := (six_closed_tight (fun i => ρ (w i)) L a hlen hrne hrclosed hρ).2
  have hpnext := six_tight_step_next (fun i => π (w i)) L hpne hpt
  have hrnext := six_tight_step_next (fun i => ρ (w i)) L hrne hrt
  have h1 : π (w 1) = ρ (w 1) := by
    calc
      π (w 1) = π (w 0) + 1 := hpnext 0 (by omega)
      _ = ρ (w 0) + 1 := congrArg (fun x : Fin 6 => x + 1) hstart
      _ = ρ (w 1) := (hrnext 0 (by omega)).symm
  have h2 : π (w 2) = ρ (w 2) := by
    calc
      π (w 2) = π (w 1) + 1 := hpnext 1 (by omega)
      _ = ρ (w 1) + 1 := congrArg (fun x : Fin 6 => x + 1) h1
      _ = ρ (w 2) := (hrnext 1 (by omega)).symm
  have h3 : π (w 3) = ρ (w 3) := by
    calc
      π (w 3) = π (w 2) + 1 := hpnext 2 (by omega)
      _ = ρ (w 2) + 1 := congrArg (fun x : Fin 6 => x + 1) h2
      _ = ρ (w 3) := (hrnext 2 (by omega)).symm
  have h4 : π (w 4) = ρ (w 4) := by
    calc
      π (w 4) = π (w 3) + 1 := hpnext 3 (by omega)
      _ = ρ (w 3) + 1 := congrArg (fun x : Fin 6 => x + 1) h3
      _ = ρ (w 4) := (hrnext 3 (by omega)).symm
  have h5 : π (w 5) = ρ (w 5) := by
    calc
      π (w 5) = π (w 4) + 1 := hpnext 4 (by omega)
      _ = ρ (w 4) + 1 := congrArg (fun x : Fin 6 => x + 1) h4
      _ = ρ (w 5) := (hrnext 4 (by omega)).symm
  have hpref : ∀ i : Fin 6, π (w i.val) = ρ (w i.val) := by
    intro i
    fin_cases i
    · exact hstart
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  have hpsurj := six_closed_prefix_surjective (fun i => π (w i)) L a
    hlen ha hpne hpclosed hπ
  apply Equiv.ext
  intro c
  obtain ⟨i, hi⟩ := hpsurj (π c)
  have hw : w i.val = c := π.injective hi
  rw [← hw]
  exact hpref i

/-- The actual one-direction multiplier bound for closed proper words. -/
theorem closed_low_descent_orders_card_le6 (w : ℕ → Fin 6) (L a : ℕ)
    (hlen : L = 6 * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 6) =>
      descents (fun i => π (w i)) L ≤ a)).card ≤ 6 := by
  classical
  calc
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 6) =>
        descents (fun i => π (w i)) L ≤ a)).card ≤
        (Finset.univ : Finset (Fin 6)).card := by
      apply Finset.card_le_card_of_injOn (fun π : Equiv.Perm (Fin 6) => π (w 0))
      · intro π _
        exact Finset.mem_univ _
      · intro π hπ ρ hρ he
        exact six_closed_orders_eq_of_start w L a hlen ha hne hclosed π ρ
          (Finset.mem_filter.mp hπ).2 (Finset.mem_filter.mp hρ).2 he
    _ = 6 := by simp

end TaskH.Six.ColorWords

#print axioms TaskH.Six.ColorWords.six_step_eq_add_one
#print axioms TaskH.Six.ColorWords.six_successor_cover
#print axioms TaskH.Six.ColorWords.six_tight_step_next
#print axioms TaskH.Six.ColorWords.six_closed_tight
#print axioms TaskH.Six.ColorWords.six_closed_prefix_surjective
#print axioms TaskH.Six.ColorWords.six_closed_orders_eq_of_start
#print axioms TaskH.Six.ColorWords.closed_low_descent_orders_card_le6
