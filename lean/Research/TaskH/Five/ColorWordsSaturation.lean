import Research.TaskH.Five.ColorWordsStrict
import Research.TaskH.ColorWordsSaturation

/-!
Strict non-saturation for a long five-color word. Swapping ranks 0 and 1
adds a descent to the tight word obtained by putting the missing prefix color
first. Saturation of the five-element missing-rank injection would require
both such rank positions, and is therefore impossible.
-/

set_option autoImplicit false

namespace TaskH.Five.ColorWords

open TaskH.ColorWords


def swapFive : Equiv.Perm (Fin 5) := Equiv.swap 0 1

theorem five_swap_step_le (x y : Fin 5) (hnot : ¬ (x = 1 ∧ y = 0)) :
    (if y < x then 1 else 0 : ℕ) ≤
      if swapFive y < swapFive x then 1 else 0 := by
  fin_cases x <;> fin_cases y <;> norm_num [swapFive, Equiv.swap_apply_def] at *

theorem five_swap_increasing_nonzero (x y : Fin 5) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x < y) : swapFive x < swapFive y := by
  fin_cases x <;> fin_cases y <;> norm_num [swapFive, Equiv.swap_apply_def] at *

/-- A long good word whose first color is not rank 0 ceases to be good after
swapping ranks 0 and 1. No extra periodic-word assumption is used. -/
theorem five_swap_exceeds_budget (w : ℕ → Fin 5) (L b : ℕ)
    (hlen : L + 2 = 5 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    b < descents (fun i => swapFive (w i)) L := by
  obtain ⟨_, hcount_eq, _, htight⟩ :=
    five_tight_of_first_ne_zero w L b hlen hne hcount hfirst
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := five_tight_prefix w L b hlen hb hne hcount hfirst
  have hw0 : w 0 = 1 := Fin.ext h0
  have hw1 : w 1 = 2 := Fin.ext h1
  have hw2 : w 2 = 3 := Fin.ext h2
  have hw3 : w 3 = 4 := Fin.ext h3
  have hw4 : w 4 = 0 := Fin.ext h4
  have hw5 : w 5 = 1 := Fin.ext h5
  have hfirst_count : descents w 5 = 1 := by
    norm_num [descents, hw0, hw1, hw2, hw3, hw4, hw5]
  have hswap_count : descents (fun i => swapFive (w i)) 5 = 2 := by
    norm_num [descents, hw0, hw1, hw2, hw3, hw4, hw5, swapFive, Equiv.swap_apply_def]
  have hno := five_tight_no_one_zero w L hne htight
  have htail := descents_mono_of_steps (fun i => w (5 + i))
    (fun i => swapFive (w (5 + i))) (L - 5) (by
      intro i hi
      exact five_swap_step_le (w (5 + i)) (w (5 + (i + 1)))
        (hno (5 + i) (by omega)))
  have hadd : 5 + (L - 5) = L := by omega
  have hsplit := descents_add w 5 (L - 5)
  rw [hadd, hfirst_count] at hsplit
  have hsplit_swap := descents_add (fun i => swapFive (w i)) 5 (L - 5)
  rw [hadd, hswap_count] at hsplit_swap
  omega

/-- Strictly fewer than five rank orders make a long proper five-color word
have at most `b` descents. This is the actual one-direction strict multiplier
bound, with no assumed rainbow prefix or predetermined missing color. -/
theorem low_descent_orders_card_lt5 (w : ℕ → Fin 5) (L b : ℕ)
    (hlen : L + 2 = 5 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 5) =>
      descents (fun i => π (w i)) L ≤ b)).card < 5 := by
  classical
  let S : Finset (Equiv.Perm (Fin 5)) := Finset.univ.filter
    (fun π => descents (fun i => π (w i)) L ≤ b)
  change S.card < 5
  have hle : S.card ≤ 5 := low_descent_orders_card_le (by omega) w L b hlen hne
  by_contra hnot
  have hcard : S.card = 5 := by omega
  obtain ⟨π₀, hπ₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hπ₀_count : descents (fun i => π₀ (w i)) L ≤ b :=
    (Finset.mem_filter.mp hπ₀).2
  let f : Fin (5 - 1) → Fin 5 := fun i => w i.val
  have hf : Function.Injective f :=
    ranked_prefix_injective (by omega) w π₀ L b hlen hne hπ₀_count
  obtain ⟨β, hmissing, hcover⟩ := exists_missing_prefix_color (by omega) f hf
  have hmono : ∀ π : Equiv.Perm (Fin 5), π ∈ S → StrictMono (fun i => π (f i)) := by
    intro π hπ
    exact ranked_prefix_strictMono (by omega) w π L b hlen hne
      (Finset.mem_filter.mp hπ).2
  have hinj : Set.InjOn (fun π : Equiv.Perm (Fin 5) => π β) (S : Set _) := by
    intro π hπ ρ hρ he
    exact perm_eq_of_missing_rank f β hmissing hcover π ρ (hmono π hπ) (hmono ρ hρ) he
  have hsurj : Set.SurjOn (fun π : Equiv.Perm (Fin 5) => π β) (S : Set _)
      ((Finset.univ : Finset (Fin 5)) : Set _) := by
    apply Finset.surjOn_of_injOn_of_card_le (fun π : Equiv.Perm (Fin 5) => π β)
    · intro π _
      exact Finset.mem_univ _
    · exact hinj
    · simpa only [Finset.card_univ, Fintype.card_fin, hcard] using (Nat.le_refl 5)
  obtain ⟨π, hπ, hπβ⟩ := hsurj (Finset.mem_univ (0 : Fin 5))
  obtain ⟨ρ, hρ, hρβ⟩ := hsurj (Finset.mem_univ (1 : Fin 5))
  change π β = 0 at hπβ
  change ρ β = 1 at hρβ
  let κ : Equiv.Perm (Fin 5) := π.trans swapFive
  have hπmono := hmono π hπ
  have hρmono := hmono ρ hρ
  have hπ_nonzero : ∀ i : Fin (5 - 1), π (f i) ≠ 0 := by
    intro i
    rw [← hπβ]
    exact π.injective.ne (hmissing i)
  have hκmono : StrictMono (fun i => κ (f i)) := by
    intro i j hij
    change swapFive (π (f i)) < swapFive (π (f j))
    exact five_swap_increasing_nonzero _ _ (hπ_nonzero i) (hπ_nonzero j) (hπmono hij)
  have hκβ : κ β = 1 := by
    change swapFive (π β) = 1
    rw [hπβ]
    simp [swapFive]
  have hκρ : κ = ρ := perm_eq_of_missing_rank f β hmissing hcover κ ρ
    hκmono hρmono (hκβ.trans hρβ.symm)
  have hπ_count : descents (fun i => π (w i)) L ≤ b := (Finset.mem_filter.mp hπ).2
  have hswap_low : descents (fun i => swapFive (π (w i))) L ≤ b := by
    change descents (fun i => κ (w i)) L ≤ b
    rw [hκρ]
    exact (Finset.mem_filter.mp hρ).2
  have hfirst : π (w 0) ≠ 0 := hπ_nonzero (0 : Fin (5 - 1))
  have hswap_high := five_swap_exceeds_budget (fun i => π (w i)) L b hlen hb
    (fun i hi => π.injective.ne (hne i hi)) hπ_count hfirst
  omega

end TaskH.Five.ColorWords

#print axioms TaskH.Five.ColorWords.swapFive
#print axioms TaskH.Five.ColorWords.five_swap_increasing_nonzero
#print axioms TaskH.Five.ColorWords.five_swap_step_le
#print axioms TaskH.Five.ColorWords.five_swap_exceeds_budget
#print axioms TaskH.Five.ColorWords.low_descent_orders_card_lt5
