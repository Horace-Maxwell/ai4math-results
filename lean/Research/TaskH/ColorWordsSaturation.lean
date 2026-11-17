import Research.TaskH.ColorWordsStrict

/-!
Strict non-saturation for a long four-color word. Swapping ranks 0 and 1
adds a descent to the tight word obtained by putting the missing prefix color
first. Saturation of the four-element missing-rank injection would require
both such rank positions, and is therefore impossible.
-/

set_option autoImplicit false

namespace TaskH.ColorWords

variable {k : ℕ}

def swapFour : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem four_swap_step_le (x y : Fin 4) (hnot : ¬ (x = 1 ∧ y = 0)) :
    (if y < x then 1 else 0 : ℕ) ≤
      if swapFour y < swapFour x then 1 else 0 := by
  fin_cases x <;> fin_cases y <;> norm_num [swapFour, Equiv.swap_apply_def] at *

theorem four_swap_increasing_nonzero (x y : Fin 4) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x < y) : swapFour x < swapFour y := by
  fin_cases x <;> fin_cases y <;> norm_num [swapFour, Equiv.swap_apply_def] at *

theorem descents_mono_of_steps (w z : ℕ → Fin k) (L : ℕ)
    (hsteps : ∀ i : ℕ, i < L →
      (if w (i + 1) < w i then 1 else 0 : ℕ) ≤
        if z (i + 1) < z i then 1 else 0) :
    descents w L ≤ descents z L := by
  revert hsteps
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hsteps
    have hi := ih (fun i hi => hsteps i (by omega))
    have hs := hsteps L (by omega)
    rw [descents_succ, descents_succ]
    omega

/-- A long good word whose first color is not rank 0 ceases to be good after
swapping ranks 0 and 1. No extra periodic-word assumption is used. -/
theorem four_swap_exceeds_budget (w : ℕ → Fin 4) (L b : ℕ)
    (hlen : L + 2 = 4 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    b < descents (fun i => swapFour (w i)) L := by
  obtain ⟨_, hcount_eq, _, htight⟩ :=
    four_tight_of_first_ne_zero w L b hlen hne hcount hfirst
  obtain ⟨h0, h1, h2, h3, h4⟩ := four_tight_prefix w L b hlen hb hne hcount hfirst
  have hw0 : w 0 = 1 := Fin.ext h0
  have hw1 : w 1 = 2 := Fin.ext h1
  have hw2 : w 2 = 3 := Fin.ext h2
  have hw3 : w 3 = 0 := Fin.ext h3
  have hw4 : w 4 = 1 := Fin.ext h4
  have hfirst_count : descents w 4 = 1 := by
    norm_num [descents, hw0, hw1, hw2, hw3, hw4]
  have hswap_count : descents (fun i => swapFour (w i)) 4 = 2 := by
    norm_num [descents, hw0, hw1, hw2, hw3, hw4, swapFour, Equiv.swap_apply_def]
  have hno := four_tight_no_one_zero w L hne htight
  have htail := descents_mono_of_steps (fun i => w (4 + i))
    (fun i => swapFour (w (4 + i))) (L - 4) (by
      intro i hi
      exact four_swap_step_le (w (4 + i)) (w (4 + (i + 1)))
        (hno (4 + i) (by omega)))
  have hadd : 4 + (L - 4) = L := by omega
  have hsplit := descents_add w 4 (L - 4)
  rw [hadd, hfirst_count] at hsplit
  have hsplit_swap := descents_add (fun i => swapFour (w i)) 4 (L - 4)
  rw [hadd, hswap_count] at hsplit_swap
  omega

/-- Strictly fewer than four rank orders make a long proper four-color word
have at most `b` descents. This is the actual one-direction strict multiplier
bound, with no assumed rainbow prefix or predetermined missing color. -/
theorem low_descent_orders_card_lt4 (w : ℕ → Fin 4) (L b : ℕ)
    (hlen : L + 2 = 4 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      descents (fun i => π (w i)) L ≤ b)).card < 4 := by
  classical
  let S : Finset (Equiv.Perm (Fin 4)) := Finset.univ.filter
    (fun π => descents (fun i => π (w i)) L ≤ b)
  change S.card < 4
  have hle : S.card ≤ 4 := low_descent_orders_card_le (by omega) w L b hlen hne
  by_contra hnot
  have hcard : S.card = 4 := by omega
  obtain ⟨π₀, hπ₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hπ₀_count : descents (fun i => π₀ (w i)) L ≤ b :=
    (Finset.mem_filter.mp hπ₀).2
  let f : Fin (4 - 1) → Fin 4 := fun i => w i.val
  have hf : Function.Injective f :=
    ranked_prefix_injective (by omega) w π₀ L b hlen hne hπ₀_count
  obtain ⟨β, hmissing, hcover⟩ := exists_missing_prefix_color (by omega) f hf
  have hmono : ∀ π : Equiv.Perm (Fin 4), π ∈ S → StrictMono (fun i => π (f i)) := by
    intro π hπ
    exact ranked_prefix_strictMono (by omega) w π L b hlen hne
      (Finset.mem_filter.mp hπ).2
  have hinj : Set.InjOn (fun π : Equiv.Perm (Fin 4) => π β) (S : Set _) := by
    intro π hπ ρ hρ he
    exact perm_eq_of_missing_rank f β hmissing hcover π ρ (hmono π hπ) (hmono ρ hρ) he
  have hsurj : Set.SurjOn (fun π : Equiv.Perm (Fin 4) => π β) (S : Set _)
      ((Finset.univ : Finset (Fin 4)) : Set _) := by
    apply Finset.surjOn_of_injOn_of_card_le (fun π : Equiv.Perm (Fin 4) => π β)
    · intro π _
      exact Finset.mem_univ _
    · exact hinj
    · simpa only [Finset.card_univ, Fintype.card_fin, hcard] using (Nat.le_refl 4)
  obtain ⟨π, hπ, hπβ⟩ := hsurj (Finset.mem_univ (0 : Fin 4))
  obtain ⟨ρ, hρ, hρβ⟩ := hsurj (Finset.mem_univ (1 : Fin 4))
  change π β = 0 at hπβ
  change ρ β = 1 at hρβ
  let κ : Equiv.Perm (Fin 4) := π.trans swapFour
  have hπmono := hmono π hπ
  have hρmono := hmono ρ hρ
  have hπ_nonzero : ∀ i : Fin (4 - 1), π (f i) ≠ 0 := by
    intro i
    rw [← hπβ]
    exact π.injective.ne (hmissing i)
  have hκmono : StrictMono (fun i => κ (f i)) := by
    intro i j hij
    change swapFour (π (f i)) < swapFour (π (f j))
    exact four_swap_increasing_nonzero _ _ (hπ_nonzero i) (hπ_nonzero j) (hπmono hij)
  have hκβ : κ β = 1 := by
    change swapFour (π β) = 1
    rw [hπβ]
    simp [swapFour]
  have hκρ : κ = ρ := perm_eq_of_missing_rank f β hmissing hcover κ ρ
    hκmono hρmono (hκβ.trans hρβ.symm)
  have hπ_count : descents (fun i => π (w i)) L ≤ b := (Finset.mem_filter.mp hπ).2
  have hswap_low : descents (fun i => swapFour (π (w i))) L ≤ b := by
    change descents (fun i => κ (w i)) L ≤ b
    rw [hκρ]
    exact (Finset.mem_filter.mp hρ).2
  have hfirst : π (w 0) ≠ 0 := hπ_nonzero (0 : Fin (4 - 1))
  have hswap_high := four_swap_exceeds_budget (fun i => π (w i)) L b hlen hb
    (fun i hi => π.injective.ne (hne i hi)) hπ_count hfirst
  omega

end TaskH.ColorWords

#print axioms TaskH.ColorWords.four_swap_step_le
#print axioms TaskH.ColorWords.descents_mono_of_steps
#print axioms TaskH.ColorWords.four_swap_exceeds_budget
#print axioms TaskH.ColorWords.low_descent_orders_card_lt4
