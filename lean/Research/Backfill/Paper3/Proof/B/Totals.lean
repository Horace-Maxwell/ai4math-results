import Research.Backfill.Paper3.Proof.B.Count

/-!
# The counts `N_{≤1}(K_{d,d})`, `N_{≤1}(S_d)`, `i_0(S_d)`

From the characterisations of `Research.Backfill.Paper3.Proof.B.Count`: `N_{≤1}(K_{d,d}) = 2^{d+1} - 1 + d²` (independent
sets plus the `d²` single edges), `N_{≤1}(S_d) = N_{≤1}(K_{d,d}) + 4(d - 2)` (the inclusion and
the four families of `d - 2` extra sets), and `i_0(S_d) = 3·2^{d-1} + 1`.
-/

set_option autoImplicit false

namespace P3B

open Finset SimpleGraph BackfillPaper3.Challenge

theorem card_filter_ne_empty_and {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset α → Prop) [DecidablePred R] (h : R ∅) :
    #(univ.filter fun T : Finset α => T ≠ ∅ ∧ R T) = #(univ.filter R) - 1 := by
  have hset : (univ.filter fun T : Finset α => T ≠ ∅ ∧ R T) = (univ.filter R).erase ∅ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [hset, Finset.card_erase_of_mem (by simp [h])]

theorem card_filter_eq_single {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    #(univ.filter fun x : α => x = a) = 1 := by
  simp [Finset.filter_eq']

/-- `N_{≤t}(K_{d,d}) = #{(S, T) : |S||T| ≤ t}`. -/
theorem iCount_kdd_eq_sum (d t : ℕ) :
    iCount (Kdd d) t =
      ∑ S : Finset (Fin d), ∑ T : Finset (Fin d), if #S * #T ≤ t then 1 else 0 := by
  rw [iCount_eq_sum_sum]
  simp only [P3Basic.edgesIn_Kdd]

/-- `N_{≤1}(K_{d,d}) = 2^{d+1} - 1 + d²`. -/
theorem iCount_kdd_one (d : ℕ) : iCount (Kdd d) 1 = 2 ^ (d + 1) - 1 + d ^ 2 := by
  have h0 := P3Basic.check_KddIndependentSets d
  rw [iCount_kdd_eq_sum] at h0 ⊢
  have hpt : ∀ S T : Finset (Fin d), (if #S * #T ≤ 1 then 1 else 0 : ℕ) =
      (if #S * #T ≤ 0 then 1 else 0) + (if #S = 1 then 1 else 0) * (if #T = 1 then 1 else 0) := by
    intro S T
    by_cases h : #S * #T ≤ 0
    · have h' : ¬ #S = 1 ∨ ¬ #T = 1 := by
        by_cases hs : #S = 1
        · refine Or.inr fun ht => ?_
          rw [hs, ht] at h
          omega
        · exact Or.inl hs
      rw [ite_eq_left (by omega : #S * #T ≤ 1), ite_eq_left h]
      rcases h' with h' | h' <;> simp [h']
    · by_cases h1 : #S * #T ≤ 1
      · obtain ⟨hs, ht⟩ := mul_eq_one_cases (by omega : #S * #T = 1)
        rw [ite_eq_left h1, ite_eq_right h, ite_eq_left hs, ite_eq_left ht]
      · have h' : ¬ #S = 1 ∨ ¬ #T = 1 := by
          by_cases hs : #S = 1
          · refine Or.inr fun ht => ?_
            rw [hs, ht] at h1
            omega
          · exact Or.inl hs
        rw [ite_eq_right h1, ite_eq_right h]
        rcases h' with h' | h' <;> simp [h']
  simp only [hpt, Finset.sum_add_distrib]
  rw [h0, ← Finset.sum_mul_sum, ← Finset.card_filter, card_filter_card_eq_one, sq]

section Sd

variable {d : ℕ} {a₁ a₂ b₁ b₂ : Fin d}

/-- The number of sets with `e_{S_d} ≤ 1 < e_{K_{d,d}}` is `4(d - 2)`. -/
theorem sd_extra_count (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    (∑ S : Finset (Fin d), ∑ T : Finset (Fin d),
      if edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 1 ∧ ¬ #S * #T ≤ 1 then 1 else 0 : ℕ) =
      4 * (d - 2) := by
  have hpt : ∀ S T : Finset (Fin d),
      (if edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 1 ∧ ¬ #S * #T ≤ 1 then 1 else 0 : ℕ) =
        (if S = {a₁} ∧ (b₁ ∈ T ∧ b₂ ∉ T ∧ #T = 2) then 1 else 0) +
        (if S = {a₂} ∧ (b₂ ∈ T ∧ b₁ ∉ T ∧ #T = 2) then 1 else 0) +
        (if T = {b₁} ∧ (a₁ ∈ S ∧ a₂ ∉ S ∧ #S = 2) then 1 else 0) +
        (if T = {b₂} ∧ (a₂ ∈ S ∧ a₁ ∉ S ∧ #S = 2) then 1 else 0) := by
    intro S T
    have h12 : ¬ ((S = {a₁} ∧ (b₁ ∈ T ∧ b₂ ∉ T ∧ #T = 2)) ∧
        (S = {a₂} ∧ (b₂ ∈ T ∧ b₁ ∉ T ∧ #T = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨h, -⟩⟩
      exact ha (Finset.singleton_inj.mp h)
    have h13 : ¬ ((S = {a₁} ∧ (b₁ ∈ T ∧ b₂ ∉ T ∧ #T = 2)) ∧
        (T = {b₁} ∧ (a₁ ∈ S ∧ a₂ ∉ S ∧ #S = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, -, -, h⟩⟩
      simp at h
    have h14 : ¬ ((S = {a₁} ∧ (b₁ ∈ T ∧ b₂ ∉ T ∧ #T = 2)) ∧
        (T = {b₂} ∧ (a₂ ∈ S ∧ a₁ ∉ S ∧ #S = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, -, -, h⟩⟩
      simp at h
    have h23 : ¬ ((S = {a₂} ∧ (b₂ ∈ T ∧ b₁ ∉ T ∧ #T = 2)) ∧
        (T = {b₁} ∧ (a₁ ∈ S ∧ a₂ ∉ S ∧ #S = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, -, -, h⟩⟩
      simp at h
    have h24 : ¬ ((S = {a₂} ∧ (b₂ ∈ T ∧ b₁ ∉ T ∧ #T = 2)) ∧
        (T = {b₂} ∧ (a₂ ∈ S ∧ a₁ ∉ S ∧ #S = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, -, -, h⟩⟩
      simp at h
    have h34 : ¬ ((T = {b₁} ∧ (a₁ ∈ S ∧ a₂ ∉ S ∧ #S = 2)) ∧
        (T = {b₂} ∧ (a₂ ∈ S ∧ a₁ ∉ S ∧ #S = 2))) := by
      rintro ⟨⟨rfl, -⟩, ⟨h, -⟩⟩
      exact hb (Finset.singleton_inj.mp h)
    rw [← ite_or4 h12 h13 h14 h23 h24 h34]
    exact if_congr (sd_extra_iff ha hb S T) rfl rfl
  simp only [hpt, Finset.sum_add_distrib, sum_sum_ite_eq_and, sum_sum_ite_and_eq]
  rw [card_filter_pair hb, card_filter_pair hb.symm, card_filter_pair ha, card_filter_pair ha.symm]
  omega

/-- `N_{≤1}(S_d) = N_{≤1}(K_{d,d}) + 4(d - 2)`. -/
theorem iCount_sd_one (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    iCount (Sd d a₁ a₂ b₁ b₂) 1 = iCount (Kdd d) 1 + 4 * (d - 2) := by
  rw [iCount_eq_sum_sum, iCount_kdd_eq_sum, ← sd_extra_count ha hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : #S * #T ≤ 1
  · rw [ite_eq_left (sd_le_one_of_kdd ha hb S T h), ite_eq_left h,
      ite_eq_right (fun hc => hc.2 h)]
  · rw [ite_eq_right h, zero_add]
    by_cases he : edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 1
    · rw [ite_eq_left he, ite_eq_left ⟨he, h⟩]
    · rw [ite_eq_right he, ite_eq_right (fun hc => he hc.1)]

/-- `i_0(S_d) = 3·2^{d-1} + 1`. -/
theorem iCount_sd_zero (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (hd : 2 ≤ d) :
    iCount (Sd d a₁ a₂ b₁ b₂) 0 = 3 * 2 ^ (d - 1) + 1 := by
  rw [iCount_eq_sum_sum]
  have hpt : ∀ S T : Finset (Fin d),
      (if edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 0 then 1 else 0 : ℕ) =
        (if T = ∅ ∧ ¬ (a₁ ∈ S ∧ a₂ ∈ S) then 1 else 0) +
        (if S = ∅ ∧ (T ≠ ∅ ∧ ¬ (b₁ ∈ T ∧ b₂ ∈ T)) then 1 else 0) +
        (if S = {a₁} ∧ T = {b₁} then 1 else 0) + (if S = {a₂} ∧ T = {b₂} then 1 else 0) := by
    intro S T
    have h12 : ¬ ((T = ∅ ∧ ¬ (a₁ ∈ S ∧ a₂ ∈ S)) ∧
        (S = ∅ ∧ (T ≠ ∅ ∧ ¬ (b₁ ∈ T ∧ b₂ ∈ T)))) := by
      rintro ⟨⟨h1, -⟩, ⟨-, h2, -⟩⟩
      exact h2 h1
    have h13 : ¬ ((T = ∅ ∧ ¬ (a₁ ∈ S ∧ a₂ ∈ S)) ∧ (S = {a₁} ∧ T = {b₁})) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, h⟩⟩
      exact Finset.singleton_ne_empty b₁ h.symm
    have h14 : ¬ ((T = ∅ ∧ ¬ (a₁ ∈ S ∧ a₂ ∈ S)) ∧ (S = {a₂} ∧ T = {b₂})) := by
      rintro ⟨⟨rfl, -⟩, ⟨-, h⟩⟩
      exact Finset.singleton_ne_empty b₂ h.symm
    have h23 : ¬ ((S = ∅ ∧ (T ≠ ∅ ∧ ¬ (b₁ ∈ T ∧ b₂ ∈ T))) ∧ (S = {a₁} ∧ T = {b₁})) := by
      rintro ⟨⟨rfl, -⟩, ⟨h, -⟩⟩
      exact Finset.singleton_ne_empty a₁ h.symm
    have h24 : ¬ ((S = ∅ ∧ (T ≠ ∅ ∧ ¬ (b₁ ∈ T ∧ b₂ ∈ T))) ∧ (S = {a₂} ∧ T = {b₂})) := by
      rintro ⟨⟨rfl, -⟩, ⟨h, -⟩⟩
      exact Finset.singleton_ne_empty a₂ h.symm
    have h34 : ¬ ((S = {a₁} ∧ T = {b₁}) ∧ (S = {a₂} ∧ T = {b₂})) := by
      rintro ⟨⟨rfl, -⟩, ⟨h, -⟩⟩
      exact ha (Finset.singleton_inj.mp h)
    rw [← ite_or4 h12 h13 h14 h23 h24 h34]
    exact if_congr (sd_indep_iff ha hb S T) rfl rfl
  simp only [hpt, Finset.sum_add_distrib, sum_sum_ite_eq_and, sum_sum_ite_and_eq]
  rw [card_filter_ne_empty_and _ (by simp), card_filter_not_mem_mem ha, card_filter_not_mem_mem hb,
    card_filter_eq_single, card_filter_eq_single]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have h1 : k + 2 - 2 = k := by omega
  have h2 : k + 2 - 1 = k + 1 := by omega
  rw [h1, h2, pow_succ, pow_succ]
  have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

end Sd

end P3B
