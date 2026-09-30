import Research.Backfill.Paper8.Proof.Main.Lemma32

/-!
# Paper 8, agent `main`: Proposition 5.6

The switchings `sw56a`, `sw56b`, `sw56c` are good, by Lemma 3.2 (`lemma_3_2`). By
`isSecular_iff` the secular values are `±2` for `T(2,2)` and `T(3)` and `±1, ±2` for `T(2,0,0)`;
`G_s` is evaluated at them with `Gs_eq`. (L) and (Z) are checked directly, the counts `k_b` by
`decide`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Main

theorem sq_eq_four {θ : ℝ} (h : θ ^ 2 = 4) : θ = 2 ∨ θ = -2 := by
  have h' : (θ - 2) * (θ + 2) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-! ### (a) `T(2,2)` -/

theorem lam_56a_0 : lam (![2, 2] : Fin 2 → ℕ) sw56a 0 = 2 := by
  simp only [lam, sw56a, mkSw]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem lam_56a_1 : lam (![2, 2] : Fin 2 → ℕ) sw56a 1 = -2 := by
  simp only [lam, sw56a, mkSw]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem condS_56a : condS (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro θ hθ
  obtain ⟨hne, hF⟩ := (isSecular_iff _ θ).1 hθ
  rw [Fin.sum_univ_two] at hF
  have h0 := hne 0
  simp at hF h0
  field_simp at hF
  have h4 : θ ^ 2 = 4 := by linarith
  rw [Gs_eq, Fin.sum_univ_two, lam_56a_0, lam_56a_1]
  simp only [sc, sig, sw56a, mkSw]
  rcases sq_eq_four h4 with rfl | rfl <;> norm_num

theorem condL_56a : condL (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro b hb _ _ θ hθ
  obtain ⟨i, rfl⟩ := (mem_Bset_iff _ b).1 hb
  have hi : (![2, 2] : Fin 2 → ℕ) i = 2 := by fin_cases i <;> rfl
  rw [hi] at hθ ⊢
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    norm_num at hθ
  refine ⟨0, (mem_Ib_iff _ _ _).2 rfl, 1, (mem_Ib_iff _ _ _).2 rfl, ?_⟩
  rw [lam_56a_0, lam_56a_1, ← sub_ne_zero]
  simp only [sig, sw56a, mkSw]
  rw [show (1 + 2 / θ) - (1 + -2 / θ) = 4 / θ by ring]
  exact div_ne_zero (by norm_num) hθ0

theorem condZ_56a : condZ (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro _
  have hk : kb (branchMS (![2, 2] : Fin 2 → ℕ)) 0 = 0 := by decide
  refine ⟨fun h => by omega, fun _ => Or.inr ?_⟩
  rw [Fin.sum_univ_two, lam_56a_0, lam_56a_1]
  norm_num [sc, sw56a, mkSw]

/-! ### (b) `T(2,0,0)` -/

theorem lam_56b (i : Fin 3) : lam (![2, 0, 0] : Fin 3 → ℕ) sw56b i = 0 := by
  simp only [lam, sw56b, mkSw]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
  fin_cases i <;> simp [Finset.sum_range_succ]

theorem condS_56b : condS (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro θ hθ
  obtain ⟨hne, hF⟩ := (isSecular_iff _ θ).1 hθ
  rw [Fin.sum_univ_three] at hF
  have h0 := hne 0
  have h1 := hne 1
  simp at hF h0 h1
  field_simp at hF
  have key : (θ - 1) * (θ + 1) * (θ - 2) * (θ + 2) = 0 := by linear_combination -hF
  rw [Gs_eq, Fin.sum_univ_three]
  simp only [lam_56b]
  simp only [sc, sig, sw56b, mkSw]
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · obtain rfl : θ = 1 := by linarith
        norm_num
      · obtain rfl : θ = -1 := by linarith
        norm_num
    · obtain rfl : θ = 2 := by linarith
      norm_num
  · obtain rfl : θ = -2 := by linarith
    norm_num

theorem condL_56b : condL (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro b hb hb1 hb2
  exfalso
  obtain ⟨i, rfl⟩ := (mem_Bset_iff _ b).1 hb
  fin_cases i
  · exact absurd hb2 (by decide)
  · exact absurd hb1 (by decide)
  · exact absurd hb1 (by decide)

theorem condZ_56b : condZ (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro _
  have hk : kb (branchMS (![2, 0, 0] : Fin 3 → ℕ)) 0 = 2 := by decide
  refine ⟨fun _ => Or.inl ⟨0, by decide, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩, fun h => by omega⟩
  norm_num [sw56b, mkSw]

/-! ### (c) `T(3)` -/

theorem lam_56c : lam (![3] : Fin 1 → ℕ) sw56c 0 = -1 := by
  simp only [lam, sw56c, mkSw]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
  norm_num [Finset.sum_range_succ]

theorem condS_56c : condS (![3] : Fin 1 → ℕ) sw56c := by
  intro θ hθ
  obtain ⟨hne, hF⟩ := (isSecular_iff _ θ).1 hθ
  have h0 := hne 0
  simp at hF h0
  have h4 : θ ^ 2 = 4 := by
    field_simp at hF
    linarith
  rw [Gs_eq, Fin.sum_univ_one, lam_56c]
  simp only [sc, sig, sw56c, mkSw]
  rcases sq_eq_four h4 with rfl | rfl <;> norm_num

theorem condL_56c : condL (![3] : Fin 1 → ℕ) sw56c := by
  intro b hb _ hb2
  exfalso
  obtain ⟨i, rfl⟩ := (mem_Bset_iff _ b).1 hb
  fin_cases i
  exact absurd hb2 (by decide)

theorem condZ_56c : condZ (![3] : Fin 1 → ℕ) sw56c := by
  intro _
  have hk : kb (branchMS (![3] : Fin 1 → ℕ)) 0 = 0 := by decide
  refine ⟨fun h => by omega, fun _ => Or.inl ⟨0, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩⟩
  norm_num [sw56c, mkSw]

/-- **Proposition 5.6.** -/
theorem prop_5_6 : Prop_5_6 :=
  ⟨⟨(lemma_3_2 _ _).2 ⟨condS_56a, condL_56a, condZ_56a⟩, by simp [Fin.sum_univ_two]⟩,
    ⟨(lemma_3_2 _ _).2 ⟨condS_56b, condL_56b, condZ_56b⟩, by simp [Fin.sum_univ_three]⟩,
    ⟨(lemma_3_2 _ _).2 ⟨condS_56c, condL_56c, condZ_56c⟩, by simp⟩⟩

end P8Main
