import Research.Backfill.Paper3.Proof.Num.RunTD2
import Research.Backfill.Paper3.Proof.Num.RunTD3
import Research.Backfill.Paper3.Proof.Num.RunTD4

/-!
# The Theorem D numerics of §8

Every comparison of `TheoremDNumerics` is read off one of the kernel runs `run_TD2`, `run_TD3`,
`run_TD4` through `cmp_of_run`; the side conditions (the query is in the table, the threshold is
below the truncation degree) are finite checks.
-/

set_option autoImplicit false

namespace P3Num

open Finset BackfillPaper3.Challenge

/-- The side conditions of `cmp_of_run` for one query. -/
def QueryOK (d M T : ℕ) (Q : ℕ → List (ℕ × ℕ)) (m p q c : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ M ∧ (p * d * (2 * d * m) / q, c) ∈ Q m ∧ p * d * (2 * d * m) / q < T

theorem td2_cmp (m p q c : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 2 150 181 qTD2 m p q c)
    (a₁ b₁ a₂ b₂ : Fin 2) :
    cmpN (iGamma (KddUnion m 2) 2 γ) (iGamma (Gn 2 m a₁ b₁ a₂ b₂) 2 γ) = c :=
  cmp_of_run 2 K2 H2 Pd_two a₁ b₁ a₂ b₂ (edgePoly_H2 a₁ b₁ a₂ b₂) 181 qTD2 150 run_TD2 m h.1
    h.2.1 p q γ hγ c h.2.2.1 h.2.2.2

theorem td3_cmp (m p q c : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 3 100 271 qTD3 m p q c)
    (a₁ b₁ a₂ b₂ : Fin 3) :
    cmpN (iGamma (KddUnion m 3) 3 γ) (iGamma (Gn 3 m a₁ b₁ a₂ b₂) 3 γ) = c :=
  cmp_of_run 3 K3 H3 Pd_three a₁ b₁ a₂ b₂ (edgePoly_H3 a₁ b₁ a₂ b₂) 271 qTD3 100 run_TD3 m h.1
    h.2.1 p q γ hγ c h.2.2.1 h.2.2.2

theorem td4_cmp (m p q c : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 4 74 375 qTD4 m p q c)
    (a₁ b₁ a₂ b₂ : Fin 4) :
    cmpN (iGamma (KddUnion m 4) 4 γ) (iGamma (Gn 4 m a₁ b₁ a₂ b₂) 4 γ) = c :=
  cmp_of_run 4 K4 H4 Pd_four a₁ b₁ a₂ b₂ (edgePoly_H4 a₁ b₁ a₂ b₂) 375 qTD4 74 run_TD4 m h.1
    h.2.1 p q γ hγ c h.2.2.1 h.2.2.2

theorem td2_wins (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 2 150 181 qTD2 m p q 0) :
    DWins 2 m γ :=
  (cmpN_eq_zero_iff _ _).1 (td2_cmp m p q 0 γ hγ h _ _ _ _)

theorem td2_loses (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 2 150 181 qTD2 m p q 2) :
    DLoses 2 m γ :=
  (cmpN_eq_two_iff _ _).1 (td2_cmp m p q 2 γ hγ h _ _ _ _)

theorem td3_wins (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 3 100 271 qTD3 m p q 0) :
    DWins 3 m γ :=
  (cmpN_eq_zero_iff _ _).1 (td3_cmp m p q 0 γ hγ h _ _ _ _)

theorem td3_loses (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 3 100 271 qTD3 m p q 2) :
    DLoses 3 m γ :=
  (cmpN_eq_two_iff _ _).1 (td3_cmp m p q 2 γ hγ h _ _ _ _)

theorem td4_wins (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 4 74 375 qTD4 m p q 0) :
    DWins 4 m γ :=
  (cmpN_eq_zero_iff _ _).1 (td4_cmp m p q 0 γ hγ h _ _ _ _)

theorem td4_loses (m p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) (h : QueryOK 4 74 375 qTD4 m p q 2) :
    DLoses 4 m γ :=
  (cmpN_eq_two_iff _ _).1 (td4_cmp m p q 2 γ hγ h _ _ _ _)

theorem gammasWin192_forall (P : ℝ → Prop) (h1 : P (1 / 5)) (h2 : P (1 / 4)) (h3 : P (1 / 3))
    (h4 : P (2 / 5)) (h5 : P (9 / 20)) : ∀ γ ∈ gammasWin192, P γ := by
  intro γ hγ
  simp only [gammasWin192, List.mem_cons, List.mem_nil_iff, or_false] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem range_TD2 : ∀ n ∈ Icc 360 600, 8 ∣ n → QueryOK 2 150 181 qTD2 (n / 4) 3 20 0 := by
  unfold QueryOK
  decide +kernel

theorem range_TD3 : ∀ n ∈ Icc 336 600, 12 ∣ n → QueryOK 3 100 271 qTD3 (n / 6) 3 20 0 := by
  unfold QueryOK
  decide +kernel

theorem range_TD4 : ∀ n ∈ Icc 320 592, 16 ∣ n → QueryOK 4 74 375 qTD4 (n / 8) 3 20 0 := by
  unfold QueryOK
  decide +kernel

theorem theoremDNumerics : TheoremDNumerics := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gammasWin192_forall _
      (td2_wins 48 1 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td2_wins 48 1 4 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td2_wins 48 1 3 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td2_wins 48 2 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td2_wins 48 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel))
  · exact td2_loses 48 3 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact gammasWin192_forall _
      (td3_wins 32 1 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td3_wins 32 1 4 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td3_wins 32 1 3 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td3_wins 32 2 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td3_wins 32 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel))
  · exact td3_loses 32 3 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact gammasWin192_forall _
      (td4_wins 24 1 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td4_wins 24 1 4 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td4_wins 24 1 3 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td4_wins 24 2 5 _ (by norm_num) (by unfold QueryOK; decide +kernel))
      (td4_wins 24 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel))
  · exact td4_loses 24 3 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact td4_loses 16 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact td4_loses 26 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact td3_wins 16 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact td3_wins 32 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · exact td3_loses 24 9 20 _ (by norm_num) (by unfold QueryOK; decide +kernel)
  · intro n hn hdiv
    exact td2_wins (n / 4) 3 20 _ (by norm_num) (range_TD2 n hn hdiv)
  · intro n hn hdiv
    exact td3_wins (n / 6) 3 20 _ (by norm_num) (range_TD3 n hn hdiv)
  · intro n hn hdiv
    exact td4_wins (n / 8) 3 20 _ (by norm_num) (range_TD4 n hn hdiv)

end P3Num
