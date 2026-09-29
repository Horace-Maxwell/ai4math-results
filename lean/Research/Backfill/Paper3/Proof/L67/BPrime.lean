import Research.Backfill.Paper3.Proof.L67.Lemma6

/-!
# Theorem B′ and the instances `(8, 2, 1/16)`, `(12, 3, 1/36)`

`H_d` is `d`-regular (a valid 2-switch keeps all degrees), bipartite (colour a vertex by its side)
and connected (each copy of `K_{d,d}` minus one edge is connected, and `u₁ w₂` joins the copies).
By Lemma 6, `N_{≤t}(H_d) - N_{≤t}(2K_{d,d}) = 2 [z^t] D`; `[z^0] D`, `[z^1] D` come from the low
coefficients of the `W`'s. For `n = 4d`, `γ ∈ [1/(4d²), 1/(2d²))` gives `⌊γ d n⌋ = 1`.
-/

set_option autoImplicit false

namespace P3L67

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

/-- `K_{d,d}` is `d`-regular. -/
theorem degree_Kdd (d : ℕ) (v : Fin d ⊕ Fin d) : (Kdd d).degree v = d := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  rcases v with x | x <;> simp

/-- `m K_{d,d}` is `d`-regular. -/
theorem degree_KddUnion (m d : ℕ) (v : Fin m × (Fin d ⊕ Fin d)) :
    (KddUnion m d).degree v = d := by
  rw [degree_boxProd, bot_degree, degree_Kdd, zero_add]

theorem regular_Hd (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : (Hd d a₁ b₁ a₂ b₂).IsRegularOfDegree d := by
  intro v
  rw [degree_twoSwitch (H := Hd d a₁ b₁ a₂ b₂) rfl (validSwitch_Hd d a₁ b₁ a₂ b₂) v]
  convert degree_KddUnion 2 d v

theorem bipartite_Hd (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : (Hd d a₁ b₁ a₂ b₂).IsBipartite := by
  refine ⟨Coloring.mk (fun p => if p.2.isLeft then (0 : Fin 2) else 1) ?_⟩
  rintro ⟨k, x | x⟩ ⟨k', y | y⟩ h
  · simp [boxProd_adj] at h
  · simp
  · simp
  · simp [boxProd_adj] at h

theorem connected_Hd (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) :
    (Hd d a₁ b₁ a₂ b₂).Connected := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨a₁', ha₁⟩ := exists_ne a₁
  obtain ⟨b₁', hb₁⟩ := exists_ne b₁
  obtain ⟨a₂', ha₂⟩ := exists_ne a₂
  obtain ⟨b₂', hb₂⟩ := exists_ne b₂
  have adj0 : ∀ x y : Fin d, ¬ (x = a₁ ∧ y = b₁) →
      (Hd d a₁ b₁ a₂ b₂).Adj (0, Sum.inl x) (0, Sum.inr y) := by
    intro x y h
    simp only [not_and] at h
    simpa [boxProd_adj] using h
  have adj1 : ∀ x y : Fin d, ¬ (x = a₂ ∧ y = b₂) →
      (Hd d a₁ b₁ a₂ b₂).Adj (1, Sum.inl x) (1, Sum.inr y) := by
    intro x y h
    simp only [not_and] at h
    simpa [boxProd_adj] using h
  have cross : (Hd d a₁ b₁ a₂ b₂).Adj (0, Sum.inl a₁) (1, Sum.inr b₂) := by
    simp [boxProd_adj]
  have r0 : ∀ v : Fin d ⊕ Fin d, (Hd d a₁ b₁ a₂ b₂).Reachable (0, Sum.inl a₁') (0, v) := by
    rintro (x | y)
    · exact (adj0 a₁' b₁' (fun h => ha₁ h.1)).reachable.trans
        (adj0 x b₁' (fun h => hb₁ h.2)).symm.reachable
    · exact (adj0 a₁' y (fun h => ha₁ h.1)).reachable
  have r1 : ∀ v : Fin d ⊕ Fin d, (Hd d a₁ b₁ a₂ b₂).Reachable (1, Sum.inl a₂') (1, v) := by
    rintro (x | y)
    · exact (adj1 a₂' b₂' (fun h => ha₂ h.1)).reachable.trans
        (adj1 x b₂' (fun h => hb₂ h.2)).symm.reachable
    · exact (adj1 a₂' y (fun h => ha₂ h.1)).reachable
  have link : (Hd d a₁ b₁ a₂ b₂).Reachable (0, Sum.inl a₁') (1, Sum.inl a₂') :=
    ((r0 (Sum.inl a₁)).trans cross.reachable).trans (r1 (Sum.inr b₂)).symm
  rw [connected_iff_exists_forall_reachable]
  refine ⟨(0, Sum.inl a₁'), ?_⟩
  rintro ⟨k, v⟩
  fin_cases k
  · exact r0 v
  · exact link.trans (r1 v)

/-- Lemma 6 with no extra graph: `N_{≤t}(H_d) - N_{≤t}(2K_{d,d}) = 2 [z^t] D`. -/
theorem iCount_Hd_sub (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) (t : ℕ) :
    (iCount (Hd d a₁ b₁ a₂ b₂) t : ℤ) - iCount (KddUnion 2 d) t = 2 * (Dpoly d).coeff t := by
  rw [iCount_eq_sum_coeff, iCount_eq_sum_coeff, ← Finset.sum_sub_distrib]
  have hH : edgePoly (Hd d a₁ b₁ a₂ b₂) = edgePoly (KddUnion 2 d) - 2 * (X - 1) * Dpoly d := by
    rw [← lemma6_poly d hd a₁ b₁ a₂ b₂]
    ring
  have hC : (C (-2 : ℤ) : ℤ[X]) = -2 := by simp
  have e : ∀ s, (edgePoly (Hd d a₁ b₁ a₂ b₂)).coeff s - (edgePoly (KddUnion 2 d)).coeff s =
      -2 * ((X - 1) * Dpoly d).coeff s := by
    intro s
    have hp : edgePoly (KddUnion 2 d) - 2 * (X - 1) * Dpoly d - edgePoly (KddUnion 2 d) =
        C (-2) * ((X - 1) * Dpoly d) := by
      rw [hC]
      ring
    rw [hH, ← coeff_sub, hp, coeff_C_mul]
  simp only [e]
  rw [← Finset.mul_sum, sum_coeff_X_sub_one_mul]
  ring

theorem coeff_mul_one (p q : ℤ[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

/-- `[z^0] D = -(2^{d-1} - 1)²` (with `d = n + 1`). -/
theorem coeff_D_zero (n : ℕ) : (Dpoly (n + 1)).coeff 0 = -(2 ^ n - 1) ^ 2 := by
  rw [Dpoly, coeff_sub, mul_coeff_zero, pow_two, mul_coeff_zero, coeff_W00_zero, coeff_W11_zero,
    coeff_W10_zero]
  ring

/-- `[z^1] D = (d - 1)(2^d + d - 3)` (with `d = n + 1`, `n ≥ 1`). -/
theorem coeff_D_one (n : ℕ) (hn : 0 < n) :
    (Dpoly (n + 1)).coeff 1 = n * (2 ^ (n + 1) + n - 2) := by
  rw [Dpoly, coeff_sub, coeff_mul_one, pow_two, coeff_mul_one, coeff_W00_zero, coeff_W11_zero,
    coeff_W10_zero, coeff_W00_one n hn, coeff_W11_one n hn, coeff_W10_one n hn]
  ring

/-- **Theorem B′.** -/
theorem theoremBprime : TheoremBprime := by
  intro d hd a₁ b₁ a₂ b₂
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 0 < n := by omega
  have h4 : (4 : ℤ) ≤ 2 ^ (n + 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hcount1 : (iCount (Hd (n + 1) a₁ b₁ a₂ b₂) 1 : ℤ) - iCount (KddUnion 2 (n + 1)) 1 =
      2 * (((n + 1 : ℕ) : ℤ) - 1) * (2 ^ (n + 1) + ((n + 1 : ℕ) : ℤ) - 3) := by
    rw [iCount_Hd_sub (n + 1) hd a₁ b₁ a₂ b₂ 1, coeff_D_one n hn]
    push_cast
    ring
  have hpos : 0 < 2 * (((n + 1 : ℕ) : ℤ) - 1) * (2 ^ (n + 1) + ((n + 1 : ℕ) : ℤ) - 3) := by
    push_cast
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  refine ⟨regular_Hd _ _ _ _ _, bipartite_Hd _ _ _ _ _, connected_Hd _ hd _ _ _ _, hcount1, hpos,
    ?_, ?_⟩
  · rw [iCount_Hd_sub (n + 1) hd a₁ b₁ a₂ b₂ 0, coeff_D_zero n, Nat.add_sub_cancel]
    ring
  · intro γ hγ1 hγ2 hQ
    have hcard : Fintype.card (Fin 2 × (Fin (n + 1) ⊕ Fin (n + 1))) = 4 * (n + 1) := by
      simp [Fintype.card_prod, Fintype.card_sum]
      ring
    have h := hQ (Fin 2 × (Fin (n + 1) ⊕ Fin (n + 1))) (Hd (n + 1) a₁ b₁ a₂ b₂) hcard
      (regular_Hd _ _ _ _ _) (bipartite_Hd _ _ _ _ _)
    have h42 : 4 * (n + 1) / (2 * (n + 1)) = 2 := by
      rw [show 4 * (n + 1) = 2 * (2 * (n + 1)) by ring]
      exact Nat.mul_div_cancel _ (by omega)
    rw [h42] at h
    have hγ0 : 0 ≤ γ := le_trans (by positivity) hγ1
    rw [iGamma_eq_iCount_floor _ _ hγ0, iGamma_eq_iCount_floor _ _ hγ0, hcard] at h
    have hfl : ⌊γ * ((n + 1 : ℕ) : ℝ) * ((4 * (n + 1) : ℕ) : ℝ)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by positivity)]
      have e1 := (div_le_iff₀ (by positivity)).1 hγ1
      have e2 := (lt_div_iff₀ (by positivity)).1 hγ2
      push_cast at e1 e2 ⊢
      constructor <;> nlinarith
    rw [hfl] at h
    have hlt : (iCount (KddUnion 2 (n + 1)) 1 : ℤ) < iCount (Hd (n + 1) a₁ b₁ a₂ b₂) 1 := by
      linarith
    omega

/-- A counterexample to the bipartite question is one to the question. -/
theorem not_careniniQuestion_of_bip {n d : ℕ} {γ : ℝ} (h : ¬ CareniniQuestionBip n d γ) :
    ¬ CareniniQuestion n d γ :=
  fun hQ => h fun V _ _ G _ hc hr _ => hQ V G hc hr

theorem neg_8_2 : Neg_8_2 :=
  not_careniniQuestion_of_bip
    ((theoremBprime 2 le_rfl 0 0 0 0).2.2.2.2.2.2 (1 / 16) (by norm_num) (by norm_num))

theorem neg_12_3_bip : Neg_12_3_bip :=
  not_careniniQuestion_of_bip
    ((theoremBprime 3 (by norm_num) 0 0 0 0).2.2.2.2.2.2 (1 / 36) (by norm_num) (by norm_num))

end P3L67
