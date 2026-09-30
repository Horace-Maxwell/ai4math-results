import Research.Backfill.Paper8.Proof.Small.Setup
import Research.Backfill.Paper8.Proof.Small.Alg
import Research.Backfill.Paper8.Proof.Small.LamStd
import Research.Backfill.Paper8.Proof.Small.CasesABC

/-!
# Paper 8, Proposition 5.1 (d), (e)

Assuming `Lemma_3_2`, the switching `s⁺` (`s_c = 1`, all `σ_i = 1`, leaf signs `λ°_i`) is good
when `k₀ ≤ 1` (and `b* ≤ 1`, `n ≥ 3`); for (d) this gives the required `ε = 1`. (S): the algebra
of `Research.Backfill.Paper8.Proof.Small.Alg` with `Λ°₁ = 2 - k₁` (`k₁ ≥ 2`) or `-1` (`k₁ = 1`). (L): `λ°` takes both values
`±1` on `I₁` when `k₁ ≥ 2`. (Z): for `k₀ = 1` the kernel of `A` is zero; for `k₀ = 0`,
`s_c = 1 ≠ Λ°₁`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Small

variable {k : ℕ} (a : Fin k → ℕ)

theorem sum_single_leaf {i : Fin k} (hi : a i = 1) (g : Fin (a i) → ℝ) :
    ∑ j, g j = g ⟨0, by omega⟩ := by
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · intro j _ hj
    exfalso
    apply hj
    ext
    have := j.isLt
    simp only
    omega
  · simp

/-- For `k₀ = 1` and `b* ≤ 1`, `0` is not an eigenvalue of `A`. -/
theorem ker_trivial (ha : ∀ i, a i ≤ 1) (hk0 : kb (branchMS a) 0 = 1) :
    ¬ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0 := by
  rintro ⟨x, hx, hAx⟩
  apply hx
  have hAx' : adjT a *ᵥ x = (0 : ℝ) • x := by
    rw [zero_smul]
    exact hAx
  obtain ⟨h0, h1, h2⟩ := (P8Basic.mulVec_eq_smul_iff a x 0).1 hAx'
  obtain ⟨i0, hI0⟩ : ∃ i0, Ib a 0 = {i0} := Finset.card_eq_one.1 (by rw [← kb_eq]; exact hk0)
  have hai0 : a i0 = 0 := (mem_Ib a).1 (by rw [hI0]; exact Finset.mem_singleton_self i0)
  have hother : ∀ i, i ≠ i0 → a i = 1 := by
    intro i hi
    have h3 := ha i
    have h4 : a i ≠ 0 := by
      intro h
      have h5 : i ∈ Ib a 0 := (mem_Ib a).2 h
      rw [hI0, Finset.mem_singleton] at h5
      exact hi h5
    omega
  have hc : x none = 0 := by
    have h5 := h1 i0
    rw [Finset.sum_eq_zero (fun j _ => absurd j.isLt (by omega))] at h5
    linarith
  have hv : ∀ i, i ≠ i0 → x (some ⟨i, none⟩) = 0 := by
    intro i hi
    have h5 := h2 i ⟨0, by rw [hother i hi]; norm_num⟩
    linarith
  have hv0 : x (some ⟨i0, none⟩) = 0 := by
    rw [Finset.sum_eq_single i0 (fun i _ hi => hv i hi) (by simp)] at h0
    linarith
  have hl : ∀ i (j : Fin (a i)), x (some ⟨i, some j⟩) = 0 := by
    intro i j
    have hai : a i = 1 := by
      have := j.isLt
      have := ha i
      omega
    have h5 := h1 i
    rw [hc, sum_single_leaf a hai] at h5
    have hj : j = ⟨0, by omega⟩ := by
      ext
      have := j.isLt
      simp only
      omega
    rw [hj]
    linarith
  funext v
  rcases v with _ | ⟨i, _ | j⟩
  · exact hc
  · by_cases hi : i = i0
    · subst hi
      exact hv0
    · exact hv i hi
  · exact hl i j

/-- The switching `s⁺` of Proposition 5.1(d), (e). -/
noncomputable abbrev sPlus : TV a → ℝ := mkSw a 1 (fun _ => 1) (fun i _ => (lamStd a i : ℝ))

theorem sPlus_isSwitching (ha : ∀ i, a i ≤ 1) : IsSwitching (sPlus a) := by
  apply isSwitching_mkSw
  · left
    rfl
  · intro _
    left
    rfl
  · intro i j
    have hai : a i = 1 := by
      have := j.isLt
      have := ha i
      omega
    exact lamStd_pm a hai

theorem sPlus_Sb (b : ℕ) : Sb a (sPlus a) b = kb (branchMS a) b := by
  rw [Sb_mkSw, kb_eq]
  simp

theorem sPlus_Ab0 : Ab a (sPlus a) 0 = kb (branchMS a) 0 := by
  simp [BackfillPaper8.Challenge.Ab, Lamb_zero]

theorem sPlus_Ab1 : Ab a (sPlus a) 1 = if 2 ≤ kb (branchMS a) 1 then 2 else 0 := by
  rw [BackfillPaper8.Challenge.Ab, sc_mkSw, Lamb_mkSw_one_const a 1 _ (fun i => (lamStd a i : ℝ)),
    sum_lamStd_I1]
  split_ifs <;> ring

theorem sPlus_condL (ha : ∀ i, a i ≤ 1) : condL a (sPlus a) := by
  intro b hb h1b h2b θ hθ
  have hb' := Bset_sub a ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
  obtain rfl : b = 1 := by omega
  obtain ⟨i, hi, i', hi', hli, hli'⟩ := exists_lamStd_I1 a h2b
  refine ⟨i', hi', i, hi, ?_⟩
  have e1 : sig a (sPlus a) i' + lam a (sPlus a) i' / θ = 1 + (-1) / θ := by
    rw [sig_mkSw, lam_mkSw_const a 1 _ (fun i => (lamStd a i : ℝ)), (mem_Ib a).1 hi', hli']
    simp
  have e2 : sig a (sPlus a) i + lam a (sPlus a) i / θ = 1 + 1 / θ := by
    rw [sig_mkSw, lam_mkSw_const a 1 _ (fun i => (lamStd a i : ℝ)), (mem_Ib a).1 hi, hli]
    simp
  rw [e1, e2]
  exact one_add_div_ne (by rw [hθ]; norm_num)

/-- Proposition 5.1(d): for `k₀ = 1` the switching `s⁺` is good. -/
theorem caseD (h32 : Lemma_3_2) (hk : 0 < k) (ha : ∀ i, a i ≤ 1) (hn : 3 ≤ 1 + k + ∑ i, a i)
    (hk0 : kb (branchMS a) 0 = 1) : IsGood (adjT a) (sPlus a) := by
  have hsum := sum_a_eq a ha
  have hcard := card_I0_add_card_I1 a ha
  rw [← kb_eq, ← kb_eq] at hcard
  rw [← kb_eq] at hsum
  have hk1 : 1 ≤ kb (branchMS a) 1 := by omega
  have hne0 : (Ib a 0).Nonempty := by
    rw [← Finset.card_pos, ← kb_eq]
    omega
  have hne1 : (Ib a 1).Nonempty := by
    rw [← Finset.card_pos, ← kb_eq]
    omega
  refine (h32 k a hk _ (sPlus_isSwitching a ha)).2 ⟨?_, sPlus_condL a ha, ?_⟩
  · intro θ hθ
    unfold IsSecular at hθ
    rw [aeval_secular_01 a ha hne0 hne1, hk0] at hθ
    push_cast at hθ
    rw [Gs_eq a ha, sPlus_Ab0, sPlus_Sb, sPlus_Ab1, sPlus_Sb, hk0]
    push_cast
    by_cases h2 : 2 ≤ kb (branchMS a) 1
    · simp only [h2, ite_true, one_mul]
      exact caseD2_alg _ h2 θ (by linear_combination hθ)
    · have h1 : kb (branchMS a) 1 = 1 := by omega
      simp only [h2, ite_false, one_mul]
      simp only [h1, Nat.cast_one, zero_add, one_mul]
      rw [h1] at hθ
      exact caseD1_alg θ (by push_cast at hθ; linear_combination hθ)
  · intro hker
    exact absurd hker (ker_trivial a ha hk0)

/-- Proposition 5.1(e): for `k₀ = 0` the switching `s⁺` is good. -/
theorem caseE (h32 : Lemma_3_2) (hk : 0 < k) (ha : ∀ i, a i ≤ 1)
    (hk0 : kb (branchMS a) 0 = 0) : IsGood (adjT a) (sPlus a) := by
  have hI0 : Ib a 0 = ∅ := by
    rw [← Finset.card_eq_zero, ← kb_eq]
    exact hk0
  have hall : ∀ i, a i = 1 := by
    intro i
    have h1 := ha i
    have h2 : i ∉ Ib a 0 := by
      rw [hI0]
      exact Finset.notMem_empty i
    rw [mem_Ib] at h2
    omega
  have hI1 : Ib a 1 = Finset.univ := by
    ext i
    simp [mem_Ib, hall i]
  have hk1 : kb (branchMS a) 1 = k := by
    rw [kb_eq, hI1, Finset.card_univ, Fintype.card_fin]
  refine (h32 k a hk _ (sPlus_isSwitching a ha)).2 ⟨?_, sPlus_condL a ha, ?_⟩
  · intro θ hθ
    unfold IsSecular at hθ
    rw [aeval_secular_single a hk hall] at hθ
    push_cast at hθ
    rw [Gs_eq a ha, sPlus_Ab0, sPlus_Sb, sPlus_Ab1, sPlus_Sb, hk0]
    push_cast
    simp only [zero_mul, add_zero, zero_div, zero_add]
    by_cases h2 : 2 ≤ kb (branchMS a) 1
    · simp only [h2, ite_true]
      exact caseE2_alg _ h2 θ (by linear_combination hθ)
    · have h1 : kb (branchMS a) 1 = 1 := by omega
      simp only [h2, ite_false]
      simp only [h1, Nat.cast_one, zero_add, one_mul]
      rw [h1] at hθ
      push_cast at hθ
      have ht : θ ^ 2 - 1 = 1 := by linarith
      rw [ht, div_one]
      rintro rfl
      norm_num at ht
  · intro _
    refine ⟨fun h => absurd h (by omega), fun _ => Or.inr ?_⟩
    have hs : ∑ i, lam a (sPlus a) i / (a i : ℝ) = ∑ i ∈ Ib a 1, (lamStd a i : ℝ) := by
      rw [hI1]
      apply Finset.sum_congr rfl
      intro i _
      rw [lam_mkSw_const a 1 _ (fun i => (lamStd a i : ℝ)), hall i]
      simp
    rw [sc_mkSw, hs, sum_lamStd_I1]
    split_ifs with h2
    · have h2' : (2 : ℝ) ≤ kb (branchMS a) 1 := by exact_mod_cast h2
      intro h
      linarith
    · intro h
      have h0 : (0 : ℝ) ≤ kb (branchMS a) 1 := Nat.cast_nonneg _
      linarith

end P8Small
