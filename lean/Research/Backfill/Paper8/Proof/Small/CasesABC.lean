import Research.Backfill.Paper8.Proof.Small.Setup
import Research.Backfill.Paper8.Proof.Small.Alg

/-!
# Paper 8, Proposition 5.1 (a), (b), (c)

Assuming `Lemma_3_2` (a switching is good iff (S), (L), (Z)), the switchings of Proposition 5.1
(a) (stars), (b) (`k₁ = 1`, `k₀ ≥ 2`) and (c) (`k₁ ≥ 2`, `k₀ ≥ 2`) are good, for every choice of
the leaves that get the sign `-1`. (S) is the algebra of `Research.Backfill.Paper8.Proof.Small.Alg`; (L) is void in (a), (b)
and holds in (c) because the leaf sums on `I₁` are not all equal; (Z) holds because the signs on
the bare branches are not all equal.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Small

variable {k : ℕ} (a : Fin k → ℕ)

theorem one_add_div_ne {θ : ℝ} (hθ : θ ^ 2 = 1) : 1 + (-1) / θ ≠ 1 + 1 / θ := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    norm_num at hθ
  intro h
  have h1 : (1 : ℝ) / θ = 0 := by
    have e : (-1 : ℝ) / θ = -(1 / θ) := by ring
    linarith
  rw [div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · norm_num at h1
  · exact hθ0 h1

/-- Proposition 5.1(a): the star, with `-1` on the leaves `v_i`, `i ∈ U`. -/
theorem caseA (h32 : Lemma_3_2) (hk : 0 < k) (ha : ∀ i, a i ≤ 1) (hn : 3 ≤ 1 + k + ∑ i, a i)
    (hk1 : kb (branchMS a) 1 = 0) (U : Finset (Fin k))
    (hU : U.card = if kb (branchMS a) 0 = 4 then 2 else 1) :
    IsGood (adjT a) (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) := by
  have hI1 : Ib a 1 = ∅ := by
    rw [← Finset.card_eq_zero, ← kb_eq]
    exact hk1
  have hall : ∀ i, a i = 0 := by
    intro i
    have h1 := ha i
    have h2 : i ∉ Ib a 1 := by
      rw [hI1]
      exact Finset.notMem_empty i
    rw [mem_Ib] at h2
    omega
  have hI0 : Ib a 0 = Finset.univ := by
    ext i
    simp [mem_Ib, hall i]
  have hk0 : kb (branchMS a) 0 = k := by
    rw [kb_eq, hI0, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, a i = 0 := by simp [hall]
  have hk2 : 2 ≤ k := by omega
  rw [hk0] at hU
  have hsw : IsSwitching (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) := by
    apply isSwitching_mkSw
    · left
      rfl
    · intro i
      split_ifs <;> simp
    · intro _ _
      left
      rfl
  refine (h32 k a hk _ hsw).2 ⟨?_, ?_, ?_⟩
  · intro θ hθ
    unfold IsSecular at hθ
    rw [aeval_secular_single a hk hall, hk0] at hθ
    have ht : θ ^ 2 = k := by
      push_cast at hθ
      linarith
    rw [Gs_eq a ha]
    have hAb0 : Ab a (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) 0 = k := by
      simp [BackfillPaper8.Challenge.Ab, Lamb_zero, hk0]
    have hSb0 : Sb a (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) 0 =
        k - 2 * U.card := by
      rw [Sb_mkSw, hI0, sum_sign_mem]
    have hAb1 : Ab a (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) 1 = 0 := by
      simp [BackfillPaper8.Challenge.Ab, Lamb, hk1, hI1]
    have hSb1 : Sb a (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1)) 1 = 0 := by
      rw [Sb_mkSw, hI1, Finset.sum_empty]
    rw [hAb0, hSb0, hAb1, hSb1]
    simp only [zero_mul, add_zero, zero_div]
    exact caseA_alg k U.card hk2 hU θ ht
  · intro b hb h1b
    obtain ⟨i, rfl⟩ := (mem_Bset a).1 hb
    rw [hall i] at h1b
    omega
  · intro _
    refine ⟨fun _ => Or.inr ?_, fun h => absurd h (by omega)⟩
    have hU1 : 0 < U.card := by
      rw [hU]
      split_ifs <;> norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hU1
    have hU2 : U.card < k := by
      rw [hU]
      split_ifs <;> omega
    obtain ⟨i', hi'⟩ : ∃ i', i' ∉ U := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      have hUu : U = Finset.univ := Finset.eq_univ_of_forall hc
      rw [hUu, Finset.card_univ, Fintype.card_fin] at hU2
      omega
    refine ⟨i, by rw [hI0]; exact Finset.mem_univ i, i', by rw [hI0]; exact Finset.mem_univ i', ?_⟩
    norm_num [hi, hi']

/-- Proposition 5.1(b): `k₁ = 1`, `k₀ ≥ 2`, `-1` on the bare branch `i₀` and on the leaf. -/
theorem caseB (h32 : Lemma_3_2) (hk : 0 < k) (ha : ∀ i, a i ≤ 1)
    (hk1 : kb (branchMS a) 1 = 1) (hk0 : 2 ≤ kb (branchMS a) 0) (i0 : Fin k) (hi0 : a i0 = 0) :
    IsGood (adjT a) (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) := by
  have hi0' : i0 ∈ Ib a 0 := (mem_Ib a).2 hi0
  have hi0'' : i0 ∉ Ib a 1 := by
    rw [mem_Ib, hi0]
    norm_num
  have hne0 : (Ib a 0).Nonempty := ⟨i0, hi0'⟩
  have hne1 : (Ib a 1).Nonempty := by
    rw [← Finset.card_pos, ← kb_eq]
    omega
  have hsw : IsSwitching (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) := by
    apply isSwitching_mkSw
    · left
      rfl
    · intro i
      split_ifs <;> simp
    · intro _ _
      right
      rfl
  refine (h32 k a hk _ hsw).2 ⟨?_, ?_, ?_⟩
  · intro θ hθ
    unfold IsSecular at hθ
    rw [aeval_secular_01 a ha hne0 hne1, hk1] at hθ
    rw [Gs_eq a ha]
    have hAb0 : Ab a (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) 0 =
        kb (branchMS a) 0 := by
      simp [BackfillPaper8.Challenge.Ab, Lamb_zero]
    have hSb0 : Sb a (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) 0 =
        (kb (branchMS a) 0 : ℝ) - 2 := by
      rw [Sb_mkSw, sum_sign_eq, kb_eq]
      simp [hi0']
    have hAb1 : Ab a (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) 1 = 0 := by
      rw [BackfillPaper8.Challenge.Ab, sc_mkSw, Lamb_mkSw_one_const a 1 _ (fun _ => (-1 : ℝ)),
        Finset.sum_const, ← kb_eq, hk1]
      norm_num
    have hSb1 : Sb a (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1)) 1 = 1 := by
      rw [Sb_mkSw, sum_sign_eq, ← kb_eq, hk1]
      simp [hi0'']
    rw [hAb0, hSb0, hAb1, hSb1]
    simp only [zero_add, one_mul]
    exact caseB_alg _ hk0 θ (by push_cast at hθ; linear_combination hθ)
  · intro b hb h1b h2b
    have hb' := Bset_sub a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl
    · omega
    · omega
  · intro _
    refine ⟨fun _ => Or.inr ?_, fun h => absurd h (by omega)⟩
    have h1 : 1 < (Ib a 0).card := by
      rw [← kb_eq]
      omega
    obtain ⟨i', hi', hne'⟩ := Finset.exists_mem_ne h1 i0
    refine ⟨i0, hi0', i', hi', ?_⟩
    norm_num [hne']

/-- Proposition 5.1(c): `k₁ ≥ 2`, `k₀ ≥ 2`, `-1` on the bare branch `i₀` and on the leaf of `i₁`. -/
theorem caseC (h32 : Lemma_3_2) (hk : 0 < k) (ha : ∀ i, a i ≤ 1)
    (hk1 : 2 ≤ kb (branchMS a) 1) (hk0 : 2 ≤ kb (branchMS a) 0) (i0 i1 : Fin k)
    (hi0 : a i0 = 0) (hi1 : a i1 = 1) :
    IsGood (adjT a)
      (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun i _ => if i = i1 then -1 else 1)) := by
  have hi0' : i0 ∈ Ib a 0 := (mem_Ib a).2 hi0
  have hi0'' : i0 ∉ Ib a 1 := by
    rw [mem_Ib, hi0]
    norm_num
  have hi1' : i1 ∈ Ib a 1 := (mem_Ib a).2 hi1
  have hne0 : (Ib a 0).Nonempty := ⟨i0, hi0'⟩
  have hne1 : (Ib a 1).Nonempty := ⟨i1, hi1'⟩
  have hsw : IsSwitching
      (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun i _ => if i = i1 then -1 else 1)) := by
    apply isSwitching_mkSw
    · left
      rfl
    · intro i
      split_ifs <;> simp
    · intro i _
      split_ifs <;> simp
  refine (h32 k a hk _ hsw).2 ⟨?_, ?_, ?_⟩
  · intro θ hθ
    unfold IsSecular at hθ
    rw [aeval_secular_01 a ha hne0 hne1] at hθ
    rw [Gs_eq a ha]
    have hAb0 : Ab a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) 0 = kb (branchMS a) 0 := by
      simp [BackfillPaper8.Challenge.Ab, Lamb_zero]
    have hSb0 : Sb a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) 0 = (kb (branchMS a) 0 : ℝ) - 2 := by
      rw [Sb_mkSw, sum_sign_eq, kb_eq]
      simp [hi0']
    have hAb1 : Ab a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) 1 = 2 * (kb (branchMS a) 1 : ℝ) - 2 := by
      rw [BackfillPaper8.Challenge.Ab, sc_mkSw,
        Lamb_mkSw_one_const a 1 _ (fun i => if i = i1 then (-1 : ℝ) else 1), sum_sign_eq, kb_eq]
      simp only [hi1', ite_true]
      ring
    have hSb1 : Sb a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) 1 = kb (branchMS a) 1 := by
      rw [Sb_mkSw, sum_sign_eq, ← kb_eq]
      simp [hi0'']
    rw [hAb0, hSb0, hAb1, hSb1]
    exact caseC_alg _ _ hk0 hk1 θ hθ
  · intro b hb h1b h2b θ hθ
    have hb' := Bset_sub a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    obtain rfl : b = 1 := by omega
    have h1 : 1 < (Ib a 1).card := by
      rw [← kb_eq]
      omega
    obtain ⟨i', hi', hne'⟩ := Finset.exists_mem_ne h1 i1
    have hai' : a i' = 1 := (mem_Ib a).1 hi'
    have hne10 : i1 ≠ i0 := by
      rintro rfl
      rw [hi0] at hi1
      exact absurd hi1 (by norm_num)
    have hne'0 : i' ≠ i0 := by
      rintro rfl
      rw [hi0] at hai'
      exact absurd hai' (by norm_num)
    refine ⟨i1, hi1', i', hi', ?_⟩
    have e1 : sig a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) i1 +
        lam a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) i1 / θ = 1 + (-1) / θ := by
      rw [sig_mkSw, lam_mkSw_const a 1 _ (fun i => if i = i1 then (-1 : ℝ) else 1)]
      simp [hne10, hi1]
    have e2 : sig a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) i' +
        lam a (mkSw a 1 (fun i => if i = i0 then -1 else 1)
        (fun i _ => if i = i1 then -1 else 1)) i' / θ = 1 + 1 / θ := by
      rw [sig_mkSw, lam_mkSw_const a 1 _ (fun i => if i = i1 then (-1 : ℝ) else 1)]
      simp [hne'0, hne', hai']
    rw [e1, e2]
    exact one_add_div_ne (by rw [hθ]; norm_num)
  · intro _
    refine ⟨fun _ => Or.inr ?_, fun h => absurd h (by omega)⟩
    have h1 : 1 < (Ib a 0).card := by
      rw [← kb_eq]
      omega
    obtain ⟨i', hi', hne'⟩ := Finset.exists_mem_ne h1 i0
    refine ⟨i0, hi0', i', hi', ?_⟩
    norm_num [hne']

end P8Small
