import Research.Backfill.Paper8.Proof.Spec.Roots
import Research.Backfill.Paper8.Proof.Spec.Eigen
import Research.Backfill.Paper8.Proof.Spec.Kernel

/-!
# Paper 8, Lemma 3.1(iv): the eigenvalues of `A(T(a))` and their number

An eigenvector with `θ ≠ 0` and `x_c ≠ 0` forces `R(θ²) = 0`; with `x_c = 0` it forces
`θ² = b ∈ B`, `b ≥ 1`, `k_b ≥ 2` (`isEigenvalue_iff_char`). The eigenvalues are therefore the `θ`
with `θ² ∈ T₁ ∪ T₂` (`T₁` the roots of `R`, `T₂` the admissible `b`), all positive, plus possibly
`0`; each positive `t` gives the two values `±√t` (`ncard_sq_mem`), whence the count
(`ncard_eigenvalues`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial Matrix

namespace P8Spec

/-- `{θ | θ² ∈ T}` for a finite set `T` of positive reals is `√T ∪ -√T`. -/
theorem sq_mem_eq (T : Finset ℝ) (hT : ∀ t ∈ T, 0 < t) :
    {θ : ℝ | θ ^ 2 ∈ T} = ↑(T.image Real.sqrt ∪ T.image (fun t => -Real.sqrt t)) := by
  ext θ
  simp only [Set.mem_ofPred_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe]
  constructor
  · intro h
    rcases le_or_gt 0 θ with hθ | hθ
    · exact Or.inl ⟨θ ^ 2, h, Real.sqrt_sq hθ⟩
    · refine Or.inr ⟨θ ^ 2, h, ?_⟩
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hθ, neg_neg]
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [Real.sq_sqrt (hT t ht).le]
      exact ht
    · rw [neg_sq, Real.sq_sqrt (hT t ht).le]
      exact ht

/-- `|{θ | θ² ∈ T}| = 2|T|` for a finite set `T` of positive reals. -/
theorem ncard_sq_mem (T : Finset ℝ) (hT : ∀ t ∈ T, 0 < t) :
    {θ : ℝ | θ ^ 2 ∈ T}.ncard = 2 * T.card := by
  have hinj1 : Set.InjOn Real.sqrt ↑T := fun s hs t ht hst =>
    (Real.sqrt_inj (hT s hs).le (hT t ht).le).1 hst
  have hinj2 : Set.InjOn (fun t => -Real.sqrt t) ↑T := fun s hs t ht hst =>
    (Real.sqrt_inj (hT s hs).le (hT t ht).le).1 (neg_inj.1 hst)
  have hdisj : Disjoint (T.image Real.sqrt) (T.image (fun t => -Real.sqrt t)) := by
    rw [Finset.disjoint_left]
    intro θ h1 h2
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t, ht, h⟩ := Finset.mem_image.1 h2
    have h3 := Real.sqrt_pos.2 (hT s hs)
    have h4 := Real.sqrt_pos.2 (hT t ht)
    have h5 : -Real.sqrt t = Real.sqrt s := h
    linarith
  rw [sq_mem_eq T hT, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2]
  ring

variable {k : ℕ} (a : Fin k → ℕ)

/-- Lemma 3.1(iv), first part: the eigenvalues of `A`. -/
theorem isEigenvalue_iff_char (θ : ℝ) :
    IsEigenvalue (adjT a) θ ↔
      (IsSecular (branchMS a) θ ∨
        (∃ b ∈ Bset (branchMS a), 1 ≤ b ∧ 2 ≤ kb (branchMS a) b ∧ θ ^ 2 = (b : ℝ)) ∨
        (θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0)) := by
  constructor
  · intro h
    obtain ⟨x, hx0, hx⟩ := (P8Basic.isEigenvalue_iff _ _).1 h
    by_cases hθ : θ = 0
    · refine Or.inr (Or.inr ⟨hθ, x, hx0, ?_⟩)
      rw [hx, hθ, zero_smul]
    have hv := mid_eq a θ hθ x hx
    have hl := leaf_eq_div a θ hθ x hx
    obtain ⟨h1, _, _⟩ := (P8Basic.mulVec_eq_smul_iff a x θ).1 hx
    by_cases hc : x none = 0
    · -- `x_c = 0`: the eigenvalues `±√b`
      refine Or.inr (Or.inl ?_)
      obtain ⟨i0, hi0⟩ : ∃ i, x (some ⟨i, none⟩) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hx0
        funext v
        rcases v with _ | ⟨i, _ | j⟩
        · exact hc
        · exact hall i
        · change x (some ⟨i, some j⟩) = 0
          rw [hl i j, hall i, zero_div]
      have hb : θ ^ 2 = (a i0 : ℝ) := by
        have e := hv i0
        rw [hc, mul_zero] at e
        have e2 := (mul_eq_zero.1 e).resolve_right hi0
        linarith
      have hvz : ∀ i, a i ≠ a i0 → x (some ⟨i, none⟩) = 0 := by
        intro i hi
        have e := hv i
        rw [hc, mul_zero] at e
        have hD : θ ^ 2 - (a i : ℝ) ≠ 0 := by
          rw [hb, sub_ne_zero]
          exact_mod_cast (Ne.symm hi)
        exact (mul_eq_zero.1 e).resolve_left hD
      refine ⟨a i0, (mem_Bset_branchMS a _).2 ⟨i0, rfl⟩, ?_, ?_, hb⟩
      · by_contra h0
        have h00 : a i0 = 0 := by omega
        rw [h00, Nat.cast_zero] at hb
        exact hθ (pow_eq_zero_iff two_ne_zero |>.1 hb)
      · rw [kb_branchMS]
        by_contra hlt
        have hmem : i0 ∈ Ib a (a i0) := by simp [Ib]
        have hcard : (Ib a (a i0)).card = 1 := by
          have := Finset.card_pos.2 ⟨i0, hmem⟩
          omega
        obtain ⟨i1, hi1⟩ := Finset.card_eq_one.1 hcard
        have hsum : ∑ i ∈ Ib a (a i0), x (some ⟨i, none⟩) = ∑ i, x (some ⟨i, none⟩) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          apply hvz i
          simpa [Ib] using hi
        have h01 : i0 = i1 := by
          rw [hi1] at hmem
          exact Finset.mem_singleton.1 hmem
        rw [hi1, Finset.sum_singleton, ← h01, ← h1, hc, mul_zero] at hsum
        exact hi0 hsum
    · -- `x_c ≠ 0`: the secular eigenvalues
      refine Or.inl ?_
      have hne : ∀ i, θ ^ 2 ≠ (a i : ℝ) := by
        intro i hi
        have e := hv i
        rw [hi, sub_self, zero_mul] at e
        exact mul_ne_zero hθ hc e.symm
      have hxv : ∀ i, x (some ⟨i, none⟩) = θ * x none * (1 / (θ ^ 2 - (a i : ℝ))) := by
        intro i
        rw [mul_one_div, eq_div_iff (sub_ne_zero.2 (hne i)), mul_comm]
        exact hv i
      simp only [hxv] at h1
      rw [← Finset.mul_sum] at h1
      have hθc : θ * x none ≠ 0 := mul_ne_zero hθ hc
      exact (aeval_secular_eq_zero_iff a (θ ^ 2) hne).2
        (mul_left_cancel₀ hθc (h1.symm.trans (mul_one _).symm))
  · rintro (hsec | ⟨b, hb, hb1, hkb, hθb⟩ | ⟨hθ, x, hx0, hx⟩)
    · have hne : ∀ i, θ ^ 2 ≠ (a i : ℝ) := by
        intro i hi
        apply aeval_secular_ne_zero_of_mem (branchMS a) (a i)
          ((mem_Bset_branchMS a _).2 ⟨i, rfl⟩)
        rw [← hi]
        exact hsec
      have hF := (aeval_secular_eq_zero_iff a (θ ^ 2) hne).1 hsec
      refine (P8Basic.isEigenvalue_iff _ _).2 ⟨secVec a θ, ?_, secVec_eigen a θ hne hF⟩
      intro h
      have h0 := congrFun h none
      simp [secVec] at h0
    · have hex := (mem_Bset_branchMS a b).1 hb
      have hθ : θ ≠ 0 := by
        rintro rfl
        have h1 : (b : ℝ) = 0 := by
          rw [← hθb]
          ring
        have h2 : b = 0 := by exact_mod_cast h1
        omega
      have hfr := finrank_eigenspace_sqrt a b hex θ hθ hθb
      rw [← kb_branchMS] at hfr
      refine Module.End.hasEigenvalue_iff.2 (fun hbot => ?_)
      rw [hbot, finrank_bot] at hfr
      omega
    · refine (P8Basic.isEigenvalue_iff _ _).2 ⟨x, hx0, ?_⟩
      rw [hx, hθ, zero_smul]

/-- Lemma 3.1(iv), second part: the number of distinct eigenvalues. -/
theorem ncard_eigenvalues (hk : 0 < k) :
    {θ : ℝ | IsEigenvalue (adjT a) θ}.ncard =
      2 * (Bset (branchMS a)).card +
        2 * ((Bset (branchMS a)).filter (fun b => 1 ≤ b ∧ 2 ≤ kb (branchMS a) b)).card +
        {θ : ℝ | θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0}.ncard := by
  have hm0 := branchMS_ne_zero a hk
  obtain ⟨t, hmono, hroots, _, _, hpos, _⟩ := roots_spec (branchMS a) hm0
  have hpR0 : (secular (branchMS a)).map (Int.castRingHom ℝ) ≠ 0 :=
    ((secular_monic (branchMS a) hm0).1.map _).ne_zero
  obtain ⟨T1, hT1⟩ : ∃ T1 : Finset ℝ,
      T1 = ((secular (branchMS a)).map (Int.castRingHom ℝ)).roots.toFinset := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : Finset ℝ,
      T2 = ((Bset (branchMS a)).filter (fun b => 1 ≤ b ∧ 2 ≤ kb (branchMS a) b)).image
        (fun b : ℕ => (b : ℝ)) := ⟨_, rfl⟩
  have hmemT1 : ∀ s : ℝ, s ∈ T1 ↔ aeval s (secular (branchMS a)) = 0 := by
    intro s
    rw [hT1, Multiset.mem_toFinset, mem_roots hpR0, IsRoot.def, eval_map_secular]
  have hsecT1 : ∀ θ : ℝ, IsSecular (branchMS a) θ ↔ θ ^ 2 ∈ T1 := fun θ => (hmemT1 (θ ^ 2)).symm
  have hT1pos : ∀ s ∈ T1, 0 < s := by
    intro s hs
    rw [hT1, hroots, Multiset.mem_toFinset] at hs
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hs
    exact (hpos j).1
  have hT1card : T1.card = (Bset (branchMS a)).card := by
    rw [hT1, hroots,
      Multiset.toFinset_card_of_nodup (Multiset.Nodup.map hmono.injective Finset.univ.nodup),
      Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hmemT2 : ∀ θ : ℝ, (∃ b ∈ Bset (branchMS a), 1 ≤ b ∧ 2 ≤ kb (branchMS a) b ∧
      θ ^ 2 = (b : ℝ)) ↔ θ ^ 2 ∈ T2 := by
    intro θ
    rw [hT2, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, h1, h2, h3⟩
      exact ⟨b, Finset.mem_filter.2 ⟨hb, h1, h2⟩, h3.symm⟩
    · rintro ⟨b, hb, h3⟩
      obtain ⟨hb, h1, h2⟩ := Finset.mem_filter.1 hb
      exact ⟨b, hb, h1, h2, h3.symm⟩
  have hT2pos : ∀ s ∈ T2, 0 < s := by
    intro s hs
    rw [hT2] at hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hs
    have h1 := (Finset.mem_filter.1 hb).2.1
    have h2 : (1 : ℝ) ≤ b := by exact_mod_cast h1
    linarith
  have hT2card : T2.card =
      ((Bset (branchMS a)).filter (fun b => 1 ≤ b ∧ 2 ≤ kb (branchMS a) b)).card := by
    rw [hT2]
    exact Finset.card_image_of_injective _ Nat.cast_injective
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    rw [hT2] at h2
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h2
    exact aeval_secular_ne_zero_of_mem (branchMS a) b (Finset.mem_filter.1 hb).1
      ((hmemT1 _).1 h1)
  have hTpos : ∀ s ∈ T1 ∪ T2, 0 < s := by
    intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · exact hT1pos s h
    · exact hT2pos s h
  have hE : {θ : ℝ | IsEigenvalue (adjT a) θ} = {θ : ℝ | θ ^ 2 ∈ T1 ∪ T2} ∪
      {θ : ℝ | θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0} := by
    ext θ
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Finset.mem_union,
      isEigenvalue_iff_char a θ, hsecT1, hmemT2, or_assoc]
  have hdisj3 : Disjoint {θ : ℝ | θ ^ 2 ∈ T1 ∪ T2}
      {θ : ℝ | θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0} := by
    rw [Set.disjoint_left]
    rintro θ h1 ⟨rfl, _⟩
    have h := hTpos ((0 : ℝ) ^ 2) h1
    norm_num at h
  have hfin1 : {θ : ℝ | θ ^ 2 ∈ T1 ∪ T2}.Finite := by
    rw [sq_mem_eq _ hTpos]
    exact Finset.finite_toSet _
  have hfin2 : {θ : ℝ | θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0}.Finite :=
    (Set.finite_singleton (0 : ℝ)).subset (fun θ h => h.1)
  rw [hE, Set.ncard_union_eq hdisj3 hfin1 hfin2, ncard_sq_mem _ hTpos,
    Finset.card_union_of_disjoint hdisj, hT1card, hT2card]
  ring

end P8Spec
