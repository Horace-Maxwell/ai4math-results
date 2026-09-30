import Research.Backfill.Paper8.Proof.Main.Eigen

/-!
# Paper 8, agent `main`: Lemma 3.2 (good switchings of `T(a)`)

A switching `s` of `T(a)` is good iff (S), (L) and (Z) hold. The proof uses equation (3.1) only
(no part of Lemma 3.1 is assumed): an eigenvector `y` of `θ ≠ 0` with `y_c ≠ 0` makes `θ`
secular and `y ⬝ s = y_c G_s(θ)`; one with `y_c = 0` lives on a single `I_b` with `θ² = b`,
`k_b ≥ 2`, and `y ⬝ s = ∑ y_{v_i}(σ_i + λ_i/θ)`; the kernel is tested with the vectors
`e_ℓ - e_ℓ'`, `e_{v_i} - e_{v_i'}` and `x_c = 1`, `x_ℓ = -1/a_i`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix P8Basic

namespace P8Main

variable {k : ℕ} (a : Fin k → ℕ) (s : TV a → ℝ)

/-- Good ⟹ (S). -/
theorem condS_of_good
    (hG : ∀ θ : ℝ, IsEigenvalue (adjT a) θ → ∃ x : TV a → ℝ, adjT a *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0) :
    condS a s := by
  intro θ hθ hGs
  have hθ0 := ne_zero_of_isSecular a hθ
  obtain ⟨hne, hF⟩ := (isSecular_iff a θ).1 hθ
  have hev : IsEigenvalue (adjT a) θ :=
    (isEigenvalue_iff _ _).2 ⟨secVec a θ, secVec_ne_zero a θ, secVec_eigen a hne hF⟩
  obtain ⟨y, hy, hys⟩ := hG θ hev
  apply hys
  rw [dot_secular a hy hθ0 hne hF, hGs, mul_zero]

/-- Good ⟹ (L). -/
theorem condL_of_good
    (hG : ∀ θ : ℝ, IsEigenvalue (adjT a) θ → ∃ x : TV a → ℝ, adjT a *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0) :
    condL a s := by
  intro b _ hb1 hb2 θ hθ
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    rw [zero_pow two_ne_zero] at hθ
    linarith
  rw [kb_branchMS] at hb2
  obtain ⟨i1, hi1, i2, hi2, h12⟩ := Finset.one_lt_card.1 hb2
  have ha1 : (a i1 : ℝ) = θ ^ 2 := by rw [(mem_Ib_iff a b i1).1 hi1, hθ]
  have ha2 : (a i2 : ℝ) = θ ^ 2 := by rw [(mem_Ib_iff a b i2).1 hi2, hθ]
  have hev : IsEigenvalue (adjT a) θ :=
    (isEigenvalue_iff _ _).2 ⟨_, pair_ne_zero a h12 θ, pair_eigen a hθ0 ha1 ha2⟩
  obtain ⟨y, hy, hys⟩ := hG θ hev
  by_contra hcon
  push Not at hcon
  apply hys
  have hyc : y none = 0 := by
    have := eig_v' hy i1
    rw [ha1, sub_self, zero_mul] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hθ0
  have hyv : ∀ m, a m ≠ b → y (some ⟨m, none⟩) = 0 := by
    intro m hm
    have := eig_v' hy m
    rw [hyc, mul_zero] at this
    have hd : θ ^ 2 - (a m : ℝ) ≠ 0 := by
      rw [hθ, sub_ne_zero]
      exact_mod_cast (Ne.symm hm)
    exact (mul_eq_zero.1 this).resolve_left hd
  rw [dot_of_leaf a y s θ (eig_l' hy hθ0), hyc, zero_mul, zero_add]
  have hterm : ∀ m, y (some ⟨m, none⟩) * (sig a s m + lam a s m / θ) =
      y (some ⟨m, none⟩) * (sig a s i1 + lam a s i1 / θ) := by
    intro m
    by_cases hm : a m = b
    · rw [hcon m ((mem_Ib_iff a b m).2 hm) i1 hi1]
    · rw [hyv m hm, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.sum_mul, ← eig_c hy, hyc, mul_zero,
    zero_mul]

/-- Good ⟹ (Z). -/
theorem condZ_of_good
    (hG : ∀ θ : ℝ, IsEigenvalue (adjT a) θ → ∃ x : TV a → ℝ, adjT a *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0) :
    condZ a s := by
  intro hker
  have hev : IsEigenvalue (adjT a) 0 := by
    obtain ⟨x, hx, hAx⟩ := hker
    exact (isEigenvalue_iff _ _).2 ⟨x, hx, by rw [hAx, zero_smul]⟩
  obtain ⟨y, hy, hys⟩ := hG 0 hev
  have hv0 : ∀ i, 1 ≤ a i → y (some ⟨i, none⟩) = 0 := by
    intro i hi
    have := eig_l hy i ⟨0, hi⟩
    rw [zero_mul] at this
    exact this.symm
  have hl0 : ∀ i, y none + ∑ j, y (some ⟨i, some j⟩) = 0 := by
    intro i
    have := eig_v hy i
    rw [zero_mul] at this
    exact this.symm
  have hc0 : ∑ i, y (some ⟨i, none⟩) = 0 := by
    have := eig_c hy
    rw [zero_mul] at this
    exact this.symm
  constructor
  · intro hk0
    by_contra hcon
    push Not at hcon
    obtain ⟨hleaf, hbare⟩ := hcon
    rw [kb_branchMS] at hk0
    obtain ⟨i0, hi0⟩ := Finset.card_pos.1 hk0
    have hi0' : a i0 = 0 := (mem_Ib_iff a 0 i0).1 hi0
    have hyc : y none = 0 := by
      have := hl0 i0
      rwa [Finset.sum_eq_zero (fun j _ => absurd j.isLt (by omega)), add_zero] at this
    have hconst : ∀ i (j j' : Fin (a i)), s (some ⟨i, some j⟩) = s (some ⟨i, some j'⟩) := by
      intro i j j'
      by_cases h2 : 2 ≤ a i
      · exact hleaf i h2 j j'
      · have : j = j' := Fin.ext (by have := j.isLt; have := j'.isLt; omega)
        rw [this]
    apply hys
    rw [dot_TV, hyc, zero_mul, zero_add]
    have hterm : ∀ i, y (some ⟨i, none⟩) * s (some ⟨i, none⟩) +
        ∑ j, y (some ⟨i, some j⟩) * s (some ⟨i, some j⟩) =
          y (some ⟨i, none⟩) * s (some ⟨i0, none⟩) := by
      intro i
      by_cases hai : a i = 0
      · rw [Finset.sum_eq_zero (fun j _ => absurd j.isLt (by omega)), add_zero]
        have := hbare i ((mem_Ib_iff a 0 i).2 hai) i0 hi0
        simp only [sig] at this
        rw [this]
      · have h1 : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 hai
        have hsum : ∑ j, y (some ⟨i, some j⟩) * s (some ⟨i, some j⟩) =
            (∑ j, y (some ⟨i, some j⟩)) * s (some ⟨i, some ⟨0, h1⟩⟩) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by rw [hconst i j ⟨0, h1⟩])
        have := hl0 i
        rw [hyc, zero_add] at this
        rw [hsum, this, zero_mul, add_zero, hv0 i h1, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul, hc0, zero_mul]
  · intro hk0
    have hall := (kb_zero_eq_zero_iff a).1 hk0
    by_contra hcon
    push Not at hcon
    obtain ⟨hleaf, hsc⟩ := hcon
    apply hys
    rw [dot_TV]
    have hterm : ∀ i, y (some ⟨i, none⟩) * s (some ⟨i, none⟩) +
        ∑ j, y (some ⟨i, some j⟩) * s (some ⟨i, some j⟩) =
          -(y none * (lam a s i / (a i : ℝ))) := by
      intro i
      have h1 : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 (hall i)
      have hsum : ∑ j, y (some ⟨i, some j⟩) * s (some ⟨i, some j⟩) =
          (∑ j, y (some ⟨i, some j⟩)) * s (some ⟨i, some ⟨0, h1⟩⟩) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [hleaf i j ⟨0, h1⟩])
      have hlam : lam a s i = (a i : ℝ) * s (some ⟨i, some ⟨0, h1⟩⟩) := by
        simp only [lam]
        rw [Finset.sum_congr rfl (fun j _ => hleaf i j ⟨0, h1⟩), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hai : (a i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hall i)
      have hl := hl0 i
      rw [hsum, hv0 i h1, zero_mul, zero_add, hlam,
        show (∑ j, y (some ⟨i, some j⟩)) = -y none by linarith]
      field_simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib, ← Finset.mul_sum, ← hsc]
    simp only [sc]
    ring

/-- (Z) ⟹ `s` is not orthogonal to the kernel (when `0` is an eigenvalue). -/
theorem good_zero (hZ : condZ a s) (hker : ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0) :
    ∃ x : TV a → ℝ, adjT a *ᵥ x = (0 : ℝ) • x ∧ x ⬝ᵥ s ≠ 0 := by
  obtain ⟨hZ1, hZ2⟩ := hZ hker
  by_cases hk0 : 1 ≤ kb (branchMS a) 0
  · rcases hZ1 hk0 with ⟨i, _, j, j', hne⟩ | ⟨i, hi, i', hi', hne⟩
    · refine ⟨_, by rw [zero_smul]; exact leafDiff_ker a i j j', ?_⟩
      rw [single_sub_dot]
      exact sub_ne_zero.2 hne
    · have hk := bareDiff_ker a i i' ((mem_Ib_iff a 0 i).1 hi) ((mem_Ib_iff a 0 i').1 hi')
      refine ⟨_, by rw [zero_smul]; exact hk, ?_⟩
      rw [single_sub_dot]
      exact sub_ne_zero.2 hne
  · have hk : kb (branchMS a) 0 = 0 := by omega
    rcases hZ2 hk with ⟨i, j, j', hne⟩ | hne
    · refine ⟨_, by rw [zero_smul]; exact leafDiff_ker a i j j', ?_⟩
      rw [single_sub_dot]
      exact sub_ne_zero.2 hne
    · refine ⟨zvec a, zvec_ker a ((kb_zero_eq_zero_iff a).1 hk), ?_⟩
      rw [zvec_dot]
      exact sub_ne_zero.2 hne

/-- (L) ⟹ `s` is not orthogonal to `E_θ` for an eigenvector with `y_c = 0`, `θ ≠ 0`. -/
theorem good_L (hL : condL a s) {θ : ℝ} {y : TV a → ℝ} (hθ0 : θ ≠ 0) (hy0 : y ≠ 0)
    (hy : adjT a *ᵥ y = θ • y) (hc : y none = 0) :
    ∃ x : TV a → ℝ, adjT a *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0 := by
  have hex : ∃ i, y (some ⟨i, none⟩) ≠ 0 := by
    by_contra h
    push Not at h
    apply hy0
    funext u
    rcases u with _ | ⟨i, _ | j⟩
    · exact hc
    · exact h i
    · rw [eig_l' hy hθ0 i j, h i, zero_div]
      rfl
  obtain ⟨i, hi⟩ := hex
  have hai : (a i : ℝ) = θ ^ 2 := by
    have := eig_v' hy i
    rw [hc, mul_zero] at this
    have := (mul_eq_zero.1 this).resolve_right hi
    linarith
  have hv : ∀ m, a m ≠ a i → y (some ⟨m, none⟩) = 0 := by
    intro m hm
    have := eig_v' hy m
    rw [hc, mul_zero] at this
    refine (mul_eq_zero.1 this).resolve_left ?_
    rw [← hai, sub_eq_zero]
    exact_mod_cast (Ne.symm hm)
  have hb : a i ∈ Bset (branchMS a) := (mem_Bset_iff a _).2 ⟨i, rfl⟩
  have hb1 : 1 ≤ a i := by
    refine Nat.one_le_iff_ne_zero.2 (fun h => pow_ne_zero 2 hθ0 ?_)
    rw [← hai, h, Nat.cast_zero]
  have hii : i ∈ Ib a (a i) := (mem_Ib_iff a _ i).2 rfl
  have hb2 : 2 ≤ kb (branchMS a) (a i) := by
    rw [kb_branchMS]
    apply Finset.one_lt_card.2
    by_contra h
    push Not at h
    apply hi
    have hsum : ∑ m ∈ Ib a (a i), y (some ⟨m, none⟩) = 0 := by
      unfold Ib
      rw [Finset.sum_filter_of_ne (fun m _ hm => of_not_not (fun h' => hm (hv m h'))), ← eig_c hy,
        hc, mul_zero]
    rwa [Finset.sum_eq_single_of_mem i hii (fun m hm hmi => absurd (h m hm i hii) hmi)] at hsum
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := hL (a i) hb hb1 hb2 θ hai.symm
  refine ⟨lvec a (Pi.single i1 1 - Pi.single i2 1) θ, pair_eigen a hθ0 ?_ ?_, ?_⟩
  · rw [(mem_Ib_iff a _ i1).1 hi1, hai]
  · rw [(mem_Ib_iff a _ i2).1 hi2, hai]
  · rw [pair_dot]
    exact sub_ne_zero.2 hne

/-- (S), (L), (Z) ⟹ good. -/
theorem good_of_conds (hS : condS a s) (hL : condL a s) (hZ : condZ a s) :
    ∀ θ : ℝ, IsEigenvalue (adjT a) θ → ∃ x : TV a → ℝ, adjT a *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0 := by
  intro θ hθ
  obtain ⟨y, hy0, hy⟩ := (isEigenvalue_iff _ _).1 hθ
  by_cases hθ0 : θ = 0
  · subst hθ0
    exact good_zero a s hZ ⟨y, hy0, by rw [hy, zero_smul]⟩
  by_cases hc : y none = 0
  · exact good_L a s hL hθ0 hy0 hy hc
  have hne : ∀ i, θ ^ 2 ≠ (a i : ℝ) := by
    intro i hi
    have := eig_v' hy i
    rw [hi, sub_self, zero_mul] at this
    exact mul_ne_zero hθ0 hc this.symm
  have hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1 := by
    have h := eig_c hy
    have hv : ∀ i, y (some ⟨i, none⟩) = θ * y none * (1 / (θ ^ 2 - (a i : ℝ))) := by
      intro i
      rw [← eig_v' hy i]
      field_simp [sub_ne_zero.2 (hne i)]
    rw [Finset.sum_congr rfl (fun i _ => hv i), ← Finset.mul_sum] at h
    exact mul_left_cancel₀ (mul_ne_zero hθ0 hc) (by rw [mul_one]; exact h.symm)
  have hsec : IsSecular (branchMS a) θ := (isSecular_iff a θ).2 ⟨hne, hF⟩
  refine ⟨y, hy, ?_⟩
  rw [dot_secular a hy hθ0 hne hF]
  exact mul_ne_zero hc (hS θ hsec)

/-- **Lemma 3.2.** -/
theorem lemma_3_2 : IsGood (adjT a) s ↔ condS a s ∧ condL a s ∧ condZ a s := by
  rw [isGood_iff]
  exact ⟨fun hG => ⟨condS_of_good a s hG, condL_of_good a s hG, condZ_of_good a s hG⟩,
    fun ⟨hS, hL, hZ⟩ => good_of_conds a s hS hL hZ⟩

end P8Main
