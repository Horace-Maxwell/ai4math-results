import Research.Backfill.Paper8.Proof.Main.Setup

/-!
# Paper 8, agent `main`: eigenvectors of `T(a)` and dot products with a switching

Consequences of equation (3.1) (`P8Basic.mulVec_eq_smul_iff`) for an eigenvector `y`; the dot
product `y ⬝ s = y_c G_s(θ)` for secular eigenvectors; `x ⬝ s = x_c s_c + ∑ x_{v_i}(σ_i + λ_i/θ)`
when `x_ℓ = x_{v_i}/θ`; and the test vectors of the proof of Lemma 3.2 (`secVec`, `lvec`, the
kernel vectors `e_u - e_u'` and `zvec`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix P8Basic

namespace P8Main

variable {k : ℕ} (a : Fin k → ℕ)

theorem dot_TV (x s : TV a → ℝ) :
    x ⬝ᵥ s = x none * s none + ∑ i, (x (some ⟨i, none⟩) * s (some ⟨i, none⟩) +
      ∑ j, x (some ⟨i, some j⟩) * s (some ⟨i, some j⟩)) := by
  rw [dotProduct, sum_TV]

section Eigen

variable {a} {y : TV a → ℝ} {θ : ℝ}

theorem eig_c (hy : adjT a *ᵥ y = θ • y) : θ * y none = ∑ i, y (some ⟨i, none⟩) :=
  ((mulVec_eq_smul_iff a y θ).1 hy).1

theorem eig_v (hy : adjT a *ᵥ y = θ • y) (i : Fin k) :
    θ * y (some ⟨i, none⟩) = y none + ∑ j, y (some ⟨i, some j⟩) :=
  ((mulVec_eq_smul_iff a y θ).1 hy).2.1 i

theorem eig_l (hy : adjT a *ᵥ y = θ • y) (i : Fin k) (j : Fin (a i)) :
    θ * y (some ⟨i, some j⟩) = y (some ⟨i, none⟩) :=
  ((mulVec_eq_smul_iff a y θ).1 hy).2.2 i j

/-- `(θ² - a_i) y_{v_i} = θ y_c`. -/
theorem eig_v' (hy : adjT a *ᵥ y = θ • y) (i : Fin k) :
    (θ ^ 2 - (a i : ℝ)) * y (some ⟨i, none⟩) = θ * y none := by
  have h2 : ∑ j, θ * y (some ⟨i, some j⟩) = (a i : ℝ) * y (some ⟨i, none⟩) := by
    simp only [eig_l hy i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : θ * (θ * y (some ⟨i, none⟩)) = θ * y none + (a i : ℝ) * y (some ⟨i, none⟩) := by
    rw [eig_v hy i, mul_add, Finset.mul_sum, h2]
  linear_combination h3

/-- For `θ ≠ 0`: `y_ℓ = y_{v_i}/θ`. -/
theorem eig_l' (hy : adjT a *ᵥ y = θ • y) (hθ : θ ≠ 0) (i : Fin k) (j : Fin (a i)) :
    y (some ⟨i, some j⟩) = y (some ⟨i, none⟩) / θ := by
  rw [← eig_l hy i j, mul_div_cancel_left₀ _ hθ]

end Eigen

/-- If `x_ℓ = x_{v_i}/θ` on every leaf, then `x ⬝ s = x_c s_c + ∑_i x_{v_i}(σ_i + λ_i/θ)`. -/
theorem dot_of_leaf (x s : TV a → ℝ) (θ : ℝ)
    (hl : ∀ i (j : Fin (a i)), x (some ⟨i, some j⟩) = x (some ⟨i, none⟩) / θ) :
    x ⬝ᵥ s = x none * sc a s + ∑ i, x (some ⟨i, none⟩) * (sig a s i + lam a s i / θ) := by
  rw [dot_TV]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [hl, sig, lam]
  rw [← Finset.mul_sum]
  ring

/-- For an eigenvector of a secular `θ`: `y ⬝ s = y_c G_s(θ)`. -/
theorem dot_secular {y : TV a → ℝ} {θ : ℝ} (hy : adjT a *ᵥ y = θ • y) (hθ : θ ≠ 0)
    (hne : ∀ i, θ ^ 2 ≠ (a i : ℝ)) (hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1) (s : TV a → ℝ) :
    y ⬝ᵥ s = y none * Gs a s θ := by
  have hv : ∀ i, y (some ⟨i, none⟩) = θ * y none / (θ ^ 2 - (a i : ℝ)) := by
    intro i
    rw [← eig_v' hy i]
    field_simp [sub_ne_zero.2 (hne i)]
  have hsc : y none * sc a s = ∑ i, y none * sc a s / (θ ^ 2 - (a i : ℝ)) := by
    calc y none * sc a s = y none * sc a s * ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) := by
          rw [hF, mul_one]
      _ = ∑ i, y none * sc a s / (θ ^ 2 - (a i : ℝ)) := by
          rw [Finset.mul_sum]
          simp only [mul_one_div]
  rw [dot_of_leaf a y s θ (eig_l' hy hθ), Gs_eq, hsc, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hd : θ ^ 2 - (a i : ℝ) ≠ 0 := sub_ne_zero.2 (hne i)
  rw [hv i]
  field_simp
  ring

/-- The secular eigenvector `x^θ` of Lemma 3.1(i). -/
theorem secVec_eigen {θ : ℝ} (hne : ∀ i, θ ^ 2 ≠ (a i : ℝ))
    (hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1) : adjT a *ᵥ secVec a θ = θ • secVec a θ := by
  rw [mulVec_eq_smul_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [secVec]
    calc θ * 1 = θ * ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) := by rw [hF]
      _ = ∑ i, θ / (θ ^ 2 - (a i : ℝ)) := by
          rw [Finset.mul_sum]
          simp only [mul_one_div]
  · simp only [secVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd : θ ^ 2 - (a i : ℝ) ≠ 0 := sub_ne_zero.2 (hne i)
    field_simp
    ring
  · simp only [secVec]
    ring

theorem secVec_ne_zero (θ : ℝ) : secVec a θ ≠ 0 := by
  intro h
  have := congrFun h none
  simp [secVec] at this

/-- `x_c = 0`, `x_{v_i} = w_i`, `x_ℓ = w_i/θ` for `ℓ ∈ L_i` (the vectors of Lemma 3.1(ii)). -/
noncomputable def lvec (w : Fin k → ℝ) (θ : ℝ) : TV a → ℝ :=
  mkSw a 0 w (fun i _ => w i / θ)

theorem lvec_eigen (w : Fin k → ℝ) {θ : ℝ} (hθ : θ ≠ 0)
    (hw : ∀ i, w i ≠ 0 → (a i : ℝ) = θ ^ 2) (hsum : ∑ i, w i = 0) :
    adjT a *ᵥ lvec a w θ = θ • lvec a w θ := by
  rw [mulVec_eq_smul_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp [lvec, mkSw, hsum]
  · simp only [lvec, mkSw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      zero_add]
    by_cases h : w i = 0
    · simp [h]
    · rw [hw i h]
      field_simp
  · simp only [lvec, mkSw]
    field_simp

theorem lvec_dot (w : Fin k → ℝ) (θ : ℝ) (s : TV a → ℝ) :
    lvec a w θ ⬝ᵥ s = ∑ i, w i * (sig a s i + lam a s i / θ) := by
  rw [dot_of_leaf a _ s θ (fun i j => rfl)]
  simp [lvec, mkSw]

/-- The eigenvector `e_{v_i} + e_{L_i}/θ - e_{v_i'} - e_{L_i'}/θ` for `a_i = a_i' = θ²`. -/
theorem pair_eigen {i i' : Fin k} {θ : ℝ} (hθ : θ ≠ 0) (hi : (a i : ℝ) = θ ^ 2)
    (hi' : (a i' : ℝ) = θ ^ 2) :
    adjT a *ᵥ lvec a (Pi.single i 1 - Pi.single i' 1) θ =
      θ • lvec a (Pi.single i 1 - Pi.single i' 1) θ := by
  apply lvec_eigen a _ hθ
  · intro m hm
    by_cases h1 : m = i
    · rw [h1, hi]
    · by_cases h2 : m = i'
      · rw [h2, hi']
      · exfalso
        apply hm
        simp [h1, h2]
  · simp [Finset.sum_sub_distrib]

theorem pair_dot (i i' : Fin k) (θ : ℝ) (s : TV a → ℝ) :
    lvec a (Pi.single i 1 - Pi.single i' 1) θ ⬝ᵥ s =
      (sig a s i + lam a s i / θ) - (sig a s i' + lam a s i' / θ) := by
  rw [lvec_dot]
  simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

theorem pair_ne_zero {i i' : Fin k} (h : i ≠ i') (θ : ℝ) :
    lvec a (Pi.single i 1 - Pi.single i' 1) θ ≠ 0 := by
  intro h0
  have := congrFun h0 (some ⟨i, none⟩)
  simp [lvec, mkSw, h] at this

theorem single_sub_dot (u u' : TV a) (s : TV a → ℝ) :
    (Pi.single u (1 : ℝ) - Pi.single u' 1) ⬝ᵥ s = s u - s u' := by
  rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

/-- `e_ℓ - e_ℓ'` lies in the kernel for two leaves `ℓ, ℓ'` of one branch. -/
theorem leafDiff_ker (i : Fin k) (j j' : Fin (a i)) :
    adjT a *ᵥ (Pi.single (some ⟨i, some j⟩) (1 : ℝ) - Pi.single (some ⟨i, some j'⟩) 1) = 0 := by
  rw [mulVec_sub, mulVec_single_one, mulVec_single_one]
  funext u
  rw [Pi.sub_apply, col_apply, col_apply, Pi.zero_apply, sub_eq_zero]
  rcases u with _ | ⟨m, _ | l⟩ <;> simp [adjT_apply]

/-- `e_{v_i} - e_{v_i'}` lies in the kernel for two bare branches `i, i'`. -/
theorem bareDiff_ker (i i' : Fin k) (hi : a i = 0) (hi' : a i' = 0) :
    adjT a *ᵥ (Pi.single (some ⟨i, none⟩) (1 : ℝ) - Pi.single (some ⟨i', none⟩) 1) = 0 := by
  rw [mulVec_sub, mulVec_single_one, mulVec_single_one]
  funext u
  rw [Pi.sub_apply, col_apply, col_apply, Pi.zero_apply, sub_eq_zero]
  rcases u with _ | ⟨m, _ | l⟩
  · simp [adjT_apply]
  · simp [adjT_apply]
  · have hm : i ≠ m := by
      rintro rfl
      have := l.isLt
      omega
    have hm' : i' ≠ m := by
      rintro rfl
      have := l.isLt
      omega
    simp [adjT_apply, hm, hm']

/-- The kernel vector with `x_c = 1`, `x_{v_i} = 0`, `x_ℓ = -1/a_i` (when no branch is bare). -/
noncomputable def zvec : TV a → ℝ := mkSw a 1 0 (fun i _ => -1 / (a i : ℝ))

theorem zvec_ker (h : ∀ i, a i ≠ 0) : adjT a *ᵥ zvec a = (0 : ℝ) • zvec a := by
  rw [mulVec_eq_smul_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp [zvec, mkSw]
  · simp only [zvec, mkSw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (a i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (h i)
    field_simp
    ring
  · simp [zvec, mkSw]

theorem zvec_dot (s : TV a → ℝ) : zvec a ⬝ᵥ s = sc a s - ∑ i, lam a s i / (a i : ℝ) := by
  rw [dot_TV, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [zvec, mkSw, Pi.zero_apply, one_mul, zero_mul, zero_add, sc, lam]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum]
  ring

end P8Main
