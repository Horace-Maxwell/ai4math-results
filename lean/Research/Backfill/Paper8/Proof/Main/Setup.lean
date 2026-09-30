import Research.Backfill.Paper8.Proof.Basic

/-!
# Paper 8, agent `main`: branch sizes, the secular polynomial and `G_s`

Sums over branches regrouped by branch size (`Bset`, `Ib`, `kb`), the value of the secular
polynomial `R(t)` and its factorization `R(t) = ∏_{b∈B} (t - b) · (1 - F(t))` off `B`, the
characterization `IsSecular θ ↔ (∀ i, θ² ≠ a_i) ∧ ∑_i 1/(θ² - a_i) = 1`, and the formula
`G_s(θ) = ∑_i (s_c + λ_i + σ_i θ)/(θ² - a_i)`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Main

variable {k : ℕ} (a : Fin k → ℕ)

theorem Bset_branchMS : Bset (branchMS a) = Finset.univ.image a := rfl

theorem mem_Bset_iff (b : ℕ) : b ∈ Bset (branchMS a) ↔ ∃ i, a i = b := by
  simp [Bset_branchMS]

theorem mem_Ib_iff (b : ℕ) (i : Fin k) : i ∈ Ib a b ↔ a i = b := by
  simp [Ib]

theorem kb_branchMS (b : ℕ) : kb (branchMS a) b = (Ib a b).card := by
  rw [kb, branchMS, Multiset.count_map, Ib, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

/-- Regrouping a sum over the branches by branch size. -/
theorem sum_Bset_Ib {M : Type*} [AddCommMonoid M] (g : Fin k → M) :
    ∑ b ∈ Bset (branchMS a), ∑ i ∈ Ib a b, g i = ∑ i, g i := by
  rw [Bset_branchMS]
  exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem a (Finset.mem_univ i)) g

/-- `∑_{b∈B} k_b/(t - b) = ∑_i 1/(t - a_i)`. -/
theorem sum_kb_div (t : ℝ) :
    ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) / (t - (b : ℝ)) =
      ∑ i, 1 / (t - (a i : ℝ)) := by
  rw [← sum_Bset_Ib a]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h : ∀ i ∈ Ib a b, 1 / (t - (a i : ℝ)) = 1 / (t - (b : ℝ)) := by
    intro i hi
    rw [(mem_Ib_iff a b i).1 hi]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, kb_branchMS, mul_one_div]

/-- `G_s(θ) = ∑_i (s_c + λ_i + σ_i θ)/(θ² - a_i)`. -/
theorem Gs_eq (s : TV a → ℝ) (θ : ℝ) :
    Gs a s θ = ∑ i, (sc a s + lam a s i + sig a s i * θ) / (θ ^ 2 - (a i : ℝ)) := by
  rw [← sum_Bset_Ib a]
  unfold Gs
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h : ∀ i ∈ Ib a b, (sc a s + lam a s i + sig a s i * θ) / (θ ^ 2 - (a i : ℝ)) =
      (sc a s + lam a s i + sig a s i * θ) / (θ ^ 2 - (b : ℝ)) := by
    intro i hi
    rw [(mem_Ib_iff a b i).1 hi]
  rw [Finset.sum_congr rfl h, ← Finset.sum_div]
  congr 1
  simp only [BackfillPaper8.Challenge.Ab, Sb, Lamb, kb_branchMS, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
  ring

/-- The value of the secular polynomial at a real `t`. -/
theorem aeval_secular (m : Multiset ℕ) (t : ℝ) :
    aeval t (secular m) = ∏ b ∈ Bset m, (t - (b : ℝ)) -
      ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, (t - (b' : ℝ)) := by
  simp [secular, map_prod, map_sum]

/-- Off `B`: `R(t) = ∏_{b∈B} (t - b) · (1 - ∑_{b∈B} k_b/(t - b))`. -/
theorem aeval_secular_of_ne (m : Multiset ℕ) (t : ℝ) (ht : ∀ b ∈ Bset m, t ≠ (b : ℝ)) :
    aeval t (secular m) = (∏ b ∈ Bset m, (t - (b : ℝ))) *
      (1 - ∑ b ∈ Bset m, (kb m b : ℝ) / (t - (b : ℝ))) := by
  rw [aeval_secular, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hne : t - (b : ℝ) ≠ 0 := sub_ne_zero.2 (ht b hb)
  rw [← Finset.prod_erase_mul _ _ hb]
  field_simp

/-- `R(a_i) ≠ 0`: no branch size is a root of the secular polynomial. -/
theorem aeval_secular_at (i : Fin k) : aeval (a i : ℝ) (secular (branchMS a)) ≠ 0 := by
  have hb : a i ∈ Bset (branchMS a) := (mem_Bset_iff a _).2 ⟨i, rfl⟩
  rw [aeval_secular, Finset.prod_eq_zero hb (sub_self _), zero_sub, neg_ne_zero,
    Finset.sum_eq_single (a i)]
  · apply mul_ne_zero
    · rw [kb_branchMS]
      exact_mod_cast (Finset.card_pos.2 ⟨i, (mem_Ib_iff a _ i).2 rfl⟩).ne'
    · rw [Finset.prod_ne_zero_iff]
      intro b' hb'
      rw [sub_ne_zero]
      exact_mod_cast (Finset.ne_of_mem_erase hb').symm
  · intro b hbB hne
    rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hne h.symm, hb⟩) (sub_self _), mul_zero]
  · intro h
    exact absurd hb h

theorem ne_of_mem_Bset {t : ℝ} (hne : ∀ i, t ≠ (a i : ℝ)) :
    ∀ b ∈ Bset (branchMS a), t ≠ (b : ℝ) := by
  intro b hb
  obtain ⟨i, rfl⟩ := (mem_Bset_iff a b).1 hb
  exact hne i

/-- `θ` is secular iff `θ²` is not a branch size and `F(θ²) = 1`. -/
theorem isSecular_iff (θ : ℝ) :
    IsSecular (branchMS a) θ ↔
      (∀ i, θ ^ 2 ≠ (a i : ℝ)) ∧ ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1 := by
  unfold IsSecular
  constructor
  · intro h
    have hne : ∀ i, θ ^ 2 ≠ (a i : ℝ) := by
      intro i hi
      rw [hi] at h
      exact aeval_secular_at a i h
    refine ⟨hne, ?_⟩
    have hB := ne_of_mem_Bset a hne
    rw [aeval_secular_of_ne _ _ hB, sum_kb_div] at h
    have hP : ∏ b ∈ Bset (branchMS a), (θ ^ 2 - (b : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun b hb => sub_ne_zero.2 (hB b hb))
    have := (mul_eq_zero.1 h).resolve_left hP
    linarith
  · rintro ⟨hne, hF⟩
    rw [aeval_secular_of_ne _ _ (ne_of_mem_Bset a hne), sum_kb_div, hF, sub_self, mul_zero]

/-- A secular value is nonzero. -/
theorem ne_zero_of_isSecular {θ : ℝ} (h : IsSecular (branchMS a) θ) : θ ≠ 0 := by
  rintro rfl
  have h1 := ((isSecular_iff a 0).1 h).2
  have h2 : ∑ i, 1 / ((0 : ℝ) ^ 2 - (a i : ℝ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply one_div_nonpos.2
    have : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
    nlinarith
  linarith

theorem kb_zero_eq_zero_iff : kb (branchMS a) 0 = 0 ↔ ∀ i, a i ≠ 0 := by
  rw [kb_branchMS, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp [mem_Ib_iff]

end P8Main
