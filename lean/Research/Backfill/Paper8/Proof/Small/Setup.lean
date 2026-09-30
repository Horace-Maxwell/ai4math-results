import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Basic

/-!
# Paper 8, Proposition 5.1: common facts for trees with `b* ≤ 1`

For `a : Fin k → ℕ` with all `a i ≤ 1`: membership in `Ib` and `Bset`, `kb` as a cardinality,
`k = k₀ + k₁` and `∑ aᵢ = k₁`, the secular polynomial for `B = {0}`, `{1}`, `{0, 1}`, the
two-term form of `Gs`, the data `sc`, `sig`, `lam`, `Lamb` of switchings built with `mkSw`,
signed counting sums, and the sum of the standard leaf sums `lamStd` over `I₁`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Small

section Counts

variable {k : ℕ} (a : Fin k → ℕ)

theorem mem_Ib {b : ℕ} {i : Fin k} : i ∈ Ib a b ↔ a i = b := by
  simp [Ib]

theorem mem_Bset {b : ℕ} : b ∈ Bset (branchMS a) ↔ ∃ i, a i = b := by
  simp [Bset, branchMS]

theorem kb_eq (b : ℕ) : kb (branchMS a) b = (Ib a b).card := by
  rw [kb, branchMS, Multiset.count_map, Ib, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  exact eq_comm

theorem card_I0_add_card_I1 (ha : ∀ i, a i ≤ 1) : (Ib a 0).card + (Ib a 1).card = k := by
  have h : Ib a 0 = Finset.univ.filter (fun i => ¬ a i = 1) := by
    ext i
    simp only [Ib, Finset.mem_filter, Finset.mem_univ, true_and]
    have := ha i
    omega
  rw [h, Ib, add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ,
    Fintype.card_fin]

theorem sum_a_eq (ha : ∀ i, a i ≤ 1) : ∑ i, a i = (Ib a 1).card := by
  rw [Ib, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have := ha i
  split_ifs with h <;> omega

theorem Bset_sub (ha : ∀ i, a i ≤ 1) : Bset (branchMS a) ⊆ {0, 1} := by
  intro b hb
  obtain ⟨i, rfl⟩ := (mem_Bset a).1 hb
  have := ha i
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem Ib_eq_empty {b : ℕ} (hb : b ∉ Bset (branchMS a)) : Ib a b = ∅ := by
  ext i
  simp only [mem_Ib, Finset.notMem_empty, iff_false]
  intro h
  exact hb ((mem_Bset a).2 ⟨i, h⟩)

end Counts

section Secular

theorem aeval_secular (m : Multiset ℕ) (x : ℝ) :
    aeval x (secular m) = ∏ b ∈ Bset m, (x - b) -
      ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, (x - b') := by
  simp [secular, map_prod, map_sum]

variable {k : ℕ} (a : Fin k → ℕ)

theorem Bset_01 (ha : ∀ i, a i ≤ 1) (h0 : (Ib a 0).Nonempty) (h1 : (Ib a 1).Nonempty) :
    Bset (branchMS a) = {0, 1} := by
  apply le_antisymm (Bset_sub a ha)
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · obtain ⟨i, hi⟩ := h0
    exact (mem_Bset a).2 ⟨i, (mem_Ib a).1 hi⟩
  · obtain ⟨i, hi⟩ := h1
    exact (mem_Bset a).2 ⟨i, (mem_Ib a).1 hi⟩

theorem Bset_single (hk : 0 < k) {b : ℕ} (hall : ∀ i, a i = b) : Bset (branchMS a) = {b} := by
  ext b'
  rw [mem_Bset, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    exact hall i
  · rintro rfl
    exact ⟨⟨0, hk⟩, hall _⟩

/-- `R(x) = x(x - 1) - (k₀(x - 1) + k₁x)` when `B = {0, 1}`. -/
theorem aeval_secular_01 (ha : ∀ i, a i ≤ 1) (h0 : (Ib a 0).Nonempty) (h1 : (Ib a 1).Nonempty)
    (x : ℝ) :
    aeval x (secular (branchMS a)) =
      x * (x - 1) - ((kb (branchMS a) 0 : ℝ) * (x - 1) + (kb (branchMS a) 1 : ℝ) * x) := by
  rw [aeval_secular, Bset_01 a ha h0 h1, Finset.prod_pair (by norm_num),
    Finset.sum_pair (by norm_num)]
  have e0 : ({0, 1} : Finset ℕ).erase 0 = {1} := by decide
  have e1 : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
  rw [e0, e1]
  simp

/-- `R(x) = x - k_b` when all branches have the same size `b`. -/
theorem aeval_secular_single (hk : 0 < k) {b : ℕ} (hall : ∀ i, a i = b) (x : ℝ) :
    aeval x (secular (branchMS a)) = (x - b) - (kb (branchMS a) b : ℝ) := by
  rw [aeval_secular, Bset_single a hk hall]
  simp

end Secular

section Gs

variable {k : ℕ} (a : Fin k → ℕ)

theorem Lamb_zero (s : TV a → ℝ) : Lamb a s 0 = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have h := (mem_Ib a).1 hi
  apply Finset.sum_eq_zero
  intro j _
  have := j.isLt
  omega

/-- `Gs` has at most two terms, `b = 0` and `b = 1`, when `b* ≤ 1`. -/
theorem Gs_eq (ha : ∀ i, a i ≤ 1) (s : TV a → ℝ) (θ : ℝ) :
    Gs a s θ = (Ab a s 0 + Sb a s 0 * θ) / θ ^ 2 + (Ab a s 1 + Sb a s 1 * θ) / (θ ^ 2 - 1) := by
  rw [Gs, Finset.sum_subset (Bset_sub a ha)]
  · rw [Finset.sum_pair (by norm_num)]
    simp
  · intro b _ hb
    have hI := Ib_eq_empty a hb
    have hk : kb (branchMS a) b = 0 := by rw [kb_eq, hI, Finset.card_empty]
    simp [BackfillPaper8.Challenge.Ab, Sb, Lamb, hI, hk]

variable (c : ℝ) (mid : Fin k → ℝ) (leafS : (i : Fin k) → Fin (a i) → ℝ)

@[simp] theorem sc_mkSw : sc a (mkSw a c mid leafS) = c := rfl

@[simp] theorem sig_mkSw (i : Fin k) : sig a (mkSw a c mid leafS) i = mid i := rfl

@[simp] theorem mkSw_leaf (i : Fin k) (j : Fin (a i)) :
    mkSw a c mid leafS (some ⟨i, some j⟩) = leafS i j := rfl

theorem lam_mkSw_const (g : Fin k → ℝ) (i : Fin k) :
    lam a (mkSw a c mid (fun i _ => g i)) i = (a i : ℝ) * g i := by
  simp [lam]

theorem Sb_mkSw (b : ℕ) : Sb a (mkSw a c mid leafS) b = ∑ i ∈ Ib a b, mid i := rfl

theorem Lamb_mkSw_one_const (g : Fin k → ℝ) :
    Lamb a (mkSw a c mid (fun i _ => g i)) 1 = ∑ i ∈ Ib a 1, g i := by
  unfold Lamb
  apply Finset.sum_congr rfl
  intro i hi
  rw [lam_mkSw_const, (mem_Ib a).1 hi]
  simp

theorem isSwitching_mkSw (hc : c = 1 ∨ c = -1) (hmid : ∀ i, mid i = 1 ∨ mid i = -1)
    (hleaf : ∀ i j, leafS i j = 1 ∨ leafS i j = -1) : IsSwitching (mkSw a c mid leafS) := by
  intro v
  rcases v with _ | ⟨i, _ | j⟩
  · exact hc
  · exact hmid i
  · exact hleaf i j

end Gs

section Sums

variable {k : ℕ}

/-- `∑_{i ∈ s} (if i = x then -1 else 1) = |s| - 2 [x ∈ s]`. -/
theorem sum_sign_eq (s : Finset (Fin k)) (x : Fin k) :
    ∑ i ∈ s, (if i = x then (-1 : ℝ) else 1) = s.card - 2 * (if x ∈ s then 1 else 0) := by
  have h : ∀ i, (if i = x then (-1 : ℝ) else 1) = 1 - 2 * (if i = x then 1 else 0) := by
    intro i
    split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- `∑_i (if i ∈ U then -1 else 1) = k - 2|U|`. -/
theorem sum_sign_mem (U : Finset (Fin k)) :
    ∑ i, (if i ∈ U then (-1 : ℝ) else 1) = k - 2 * U.card := by
  have h : ∀ i, (if i ∈ U then (-1 : ℝ) else 1) = 1 - 2 * (if i ∈ U then 1 else 0) := by
    intro i
    split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

end Sums

end P8Small
