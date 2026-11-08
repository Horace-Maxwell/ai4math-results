import Research.Backfill.Paper1.Prop31FirstDeviation

/-! Static normalized-norm and complete-tail (C3) argument. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral ICGEqualParity
namespace Prop31

def normalizedD (q : ℝ) (b : ℕ) : ℝ := Challenge.dNorm b q / q ^ b

lemma normalizedD_pos {q : ℝ} (hq : 2 < q) (b : ℕ) : 0 < normalizedD q b := by
  unfold normalizedD
  rw [Additional.dNorm_eq_L1]
  exact div_pos (L1_sgnv_pos hq b) (pow_pos (by linarith) _)

lemma normalizedD_succ {q : ℝ} (hq : 2 < q) (b : ℕ) :
    normalizedD q (b + 1) = normalizedD q b + 2 * nu q (b + 1) := by
  have hq0 : q ≠ 0 := by linarith
  unfold normalizedD
  rw [ClosedForms.dNorm_succ hq, ← ClosedForms.weighted_nu_eq_deltaK hq,
    pow_succ]
  field_simp [hq0]

lemma normalizedD_mono {q : ℝ} (hq : 2 < q) {s b : ℕ} (hs : s ≤ b) :
    normalizedD q s ≤ normalizedD q b := by
  induction b, hs using Nat.le_induction with
  | base => exact le_rfl
  | succ b hsb ih =>
    rw [normalizedD_succ hq]
    have hn := nu_pos hq (b + 1)
    linarith

lemma normalizedD_ge_add_last {q : ℝ} (hq : 2 < q) {s b : ℕ} (hs : s < b) :
    normalizedD q s + 2 * nu q b ≤ normalizedD q b := by
  have hm := normalizedD_mono hq (show s ≤ b - 1 by omega)
  have he := normalizedD_succ hq (b - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ b by omega)] at he
  linarith

lemma normalizedD_one {q : ℝ} (hq : 2 < q) : normalizedD q 1 = Challenge.Dhat1 q := by
  unfold normalizedD Challenge.Dhat1
  rw [ClosedForms.dNorm_eq_dClosed hq]
  norm_num [Challenge.dClosed, Finset.sum_range_succ]
  ring

lemma normalizedD_two {q : ℝ} (hq : 2 < q) : normalizedD q 2 = Challenge.Dhat2 q := by
  unfold normalizedD Challenge.Dhat2
  rw [ClosedForms.dNorm_eq_dClosed hq]
  norm_num [Challenge.dClosed, Finset.sum_range_succ]
  ring

lemma ratio_lower {D A ρ d : ℝ} (hA : 0 ≤ A) (hρ : 0 < ρ)
    (hd : ρ ≤ d) (hD : A + 2 * ρ ≤ D) : A / d + 2 ≤ D / ρ := by
  have hd0 : 0 < d := lt_of_lt_of_le hρ hd
  have hquot : 0 ≤ A / d := div_nonneg hA hd0.le
  have hm := mul_le_mul_of_nonneg_right hd hquot
  have he : d * (A / d) = A := by field_simp
  rw [he] at hm
  apply (le_div_iff₀ hρ).mpr
  nlinarith

lemma normalized_ratio_even {q : ℝ} (hq : 2 < q) {b : ℕ}
    (hb : 1 ≤ b) (heven : Even b) :
    Challenge.Dhat1 q / Challenge.mu q 1 + 2 ≤ normalizedD q b / nu q b := by
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := heven; omega
  apply ratio_lower
  · rw [← normalizedD_one hq]; exact (normalizedD_pos hq 1).le
  · exact nu_pos hq b
  · have hm1 : Challenge.mu q 1 = nu q 2 := by simpa using Additional.mu_nat_eq_nu q 1
    rw [hm1]
    exact nu_even_le_two (by linarith) heven hb2
  · rw [← normalizedD_one hq]
    exact normalizedD_ge_add_last hq (by omega)

lemma normalized_ratio_odd {q : ℝ} (hq : 2 < q) {b : ℕ}
    (hb : 3 ≤ b) (hodd : Odd b) :
    Challenge.Dhat2 q / Challenge.muInf q + 2 ≤ normalizedD q b / nu q b := by
  apply ratio_lower
  · rw [← normalizedD_two hq]; exact (normalizedD_pos hq 2).le
  · exact nu_pos hq b
  · exact (nu_odd_lt (by linarith) hodd).le
  · rw [← normalizedD_two hq]
    exact normalizedD_ge_add_last hq (by omega)

lemma C3_actual {q Δ δ : ℝ} (hq : 2 < q) (hΔ : 0 < Δ) {a b : ℕ}
    (hb : 1 ≤ b) (hpar : b % 2 = a % 2)
    (hC3 : if Even a then Δ * (Challenge.Dhat1 q / Challenge.mu q 1 + 2) > 2 * δ
      else Δ * Challenge.Dhat1 q / Challenge.mu q 0 > 2 * δ ∧
        Δ * (Challenge.Dhat2 q / Challenge.muInf q + 2) > 2 * δ) :
    2 * δ < Δ * (normalizedD q b / nu q b) := by
  by_cases ha : Even a
  · rw [ite_eq_left ha] at hC3
    have hbE : Even b := by rw [Nat.even_iff, hpar]; exact Nat.even_iff.mp ha
    exact hC3.trans_le (mul_le_mul_of_nonneg_left (normalized_ratio_even hq hb hbE) hΔ.le)
  · rw [ite_eq_right ha] at hC3
    have hbO : Odd b := by
      have ham : a % 2 ≠ 0 := by simpa only [Nat.even_iff] using ha
      rw [Nat.odd_iff]; omega
    by_cases hb1 : b = 1
    · subst b
      rw [normalizedD_one hq, ← Additional.mu_nat_eq_nu q 0]
      convert hC3.1 using 1; ring
    · have hb3 : 3 ≤ b := by have := Nat.odd_iff.mp hbO; omega
      exact hC3.2.trans_le (mul_le_mul_of_nonneg_left (normalized_ratio_odd hq hb3 hbO) hΔ.le)

lemma whole_chain_sum {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b))
    {p q : ℝ} (hreg : Challenge.Regions p q) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) {g : ℕ → ℝ} (hg : Challenge.IsSignVec a g)
    (hlast : ∀ i ≤ a, Y i b = g i) (hchain : TailChain a b b Y g) :
    (∑ j ∈ range b, Challenge.psiCol a b p q Y j) =
      q * Challenge.DeltaC a p g * (normalizedD q b - nu q b) := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hcol := ((check_Lemma23 a b ha hb hab p q hreg Y hY).1 g hg b le_rfl hlast hchain).2
  have hterm : ∀ j < b, Challenge.psiCol a b p q Y j =
      ColumnIdentity.coeff q j * Challenge.DeltaC a p g := by
    intro j hj
    have hh := hcol (b - j) (by omega) (Nat.sub_le _ _)
    rw [show b - (b - j) = j by omega] at hh
    have hind : (b : ℤ) - (b - j : ℕ) - 1 = (j : ℤ) - 1 := by omega
    rw [hind] at hh
    exact hh
  have hbudget := ColumnIdentity.alternating_budget hq b
  rw [Additional.mu_pred_eq_nu] at hbudget
  have hqpow : q ^ b ≠ 0 := pow_ne_zero _ (by linarith)
  have hcoeff : (∑ j ∈ range b, ColumnIdentity.coeff q j) =
      q * (normalizedD q b - nu q b) := by
    unfold normalizedD
    apply (mul_left_cancel₀ hqpow)
    field_simp [hqpow]
    nlinarith [hbudget]
  calc
    _ = ∑ j ∈ range b, ColumnIdentity.coeff q j * Challenge.DeltaC a p g :=
      Finset.sum_congr rfl (fun j hj => hterm j (Finset.mem_range.mp hj))
    _ = (∑ j ∈ range b, ColumnIdentity.coeff q j) * Challenge.DeltaC a p g :=
      (Finset.sum_mul _ _ _).symm
    _ = q * Challenge.DeltaC a p g * (normalizedD q b - nu q b) := by
      rw [hcoeff]; ring

lemma whole_chain_strict {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b))
    (hpar : b % 2 = a % 2) {p q : ℝ} (hreg : Challenge.Regions p q)
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y)
    {g : ℕ → ℝ} (hg : Challenge.IsSignVec a g)
    (hlast : ∀ i ≤ a, Y i b = g i) (hchain : TailChain a b b Y g)
    (hΔ : 0 < Challenge.DeltaC a p g)
    (hC3 : if Even a then
        Challenge.DeltaC a p g * (Challenge.Dhat1 q / Challenge.mu q 1 + 2) > 2 * Challenge.deltaK a p
      else Challenge.DeltaC a p g * Challenge.Dhat1 q / Challenge.mu q 0 > 2 * Challenge.deltaK a p ∧
        Challenge.DeltaC a p g * (Challenge.Dhat2 q / Challenge.muInf q + 2) > 2 * Challenge.deltaK a p) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hratio := C3_actual hq hΔ hb hpar hC3
  have hν := nu_pos hq b
  have hclear : 2 * Challenge.deltaK a p * nu q b <
      Challenge.DeltaC a p g * normalizedD q b := by
    have hh := mul_lt_mul_of_pos_right hratio hν
    have he : Challenge.DeltaC a p g * (normalizedD q b / nu q b) * nu q b =
        Challenge.DeltaC a p g * normalizedD q b := by field_simp
    rwa [he] at hh
  apply strict_of_surplus hq a b p Y
  have hdelta : Challenge.DeltaC a p (Challenge.col Y b) = Challenge.DeltaC a p g :=
    DeltaC_congr a p hlast
  rw [whole_chain_sum ha hb hab hreg hY hg hlast hchain,
    hdelta, Additional.mu_pred_eq_nu]
  have hh := mul_lt_mul_of_pos_left hclear (show 0 < q by linarith)
  nlinarith

end Prop31
end CodexPaper1
