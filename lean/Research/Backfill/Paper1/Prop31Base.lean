import Research.Backfill.Paper1.GeneralEquality

/-!
Static source: the general CondS/column-budget part of Proposition31.
All conditions below are the frozen Challenge conditions. These helper
proofs do not assert that Proposition31 or any certificate has been accepted.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31

lemma delta_nonneg {p : ℝ} (hp : 2 < p) {a : ℕ} {c : ℕ → ℝ}
    (hc : Challenge.IsSignVec a c) : 0 ≤ Challenge.DeltaC a p c := by
  unfold Challenge.DeltaC
  rw [Additional.dNorm_eq_L1, Additional.l1_tMulVec_eq_L1]
  exact sub_nonneg.mpr (L1_le_sgnv hp hc)

lemma delta_pos {p : ℝ} (hp : 2 < p) {a : ℕ} {c : ℕ → ℝ}
    (hc : Challenge.IsSignVec a c) (hne : ¬ Challenge.IsPmAlt a c) :
    0 < Challenge.DeltaC a p c := by
  have hnon := delta_nonneg hp hc
  by_contra h
  have hz : Challenge.DeltaC a p c = 0 := by linarith
  unfold Challenge.DeltaC at hz
  rw [Additional.dNorm_eq_L1, Additional.l1_tMulVec_eq_L1] at hz
  exact hne (L1_eq_sgnv hp hc (by linarith))

lemma tMulVec_abs_le_rowAbs (a : ℕ) (p : ℝ) (ζ : ℕ → ℝ)
    (hζ : ∀ j ≤ a, |ζ j| ≤ 1) (i : ℕ) :
    |Challenge.tMulVec a p ζ i| ≤ Challenge.rowAbsSum a p i := by
  unfold Challenge.tMulVec Challenge.rowAbsSum
  calc
    _ ≤ ∑ j ∈ range (a + 1), |Challenge.tEntry a p i j * ζ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (a + 1), |Challenge.tEntry a p i j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (hζ j (by simpa using Finset.mem_range.mp hj)) (abs_nonneg _)).trans_eq
        (mul_one _)

lemma psi_positive_of_CondS {a : ℕ} (ha : 2 ≤ a) {p q Pm : ℝ}
    (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {c ζ : ℕ → ℝ} (hc : Challenge.IsSignVec a c)
    (hna : ¬ Challenge.IsPmAlt a c) (hζ : ∀ i ≤ a, |ζ i| ≤ 1) :
    0 < Challenge.psi a p q μ c ζ := by
  let Δ := Challenge.DeltaC a p c
  let B := ∑ i ∈ range (a + 1),
    max 0 (|Challenge.tMulVec a p ζ i| - (q - 1) * |Challenge.tMulVec a p c i|)
  let Bm := ∑ i ∈ range (a + 1),
    max 0 (Challenge.rowAbsSum a p i - Pm * |Challenge.tMulVec a p c i|)
  have hΔ : 0 < Δ := delta_pos (OneColumn.region_bounds hreg).1 hc hna
  have hB : B ≤ Bm := by
    apply Finset.sum_le_sum
    intro i hi
    apply max_le_max le_rfl
    have hw := tMulVec_abs_le_rowAbs a p ζ hζ i
    have hp := mul_le_mul_of_nonneg_right hPm (abs_nonneg (Challenge.tMulVec a p c i))
    linarith
  have hS' : Bm < Pm * Δ := hS c hc hna
  have hPΔ : 0 < (q - 1) * Δ :=
    mul_pos (by have := (OneColumn.region_bounds hreg).2.1; linarith) hΔ
  have hgap : 0 < (q - 1) * Δ - B := by
    have hm := mul_le_mul_of_nonneg_right hPm hΔ.le
    linarith
  have haff : 0 < (q - 1) * (1 + μ) * Δ - 2 * μ * B := by
    have hx := mul_nonneg (by linarith : 0 ≤ 1 - μ) hPΔ.le
    have hy := mul_nonneg hμ0 hgap.le
    by_cases hz : μ = 0
    · subst μ; nlinarith
    · have hy' := mul_pos (lt_of_le_of_ne hμ0 (Ne.symm hz)) hgap
      nlinarith
  have hh := (check_Lemma22 a ha p q hreg μ hμ0 hμ1 c ζ hc hζ).1
  exact haff.trans_le hh

lemma psi_nonneg_of_CondS {a : ℕ} (ha : 2 ≤ a) {p q Pm : ℝ}
    (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {c ζ : ℕ → ℝ} (hc : Challenge.IsSignVec a c)
    (hζ : ∀ i ≤ a, |ζ i| ≤ 1) :
    0 ≤ Challenge.psi a p q μ c ζ ∧
      (Challenge.psi a p q μ c ζ = 0 → Challenge.IsPmAlt a c) := by
  by_cases halt : Challenge.IsPmAlt a c
  · exact ⟨((check_Lemma22 a ha p q hreg μ hμ0 hμ1 c ζ hc hζ).2 halt).2.1,
      fun _ => halt⟩
  · have hp := psi_positive_of_CondS ha hreg hPm hS hμ0 hμ1 hc halt hζ
    exact ⟨hp.le, fun hz => False.elim (hp.ne' hz)⟩

lemma psiCol_nonneg {a b : ℕ} (ha : 2 ≤ a) {p q Pm : ℝ}
    (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) {j : ℕ} (hj : j < b) :
    0 ≤ Challenge.psiCol a b p q Y j ∧
      (Challenge.psiCol a b p q Y j = 0 → Challenge.IsPmAlt a (Challenge.col Y j)) := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have h0 : 0 ≤ Challenge.mu q ((j : ℤ) - 1) := by
    rw [Additional.mu_pred_eq_nu]; exact (nu_pos hq j).le
  have h1 : Challenge.mu q ((j : ℤ) - 1) ≤ 1 := by
    rw [Additional.mu_pred_eq_nu]; exact (nu_bounds hq.le j).2
  have hz := GeneralEquality.zeta_bound (show 1 ≤ q by linarith) hY
    (show j + 1 ≤ b by omega)
  rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega] at hz
  exact psi_nonneg_of_CondS ha hreg hPm hS h0 h1
    (fun i hi => hY i hi j hj.le) hz

lemma budget {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) :
    (∑ j ∈ range b, Challenge.psiCol a b p q Y j) +
        q * Challenge.mu q ((b : ℤ) - 1) *
          (Challenge.DeltaC a p (Challenge.col Y b) - 2 * Challenge.deltaK a p) ≤
      q ^ (1 - (b : ℤ)) * (Challenge.Theta a b p q - Challenge.Gval a b p q Y) := by
  rw [ColumnIdentity.identity hq]
  have hneg : 0 ≤ Challenge.negPt
      (Challenge.tMulVec a p (Challenge.zetaPath b q Y (-1)) a) := le_max_right _ _
  have hm := mul_nonneg (show 0 ≤ 2 * q by linarith) hneg
  linarith

lemma strict_of_surplus {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ)
    (hs : q * Challenge.mu q ((b : ℤ) - 1) *
        (2 * Challenge.deltaK a p - Challenge.DeltaC a p (Challenge.col Y b)) <
      ∑ j ∈ range b, Challenge.psiCol a b p q Y j) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  have hh := budget hq a b p Y
  have hx : 0 < q ^ (1 - (b : ℤ)) := zpow_pos (by linarith) _
  have hm : 0 < q ^ (1 - (b : ℤ)) *
      (Challenge.Theta a b p q - Challenge.Gval a b p q Y) := by nlinarith
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hx).mp hm)

lemma triple_congr (a b : ℕ) (p q : ℝ) {Y Y' : ℕ → ℕ → ℝ}
    (he : Challenge.MatEq a b Y Y') (u v : ℕ) :
    Challenge.triple a b p q Y u v = Challenge.triple a b p q Y' u v := by
  unfold Challenge.triple
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [he i (by simpa using Finset.mem_range.mp hi)
    j (by simpa using Finset.mem_range.mp hj)]

lemma Gval_congr (a b : ℕ) (p q : ℝ) {Y Y' : ℕ → ℕ → ℝ}
    (he : Challenge.MatEq a b Y Y') :
    Challenge.Gval a b p q Y = Challenge.Gval a b p q Y' := by
  unfold Challenge.Gval
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [triple_congr a b p q he u v]

lemma minus_value {p q : ℝ} (hp : 2 < p) (hq : 2 < q) (a b : ℕ) :
    Challenge.Gval a b p q Challenge.Yminus = Challenge.Theta a b p q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hdpa : 0 < Challenge.deltaK a p := by
    rw [← ClosedForms.weighted_nu_eq_deltaK hp a]
    exact mul_pos (pow_pos hp0 a) (nu_pos hp a)
  have hdqb : 0 < Challenge.deltaK b q := by
    rw [← ClosedForms.weighted_nu_eq_deltaK hq b]
    exact mul_pos (pow_pos hq0 b) (nu_pos hq b)
  have he : Challenge.triple a b p q Challenge.Yminus a b =
      -(Challenge.deltaK a p * Challenge.deltaK b q) := by
    rw [PathAndSign.triple_eq_Mentry p q a b Challenge.Yminus a b le_rfl le_rfl]
    rw [Mentry_prod p q a b
      (e := fun i => -sgnv i) (f := sgnv)
      (by intro i hi j hj; dsimp [Challenge.Yminus, Challenge.sAlt, sgnv]; ring)]
    have hm := Tv_smul p a (-1) sgnv a
    simp only [neg_one_mul] at hm
    rw [hm]
    have hpa := ClosedForms.last_alt_eq_deltaK hp a
    have hqb := ClosedForms.last_alt_eq_deltaK hq b
    rw [Additional.tMulVec_eq_Tv p a Challenge.sAlt a le_rfl] at hpa
    rw [Additional.tMulVec_eq_Tv q b Challenge.sAlt b le_rfl] at hqb
    change Tv p a sgnv a = Challenge.deltaK a p at hpa
    change Tv q b sgnv b = Challenge.deltaK b q at hqb
    rw [hpa, hqb]
    ring
  rw [ColumnIdentity.Gval_corner, PathAndSign.l1Mat_triple_eq_L1mat,
    PathAndSign.checkerboard_value p q a b Challenge.Yminus
      (Or.inr (by intros; rfl)), he]
  rw [← Additional.dNorm_eq_L1, ← Additional.dNorm_eq_L1]
  unfold Challenge.negPt Challenge.Theta
  rw [neg_neg, max_eq_left (mul_pos hdpa hdqb).le]
  ring

lemma plus_case {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b))
    {p q Pm : ℝ} (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y)
    (hLast : ∀ i ≤ a, Y i b = Challenge.gPlus a i) :
    Challenge.Gval a b p q Y ≤ Challenge.Theta a b p q ∧
      (Challenge.Gval a b p q Y = Challenge.Theta a b p q ↔
        Challenge.MatEq a b Y (Challenge.Yplus a b)) := by
  have hp := (OneColumn.region_bounds hreg).1
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hnon : ∀ j ∈ range b, 0 ≤ Challenge.psiCol a b p q Y j :=
    fun j hj => (psiCol_nonneg ha hreg hPm hS hY (Finset.mem_range.mp hj)).1
  have hsum := Finset.sum_nonneg hnon
  have hdelta : Challenge.DeltaC a p (Challenge.col Y b) = 2 * Challenge.deltaK a p := by
    rw [Chain.delta_sign_scale a p 0 (Challenge.col Y b) (Challenge.gPlus a)
      (by intro i hi; simpa only [pow_zero, one_mul, Challenge.col] using hLast i hi)]
    exact GeneralEquality.delta_gPlus (by omega) hp
  have hbudget := budget hq a b p Y
  rw [hdelta, sub_self, mul_zero, add_zero] at hbudget
  have hzpow : 0 < q ^ (1 - (b : ℤ)) := zpow_pos (by linarith) _
  have hle : Challenge.Gval a b p q Y ≤ Challenge.Theta a b p q := by
    have hx : 0 ≤ q ^ (1 - (b : ℤ)) *
        (Challenge.Theta a b p q - Challenge.Gval a b p q Y) := hsum.trans hbudget
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hzpow).mp hx)
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    rw [heq, sub_self, mul_zero] at hbudget
    have hCols : ∀ j < b, Challenge.IsPmAlt a (Challenge.col Y j) ∧
        Challenge.psiCol a b p q Y j = 0 := by
      intro j hj
      have hjle := Finset.single_le_sum hnon (Finset.mem_range.mpr hj)
      have hnj := (psiCol_nonneg ha hreg hPm hS hY hj).1
      have hzero : Challenge.psiCol a b p q Y j = 0 := by linarith
      exact ⟨(psiCol_nonneg ha hreg hPm hS hY hj).2 hzero, hzero⟩
    exact GeneralEquality.uniqueness hreg ha hab hY hLast hCols
  · intro heq
    rw [Gval_congr a b p q heq]
    exact GeneralEquality.plus_value hreg ha hb hab

end Prop31
end CodexPaper1
