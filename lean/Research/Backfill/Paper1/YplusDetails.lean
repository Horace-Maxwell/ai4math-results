import Research.Backfill.Paper1.GeneralEquality
import Research.Backfill.Paper1.PathLinearConvex

/-! Exact retained proof formulas at note.tex T936--941 and T951.
These named internal proof lemmas do not enlarge the 51 frozen research contracts.
No machine acceptance is claimed by this source. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace PaperDetails

lemma path_last_unit (q : ℝ) (b r : ℕ) (hr : r ≤ b) :
    Zp q b (fun t => if t = b then 1 else 0) r = 1 / q ^ (b - r) := by
  simp [Zp, Wp, mul_ite, hr, phiX]

lemma plus_path_natural {q : ℝ} (hq : 2 < q) (a b r i : ℕ) (hr : r ≤ b) :
    Zp q b (Challenge.Yplus a b i) r =
      sgnv r * nu q (b - r) * Challenge.sAlt i -
        2 * (q ^ (b - r))⁻¹ * (if i = a then 1 else 0) := by
  have hy : Challenge.Yplus a b i = fun t =>
      Challenge.sAlt i * sgnv t + (-2 * (if i = a then 1 else 0)) *
        (if t = b then 1 else 0) := by
    funext t
    by_cases hia : i = a
    · by_cases htb : t = b
      · simp [Challenge.Yplus, Challenge.sAlt, sgnv, hia, htb]
        ring
      · simp [Challenge.Yplus, Challenge.sAlt, sgnv, hia, htb]
    · simp [Challenge.Yplus, Challenge.sAlt, sgnv, hia]
  rw [hy, Zp_linear, ICGEqualParityB.Zp_sgnv_eq hq hr, path_last_unit q b r hr]
  ring

lemma plus_zeta_closed {q : ℝ} (hq : 2 < q) (a b : ℕ) (j : ℤ)
    (hj : -1 ≤ j) (hjb : j ≤ (b : ℤ) - 1) (i : ℕ) :
    Challenge.zetaPath b q (Challenge.Yplus a b) j i =
      (-1 : ℝ) ^ (j + 1) * Challenge.mu q ((b : ℤ) - 2 - j) * Challenge.sAlt i -
        2 * q ^ (j + 1 - (b : ℤ)) * (if i = a then 1 else 0) := by
  let r := (j + 1).toNat
  have hr : r ≤ b := by dsimp [r]; omega
  have hrz : (r : ℤ) = j + 1 := by dsimp [r]; omega
  have hmu : Challenge.mu q ((b : ℤ) - 2 - j) = nu q (b - r) := by
    unfold Challenge.mu
    rw [Additional.muSeq_eq_nu]
    congr 1
    omega
  have hsign : (-1 : ℝ) ^ (j + 1) = sgnv r := by
    rw [← hrz, zpow_natCast]
    rfl
  have hpow : q ^ (j + 1 - (b : ℤ)) = (q ^ (b - r))⁻¹ := by
    rw [show j + 1 - (b : ℤ) = -((b - r : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
  change Challenge.z q b (Challenge.Yplus a b i) j = _
  rw [NarrowPath.z_eq_Zp (by linarith : q ≠ 0) b j hj hjb,
    hmu, hsign, hpow]
  exact plus_path_natural hq a b r i hr

lemma transform_sub_unit (a : ℕ) (p c d : ℝ) (i : ℕ) :
    Challenge.tMulVec a p
      (fun t => c * Challenge.sAlt t - d * (if t = a then 1 else 0)) i =
      c * GeneralEquality.alpha a p i - d * GeneralEquality.unitColumn a p i := by
  unfold GeneralEquality.alpha GeneralEquality.unitColumn Challenge.tMulVec
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · simp [mul_ite, mul_comm]

lemma plus_transformed_closed {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ) (j : ℤ)
    (hj : -1 ≤ j) (hjb : j ≤ (b : ℤ) - 1) (i : ℕ) :
    Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) j) i =
      ((-1 : ℝ) ^ (j + 1) * Challenge.mu q ((b : ℤ) - 2 - j)) *
        GeneralEquality.alpha a p i -
      (2 * q ^ (j + 1 - (b : ℤ))) * GeneralEquality.unitColumn a p i := by
  have he : Challenge.zetaPath b q (Challenge.Yplus a b) j = fun t =>
      ((-1 : ℝ) ^ (j + 1) * Challenge.mu q ((b : ℤ) - 2 - j)) * Challenge.sAlt t -
        (2 * q ^ (j + 1 - (b : ℤ))) * (if t = a then 1 else 0) := by
    funext t
    exact plus_zeta_closed hq a b j hj hjb t
  rw [he, transform_sub_unit]

lemma alpha_signed {p q : ℝ} (hreg : Challenge.Regions p q) {a i : ℕ}
    (ha : 2 ≤ a) (hi : i ≤ a) :
    0 < |GeneralEquality.alpha a p i| ∧
      sgnv (a - i) * GeneralEquality.alpha a p i = |GeneralEquality.alpha a p i| := by
  have hp := (GeneralEquality.region_strict hreg ha).1
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  by_cases he : i = a
  · subst i
    rw [GeneralEquality.alpha_last hp, Nat.sub_self, sgnv_zero, one_mul,
      abs_of_nonneg (by have := (GeneralEquality.region_strict hreg ha).2.2.2.1; linarith)]
    exact ⟨by have := (GeneralEquality.region_strict hreg ha).2.2.2.1; linarith, rfl⟩
  · have hit : i < a := lt_of_le_of_ne hi he
    rw [GeneralEquality.alpha_row_abs hp hit]
    constructor
    · have hn := nu_pos hp i
      positivity
    · rw [GeneralEquality.alpha_row hp hit]
      calc
        sgnv (a - i) * (sgnv (a - i) * p ^ (a - 1) * (p - 1) * (1 + nu p i)) =
            (sgnv (a - i) * sgnv (a - i)) * p ^ (a - 1) * (p - 1) * (1 + nu p i) := by ring
        _ = _ := by rw [GeneralEquality.sign_sq, one_mul]

lemma plus_signed_cell_closed {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b)) {j i : ℕ} (hj : j < b) (hi : i ≤ a) :
    Real.sign (Challenge.tMulVec a p (Challenge.col (Challenge.Yplus a b) j) i) =
      (-1 : ℝ) ^ (j + a - i) ∧
    (-1 : ℝ) ^ (j + a - i) *
      Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) j) i =
      -Challenge.mu q ((b : ℤ) - 2 - j) * |GeneralEquality.alpha a p i| -
        2 * (-1 : ℝ) ^ (j + a - i) * q ^ ((j : ℤ) + 1 - b) *
          GeneralEquality.unitColumn a p i := by
  have _hY := GeneralEquality.plus_sign hab
  have _hb0 : 0 < b := by omega
  have hq := (GeneralEquality.region_strict hreg ha).2.1
  have hsig : (-1 : ℝ) ^ (j + a - i) = sgnv j * sgnv (a - i) := by
    rw [show j + a - i = j + (a - i) by omega, pow_add]
    rfl
  have halpha := alpha_signed hreg ha hi
  have hA := Chain.tMulVec_scale_of_eq a p _ _ Challenge.sAlt
    (GeneralEquality.col_plus_early hj) i
  change Challenge.tMulVec a p (Challenge.col (Challenge.Yplus a b) j) i =
      sgnv j * GeneralEquality.alpha a p i at hA
  have hsa : (-1 : ℝ) ^ (j + a - i) *
      Challenge.tMulVec a p (Challenge.col (Challenge.Yplus a b) j) i =
        |GeneralEquality.alpha a p i| := by
    rw [hA, hsig]
    calc
      (sgnv j * sgnv (a - i)) * (sgnv j * GeneralEquality.alpha a p i) =
          (sgnv j * sgnv j) * (sgnv (a - i) * GeneralEquality.alpha a p i) := by ring
      _ = _ := by rw [GeneralEquality.sign_sq, one_mul, halpha.2]
  constructor
  · rcases neg_one_pow_eq_or ℝ (j + a - i) with hs | hs
    · rw [hs, one_mul] at hsa
      rw [Real.sign_of_pos (by linarith [halpha.1]), hs]
    · rw [hs, neg_one_mul] at hsa
      rw [Real.sign_of_neg (by linarith [halpha.1]), hs]
  · rw [plus_transformed_closed hq a b p j (by omega) (by omega) i,
      show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
    change (-1 : ℝ) ^ (j + a - i) *
        ((sgnv (j + 1) * Challenge.mu q ((b : ℤ) - 2 - j)) *
          GeneralEquality.alpha a p i -
          (2 * q ^ (((j + 1 : ℕ) : ℤ) - b)) * GeneralEquality.unitColumn a p i) = _
    rw [sgnv_succ]
    calc
      _ = -Challenge.mu q ((b : ℤ) - 2 - j) *
          ((sgnv j * sgnv j) * (sgnv (a - i) * GeneralEquality.alpha a p i)) -
          2 * (-1 : ℝ) ^ (j + a - i) * q ^ (((j + 1 : ℕ) : ℤ) - b) *
            GeneralEquality.unitColumn a p i := by rw [hsig]; ring
      _ = _ := by rw [GeneralEquality.sign_sq, one_mul, halpha.2]

lemma plus_terminal_closed {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b)) :
    Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) (-1)) a =
      Challenge.mu q ((b : ℤ) - 1) * Challenge.deltaK a p - 2 * q ^ (-(b : ℤ)) ∧
    ((q - 2) * Challenge.deltaK a p - 2) / q ≤
      Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) (-1)) a ∧
    0 < ((q - 2) * Challenge.deltaK a p - 2) / q := by
  have _hY := GeneralEquality.plus_sign hab
  obtain ⟨hp, hq, hP, hd, _⟩ := GeneralEquality.region_strict hreg ha
  have hq0 : 0 < q := by linarith
  have he := plus_transformed_closed hq a b p (-1) (by norm_num) (by omega) a
  rw [show (b : ℤ) - 2 - (-1) = (b : ℤ) - 1 by ring,
    show (-1 : ℤ) + 1 = 0 by norm_num, zpow_zero, one_mul,
    zero_sub, GeneralEquality.alpha_last hp, GeneralEquality.unitColumn_last, mul_one] at he
  refine ⟨he, ?_, ?_⟩
  · have hm := (nu_bounds hq.le b).1
    rw [← Additional.mu_pred_eq_nu] at hm
    have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ Challenge.deltaK a p by linarith)
    have hpow : q ^ (-(b : ℤ)) ≤ 1 / q := by
      simpa only [zpow_neg_one, one_div] using
        zpow_le_zpow_right₀ (show 1 ≤ q by linarith) (show -(b : ℤ) ≤ -1 by omega)
    rw [he]
    calc
      ((q - 2) * Challenge.deltaK a p - 2) / q =
          ((q - 2) / q) * Challenge.deltaK a p - 2 * (1 / q) := by ring
      _ ≤ _ := sub_le_sub hmul (mul_le_mul_of_nonneg_left hpow (by norm_num))
  · apply div_pos _ hq0
    nlinarith

end PaperDetails
#print axioms PaperDetails.plus_zeta_closed
#print axioms PaperDetails.plus_signed_cell_closed
#print axioms PaperDetails.plus_terminal_closed
end CodexPaper1
