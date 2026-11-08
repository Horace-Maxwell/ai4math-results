import Research.Backfill.Paper1.Chain
import Research.Backfill.Paper1.OneColumn
import Research.Backfill.Paper1.ColumnIdentity
import Research.ICGEqualParityBMain

/-! General-dimensional scalar, transform and path facts for frozen Lemma24.
Acceptance evidence is recorded separately. No acceptance claim is made here. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace GeneralEquality

def alpha (a : ℕ) (p : ℝ) (i : ℕ) : ℝ := Challenge.tMulVec a p Challenge.sAlt i

def unitColumn (a : ℕ) (p : ℝ) (i : ℕ) : ℝ := Challenge.tEntry a p i a

def state (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (i k : ℕ) : ℝ :=
  Zp q b (ColumnIdentity.row a p Y i) k

lemma sign_sq (j : ℕ) : sgnv j * sgnv j = (1 : ℝ) := by
  rcases sgnv_isSign j j le_rfl with h | h <;> rw [h] <;> norm_num

lemma sign_abs (j : ℕ) : |sgnv j| = (1 : ℝ) := by
  exact abs_neg_one_pow j

lemma even_sum_sign {a b : ℕ} (hab : Even (a + b)) : sgnv a = sgnv b := by
  have hprod : sgnv a * sgnv b = (1 : ℝ) := by
    unfold sgnv
    rw [← pow_add, hab.neg_one_pow]
  have hsq := sign_sq b
  rcases sgnv_isSign b b le_rfl with h | h <;> rw [h] at hprod ⊢ <;> linarith

lemma gPlus_last (a : ℕ) : Challenge.gPlus a a = -1 := by
  unfold Challenge.gPlus Challenge.sAlt
  have h := sign_sq a
  change (-1 : ℝ) ^ a * (-1 : ℝ) ^ a = 1 at h
  simp only [h]
  norm_num

lemma gPlus_early {a i : ℕ} (hi : i < a) :
    Challenge.gPlus a i = sgnv a * sgnv i := by
  simp [Challenge.gPlus, Challenge.sAlt, sgnv, hi.ne]

lemma gPlus_sign (a : ℕ) : Challenge.IsSignVec a (Challenge.gPlus a) := by
  intro i hi
  by_cases hia : i = a
  · subst i; exact Or.inr (gPlus_last a)
  · rw [gPlus_early (lt_of_le_of_ne hi hia)]
    rcases sgnv_isSign a a le_rfl with ha | ha <;>
      rcases sgnv_isSign a i hi with hi | hi <;> rw [ha, hi] <;> norm_num

lemma gPlus_repeat {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) :
    Challenge.gPlus a j = Challenge.gPlus a (j + 1) ↔ j = a - 1 := by
  by_cases he : j = a - 1
  · subst j
    have hj1 : a - 1 + 1 = a := by omega
    have hs : sgnv (a - 1) = -sgnv a := by
      have h := sgnv_succ (a - 1)
      rw [hj1] at h
      linarith
    simp only [gPlus_early (show a - 1 < a by omega), hj1, gPlus_last, hs]
    have hsq := sign_sq a
    constructor
    · intro _; trivial
    · intro _; nlinarith
  · have hj1 : j + 1 < a := by omega
    rw [gPlus_early hj, gPlus_early hj1, sgnv_succ]
    have hne : sgnv a * sgnv j ≠ 0 := by
      unfold sgnv
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    constructor
    · intro h; exact False.elim (hne (by linarith))
    · exact False.elim ∘ he

lemma delta_gPlus {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 2 < p) :
    Challenge.DeltaC a p (Challenge.gPlus a) = 2 * Challenge.deltaK a p := by
  have hslack : slack p a (Challenge.gPlus a) = 2 * nu p a := by
    unfold slack
    rw [Finset.sum_eq_single (a - 1)]
    · have hlast : a - 1 + 1 = a := by omega
      rw [ite_eq_left ((gPlus_repeat ha (by omega)).mpr rfl), hlast, Zp_self, gPlus_last]
      norm_num
    · intro j hj hne
      rw [ite_eq_right (fun h => hne ((gPlus_repeat ha (Finset.mem_range.mp hj)).mp h))]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  unfold Challenge.DeltaC
  rw [Additional.dNorm_eq_L1, Additional.l1_tMulVec_eq_L1,
    L1_sign hp (show IsSign a (Challenge.gPlus a) from gPlus_sign a), L1_sgnv hp,
    hslack, ← ClosedForms.weighted_nu_eq_deltaK hp a]
  ring

lemma alpha_last {p : ℝ} (hp : 2 < p) (a : ℕ) :
    alpha a p a = Challenge.deltaK a p :=
  ClosedForms.last_alt_eq_deltaK hp a

lemma alpha_row {p : ℝ} (hp : 2 < p) {a i : ℕ} (hi : i < a) :
    alpha a p i = sgnv (a - i) * p ^ (a - 1) * (p - 1) * (1 + nu p i) := by
  have hp0 : p ≠ 0 := by linarith
  have hidx : a - 1 - i + i + 1 = a := by omega
  have hn : a - 1 - i + 1 = a - i := by omega
  have hrow := Tv_row hp0 (a - 1 - i) i sgnv
  rw [hidx, ICGEqualParityB.Zp_sgnv_eq hp (by omega),
    ICGEqualParityB.Zp_sgnv_eq hp (by omega),
    show a - (a - 1 - i + 1) = i by omega,
    show a - (a - 1 - i) = i + 1 by omega, hn] at hrow
  have hs : sgnv (a - 1 - i) = -sgnv (a - i) := by
    have h := sgnv_succ (a - 1 - i)
    rw [hn] at h
    linarith
  have hpow : p ^ a = p ^ (a - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  unfold alpha
  rw [Additional.tMulVec_eq_Tv p a Challenge.sAlt i hi.le]
  change Tv p a sgnv i = _
  rw [hrow, hs, nu_succ, hpow]
  field_simp [hp0]
  ring

lemma alpha_row_abs {p : ℝ} (hp : 2 < p) {a i : ℕ} (hi : i < a) :
    |alpha a p i| = p ^ (a - 1) * (p - 1) * (1 + nu p i) := by
  rw [alpha_row hp hi]
  have hp0 : 0 < p := by linarith
  have hnu := nu_pos hp i
  simp only [abs_mul, sign_abs, one_mul, abs_of_pos (pow_pos hp0 _),
    abs_of_pos (show 0 < p - 1 by linarith), abs_of_pos (show 0 < 1 + nu p i by linarith)]

lemma unitColumn_early {a i : ℕ} (hi : i < a) (p : ℝ) :
    unitColumn a p i = p ^ (a - i - 1) * (p - 1) := by
  simp [unitColumn, Challenge.tEntry, hi]

lemma unitColumn_last (a : ℕ) (p : ℝ) : unitColumn a p a = 1 := by
  simp [unitColumn, Challenge.tEntry]

lemma delta_lower {p : ℝ} (hp : 2 < p) {a : ℕ} (ha : 1 ≤ a) :
    p ^ (a - 1) * (p - 2) ≤ Challenge.deltaK a p := by
  have hp0 : 0 < p := by linarith
  have h := mul_le_mul_of_nonneg_left (nu_bounds hp.le a).1 (pow_pos hp0 a).le
  rw [ClosedForms.weighted_nu_eq_deltaK hp a] at h
  have hpow : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  have he : p ^ a * ((p - 2) / p) = p ^ (a - 1) * (p - 2) := by
    rw [hpow]
    field_simp [hp0.ne']
  rwa [he] at h

lemma region_strict {p q : ℝ} (hreg : Challenge.Regions p q) {a : ℕ} (ha : 2 ≤ a) :
    2 < p ∧ 2 < q ∧ 2 ≤ q - 1 ∧ 3 ≤ Challenge.deltaK a p ∧
      p ^ a < (q - 1) * Challenge.deltaK a p := by
  have hp := (OneColumn.region_bounds hreg).1
  have hP := (OneColumn.region_bounds hreg).2.1
  have hp0 : 0 < p := by linarith
  have hlow := delta_lower hp (by omega : 1 ≤ a)
  have hpow : p ≤ p ^ (a - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p) (by omega : 1 ≤ a - 1)
  have hexp : p ^ a = p ^ (a - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have hpw := pow_pos hp0 (a - 1)
  have hp3 : 3 ≤ p := by
    rcases hreg with ⟨hp5, _⟩ | ⟨hp3, _⟩ <;> linarith
  refine ⟨hp, by linarith, hP, ?_, ?_⟩
  · have hmon := mul_le_mul hpow (show (1 : ℝ) ≤ p - 2 by linarith)
        zero_le_one hpw.le
    nlinarith
  · rw [hexp]
    have hfactor : p < (q - 1) * (p - 2) := by
      rcases hreg with ⟨hp5, _⟩ | ⟨hp3, hq5⟩
      · nlinarith
      · subst p; nlinarith
    have hstrict := mul_lt_mul_of_pos_left hfactor hpw
    have hmul := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ q - 1)
    nlinarith

lemma unit_le_half_alpha {p q : ℝ} (hreg : Challenge.Regions p q)
    {a : ℕ} (ha : 2 ≤ a) {i : ℕ} (hi : i ≤ a) :
    0 ≤ unitColumn a p i ∧ 2 * unitColumn a p i ≤ |alpha a p i| := by
  have hp := (OneColumn.region_bounds hreg).1
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  by_cases he : i = a
  · subst i
    rw [unitColumn_last, alpha_last hp]
    have hd := (region_strict hreg ha).2.2.2.1
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith
  · have hit : i < a := lt_of_le_of_ne hi he
    rw [unitColumn_early hit, alpha_row_abs hp hit]
    constructor
    · positivity
    · by_cases hiz : i = 0
      · subst i
        simp only [Nat.sub_zero, nu_zero]
        ring_nf
        exact le_rfl
      · have hi1 : 1 ≤ i := by omega
        have hpi : p ≤ p ^ i := by
          simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p) hi1
        have hni := nu_pos hp i
        have hsplit : a - 1 = (a - i - 1) + i := by omega
        rw [hsplit, pow_add]
        have hprod : 2 ≤ p ^ i * (1 + nu p i) := by nlinarith
        have hw : 0 ≤ p ^ (a - i - 1) * (p - 1) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hprod hw]

lemma tMulVec_last_sub (a : ℕ) (p c : ℝ) (w : ℕ → ℝ) (u : ℕ) :
    Challenge.tMulVec a p (fun i => c * w i - if i = a then 2 else 0) u =
      c * Challenge.tMulVec a p w u - 2 * unitColumn a p u := by
  unfold Challenge.tMulVec unitColumn
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [mul_comm]

lemma tMul_gPlus (a : ℕ) (p : ℝ) (i : ℕ) :
    Challenge.tMulVec a p (Challenge.gPlus a) i =
      sgnv a * alpha a p i - 2 * unitColumn a p i := by
  exact tMulVec_last_sub a p (sgnv a) Challenge.sAlt i

lemma col_plus_early {a b j : ℕ} (hj : j < b) :
    ∀ i ≤ a, Challenge.col (Challenge.Yplus a b) j i = sgnv j * Challenge.sAlt i := by
  intro i _
  simp [Challenge.col, Challenge.Yplus, hj.ne, Challenge.sAlt, sgnv, mul_comm]

lemma col_plus_last {a b : ℕ} (hab : Even (a + b)) :
    ∀ i ≤ a, Challenge.Yplus a b i b = Challenge.gPlus a i := by
  intro i _
  unfold Challenge.Yplus Challenge.gPlus
  change Challenge.sAlt i * sgnv b - (if i = a ∧ b = b then 2 else 0) =
    sgnv a * Challenge.sAlt i - (if i = a then 2 else 0)
  rw [even_sum_sign hab]
  simp [mul_comm]

lemma plus_sign {a b : ℕ} (hab : Even (a + b)) :
    Challenge.IsSignMat a b (Challenge.Yplus a b) := by
  intro i hi j hj
  by_cases hcorner : i = a ∧ j = b
  · rcases hcorner with ⟨rfl, rfl⟩
    right
    simp only [Challenge.Yplus, Challenge.sAlt, ← pow_add, hab.neg_one_pow]
    norm_num
  · simp only [Challenge.Yplus, ite_eq_right hcorner, sub_zero, Challenge.sAlt, ← pow_add]
    exact neg_one_pow_eq_or ℝ (i + j)

lemma state_eq_zeta {q : ℝ} (hq : q ≠ 0) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (i k : ℕ) (hk : k ≤ b) :
    state a b p q Y i k =
      Challenge.tMulVec a p (Challenge.zetaPath b q Y ((k : ℤ) - 1)) i :=
  ColumnIdentity.Zp_row_eq_zeta hq a b p Y i k hk

lemma zeta_bound {q : ℝ} (hq : 1 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) {k : ℕ} (hk : k ≤ b) :
    ∀ i ≤ a, |Challenge.zetaPath b q Y ((k : ℤ) - 1) i| ≤ 1 := by
  intro i hi
  unfold Challenge.zetaPath
  rw [PathAndSign.z_pred_eq_Zp (by linarith : q ≠ 0) b (Y i) k hk]
  apply Zp_abs_le hq _ k hk
  intro j hj
  rcases hY i hi j hj with h | h <;> rw [h] <;> norm_num

lemma state_bound {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y) {i k : ℕ}
    (hi : i ≤ a) (hk : k ≤ b) :
    |state a b p q Y i k| ≤ (q - 1) * |alpha a p i| := by
  have hq1 : 1 ≤ q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  rw [state_eq_zeta (by linarith : q ≠ 0) a b p Y i k hk]
  unfold alpha
  rw [Additional.tMulVec_eq_Tv p a _ i hi, Additional.tMulVec_eq_Tv p a _ i hi]
  exact OneColumn.alt_row_dominates hreg a (zeta_bound hq1 hY hk) hi

lemma state_last_bound {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y) {k : ℕ} (hk : k ≤ b) :
    |state a b p q Y a k| ≤ p ^ a := by
  have hp := (OneColumn.region_bounds hreg).1
  have hp0 : 0 < p := by linarith
  have hq1 : 1 ≤ q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  rw [state_eq_zeta (by linarith : q ≠ 0) a b p Y a k hk,
    Additional.tMulVec_eq_Tv p a _ a le_rfl, Tv_last hp0.ne', abs_mul,
    abs_of_pos (pow_pos hp0 a)]
  have hz := Zp_abs_le (by linarith : 1 ≤ p) (zeta_bound hq1 hY hk) 0 (Nat.zero_le a)
  nlinarith [pow_pos hp0 a]

lemma state_succ_zeta {q : ℝ} (hq : q ≠ 0) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (i j : ℕ) (hj : j < b) :
    state a b p q Y i (j + 1) = Challenge.tMulVec a p (Challenge.zetaPath b q Y j) i := by
  rw [state_eq_zeta hq a b p Y i (j + 1) hj]
  rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]

lemma state_rec {q : ℝ} (hq : q ≠ 0) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (i j : ℕ) (hj : j < b) :
    state a b p q Y i j =
      (state a b p q Y i (j + 1) +
        (q - 1) * Challenge.tMulVec a p (Challenge.col Y j) i) / q := by
  exact Zp_rec hq b (ColumnIdentity.row a p Y i) hj

lemma state_last (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (i : ℕ) :
    state a b p q Y i b = Challenge.tMulVec a p (Challenge.col Y b) i :=
  Zp_self q b (ColumnIdentity.row a p Y i)

lemma dot_step_nonneg {P A B : ℝ} (hB : |B| ≤ P * |A|) :
    0 ≤ A * (B + P * A) := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA] at hB
    have hb : 0 ≤ B + P * A := by linarith [neg_abs_le B]
    exact mul_nonneg hA hb
  · rw [abs_of_nonpos hA] at hB
    have hb : B + P * A ≤ 0 := by linarith [le_abs_self B]
    exact mul_nonneg_of_nonpos_of_nonpos hA hb

lemma dot_base_nonneg {A u : ℝ} (hu : 0 ≤ u) (hAu : 2 * u ≤ |A|) :
    0 ≤ A * (A - 2 * u) := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA] at hAu
    exact mul_nonneg hA (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos hA (by linarith)

lemma cell_zero_of_dot {P μ A B : ℝ} (hdot : A * B ≤ 0) (hB : |B| ≤ P * |A|) :
    Challenge.hcell P μ A B = 0 := by
  rcases lt_trichotomy A 0 with hA | hA | hA
  · have hBn : 0 ≤ B := by nlinarith
    rw [abs_of_nonneg hBn, abs_of_neg hA] at hB
    exact ICGEqualParity.hcell_opp' hA.le hBn (by linarith)
  · subst A
    have hB0 : B = 0 := by simpa using (abs_nonpos_iff.mp (by simpa using hB))
    subst B
    simp [Challenge.hcell]
  · have hBn : B ≤ 0 := by nlinarith
    rw [abs_of_nonpos hBn, abs_of_pos hA] at hB
    exact ICGEqualParity.hcell_opp hA.le hBn (by linarith)

lemma state_column_dot {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y) {i j : ℕ}
    (hi : i ≤ a) (hj : j < b)
    (hc : ∀ t ≤ a, Challenge.col Y j t = sgnv j * Challenge.sAlt t) :
    0 ≤ (sgnv j * alpha a p i) * state a b p q Y i j := by
  have hq0 : 0 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  rw [state_rec hq0.ne' a b p Y i j hj,
    Chain.tMulVec_scale_of_eq a p _ _ Challenge.sAlt hc i]
  change 0 ≤ (sgnv j * alpha a p i) *
    ((state a b p q Y i (j + 1) + (q - 1) * (sgnv j * alpha a p i)) / q)
  rw [← mul_div_assoc]
  apply div_nonneg _ hq0.le
  apply dot_step_nonneg
  rw [abs_mul, sign_abs, one_mul]
  exact state_bound hreg hY hi hj

lemma state_last_step_pos {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y) {j : ℕ}
    (hj : j < b)
    (hc : ∀ t ≤ a, Challenge.col Y j t = sgnv j * Challenge.sAlt t) :
    0 < sgnv j * state a b p q Y a j := by
  obtain ⟨hp, hq, _hP, _hd, hstrict⟩ := region_strict hreg ha
  have hb := state_last_bound hreg hY (show j + 1 ≤ b by omega)
  rw [state_rec (by linarith : q ≠ 0) a b p Y a j hj,
    Chain.tMulVec_scale_of_eq a p _ _ Challenge.sAlt hc a]
  change 0 < sgnv j *
    ((state a b p q Y a (j + 1) + (q - 1) * (sgnv j * alpha a p a)) / q)
  rw [alpha_last hp]
  rcases sgnv_isSign j j le_rfl with hs | hs
  · rw [hs, one_mul, one_mul]
    apply div_pos _ (by linarith)
    linarith [neg_abs_le (state a b p q Y a (j + 1))]
  · rw [hs]
    rw [neg_one_mul, neg_one_mul, ← neg_div]
    apply div_pos _ (by linarith)
    linarith [le_abs_self (state a b p q Y a (j + 1))]

end GeneralEquality
end CodexPaper1
