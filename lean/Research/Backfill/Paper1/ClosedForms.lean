import Research.Backfill.Paper1.Additional

/-!
# Paper 1, Remark 9: all five closed-form identities

Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.

The complete frozen Remark9 is proved below, including k = 0.
The proof uses Additional's three exact transform/potential bridges.
Compilation, standard proof dependencies, individual kernel checks and fresh
Additional/ClosedForms/Check replay are recorded by check_closedforms.py;
this single target does not claim complete Paper 1 acceptance.
-/

set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset

namespace ClosedForms

def altSum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range k, (-1) ^ (k - i) * x ^ i

def weightedSum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range k, (-1) ^ (k - i) * ((i : ℝ) + 1) * x ^ i

lemma altSum_succ (k : ℕ) (x : ℝ) :
    altSum (k + 1) x = x * altSum k x + (-1) ^ (k + 1) := by
  unfold altSum
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
  ring

lemma weightedSum_succ (k : ℕ) (x : ℝ) :
    weightedSum (k + 1) x = x * weightedSum k x + altSum (k + 1) x := by
  calc
    weightedSum (k + 1) x =
        (∑ i ∈ range (k + 1), (-1) ^ (k + 1 - i) * (i : ℝ) * x ^ i) +
          altSum (k + 1) x := by
      unfold weightedSum altSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = x * weightedSum k x + altSum (k + 1) x := by
      congr 1
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      unfold weightedSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
      push_cast
      ring

lemma deltaK_zero {x : ℝ} (hx : 2 < x) : Challenge.deltaK 0 x = 1 := by
  have hx1 : x + 1 ≠ 0 := by linarith
  unfold Challenge.deltaK
  norm_num only [pow_zero]
  field_simp [hx1]
  ring

lemma deltaK_succ {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.deltaK (k + 1) x = x * Challenge.deltaK k x + 2 * (-1) ^ (k + 1) := by
  have hx1 : x + 1 ≠ 0 := by linarith
  unfold Challenge.deltaK
  simp only [pow_succ]
  field_simp [hx1]
  ring

lemma deltaK_eq_polynomial {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.deltaK k x = x ^ k + 2 * altSum k x := by
  induction k with
  | zero => simpa [altSum] using deltaK_zero hx
  | succ k ih =>
    rw [deltaK_succ hx, ih, altSum_succ]
    simp only [pow_succ]
    ring

lemma weighted_nu_eq_deltaK {x : ℝ} (hx : 2 < x) (k : ℕ) :
    x ^ k * ICGGeneral.nu x k = Challenge.deltaK k x := by
  have hx0 : 0 < x := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hxk : x ^ k ≠ 0 := pow_ne_zero k hx0.ne'
  have h := ICGEqualParity.nu_sub_L hx0 k
  rw [div_pow] at h
  unfold Challenge.deltaK
  apply (eq_div_iff hx1).2
  field_simp [hxk, hx1] at h
  nlinarith only [h]

lemma weighted_mu_eq_deltaK {x : ℝ} (hx : 2 < x) (k : ℕ) :
    x ^ k * Challenge.mu x ((k : ℤ) - 1) = Challenge.deltaK k x := by
  rw [Additional.mu_pred_eq_nu]
  exact weighted_nu_eq_deltaK hx k

lemma last_alt_eq_deltaK {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.tMulVec k x Challenge.sAlt k = Challenge.deltaK k x := by
  have hx0 : 0 < x := by linarith
  rw [Additional.tMulVec_eq_Tv x k Challenge.sAlt k le_rfl]
  change ICGGeneral.Tv x k ICGGeneral.sgnv k = Challenge.deltaK k x
  rw [ICGGeneral.Tv_last hx0.ne', ICGEqualParity.Zp_sgnv_zero hx]
  exact weighted_nu_eq_deltaK hx k

lemma dNorm_succ {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.dNorm (k + 1) x =
      x * Challenge.dNorm k x + 2 * Challenge.deltaK (k + 1) x := by
  have hx0 : x ≠ 0 := by linarith
  rw [Additional.dNorm_eq_L1 x (k + 1), Additional.dNorm_eq_L1 x k,
    ICGGeneral.L1_sgnv hx (k + 1), ICGGeneral.L1_sgnv hx k,
    ← weighted_nu_eq_deltaK hx (k + 1), Finset.sum_range_succ]
  simp only [pow_succ, ICGGeneral.cc, ICGGeneral.nu_succ]
  field_simp [hx0]
  ring

lemma dNorm_zero {x : ℝ} (hx : 2 < x) : Challenge.dNorm 0 x = 1 := by
  rw [Additional.dNorm_eq_L1 x 0, ICGGeneral.L1_sgnv hx 0]
  norm_num [ICGGeneral.nu_zero]

lemma dClosed_eq (k : ℕ) (x : ℝ) :
    Challenge.dClosed k x = (2 * (k : ℝ) + 1) * x ^ k + 4 * weightedSum k x := by
  simp [Challenge.dClosed, weightedSum]

lemma dClosed_succ {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.dClosed (k + 1) x =
      x * Challenge.dClosed k x + 2 * Challenge.deltaK (k + 1) x := by
  rw [dClosed_eq (k + 1) x, dClosed_eq k x, weightedSum_succ,
    deltaK_eq_polynomial hx (k + 1)]
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

lemma dNorm_eq_dClosed {x : ℝ} (hx : 2 < x) (k : ℕ) :
    Challenge.dNorm k x = Challenge.dClosed k x := by
  induction k with
  | zero =>
    rw [dNorm_zero hx]
    norm_num [Challenge.dClosed]
  | succ k ih =>
    rw [dNorm_succ hx k, dClosed_succ hx k, ih]

end ClosedForms

theorem check_Remark9 : Challenge.Remark9 := by
  intro x hx k
  exact ⟨ClosedForms.weighted_mu_eq_deltaK hx k,
    ClosedForms.last_alt_eq_deltaK hx k,
    ClosedForms.dNorm_succ hx k,
    ClosedForms.dNorm_eq_dClosed hx k,
    ClosedForms.deltaK_eq_polynomial hx k⟩

#print axioms check_Remark9

end CodexPaper1
