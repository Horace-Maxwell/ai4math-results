import Research.Backfill.Paper1.PathAndSign
import Research.Backfill.Paper1.ClosedForms

/-!
Proof source for the complete frozen Lemma21. Compilation and acceptance
evidence are recorded separately by check_column_identity.py.
The row potential identity, the q-path/left-transform interchange and the
single signed corner are kept separate. No sign or corner-positivity premise
is added to the frozen statement.
-/

set_option autoImplicit false
noncomputable section

namespace CodexPaper1
open BackfillPaper1 Finset
open Additional

namespace ColumnIdentity

def row (a : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) (u j : ℕ) : ℝ :=
  Challenge.tMulVec a p (Challenge.col Y j) u

def colNorm (a : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  Challenge.l1 a (Challenge.tMulVec a p (Challenge.col Y j))

def coeff (q : ℝ) (j : ℕ) : ℝ :=
  (q - 1) * (1 + Challenge.mu q ((j : ℤ) - 1))

def cell (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u j : ℕ) : ℝ :=
  Challenge.hcell (q - 1) (Challenge.mu q ((j : ℤ) - 1))
    (row a p Y u j) (Challenge.tMulVec a p (Challenge.zetaPath b q Y j) u)

def cellSum (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ u ∈ range (a + 1), cell a b p q Y u j

lemma triple_row (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) :
    Challenge.triple a b p q Y u v = Challenge.tMulVec b q (row a p Y u) v := by
  unfold Challenge.triple row Challenge.tMulVec Challenge.col
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma matrix_norm_rows (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) :
    Challenge.l1Mat a b (Challenge.triple a b p q Y) =
      ∑ u ∈ range (a + 1), Challenge.l1 b (Challenge.tMulVec b q (row a p Y u)) := by
  unfold Challenge.l1Mat Challenge.l1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [triple_row]

lemma Zp_row (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u k : ℕ) :
    ICGGeneral.Zp q b (row a p Y u) k =
      ∑ i ∈ range (a + 1), Challenge.tEntry a p u i * ICGGeneral.Zp q b (Y i) k := by
  unfold row Challenge.tMulVec Challenge.col
  exact ICGGeneral.Zp_sum q b (range (a + 1)) (fun i => Challenge.tEntry a p u i) Y k

lemma Zp_row_eq_zeta {q : ℝ} (hq : q ≠ 0) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (u k : ℕ) (hk : k ≤ b) :
    ICGGeneral.Zp q b (row a p Y u) k =
      Challenge.tMulVec a p (Challenge.zetaPath b q Y ((k : ℤ) - 1)) u := by
  rw [Zp_row]
  unfold Challenge.tMulVec Challenge.zetaPath
  apply Finset.sum_congr rfl
  intro i _
  rw [PathAndSign.z_pred_eq_Zp hq b (Y i) k hk]

lemma coeff_eq {q : ℝ} (hq : q ≠ 0) (j : ℕ) :
    coeff q j = q * ICGGeneral.cc q j := by
  unfold coeff ICGGeneral.cc
  rw [mu_pred_eq_nu]
  field_simp [hq]

lemma row_potential {q : ℝ} (hq : 1 < q) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (u : ℕ) :
    q * Challenge.l1 b (Challenge.tMulVec b q (row a p Y u)) =
      q ^ b * ((∑ j ∈ range b, coeff q j * |row a p Y u j|) +
        q * Challenge.mu q ((b : ℤ) - 1) * |row a p Y u b| +
        ∑ j ∈ range b, cell a b p q Y u j) := by
  have hq0 : 0 < q := by linarith
  have hcoeff : (∑ j ∈ range b, coeff q j * |row a p Y u j|) =
      q * ∑ j ∈ range b, ICGGeneral.cc q j * |row a p Y u j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coeff_eq hq0.ne']
    ring
  have hcells : (∑ j ∈ range b, ICGGeneral.hcell (q - 1) (ICGGeneral.nu q j)
      (row a p Y u j) (ICGGeneral.Zp q b (row a p Y u) (j + 1))) =
      ∑ j ∈ range b, cell a b p q Y u j := by
    apply Finset.sum_congr rfl
    intro j hj
    unfold cell
    rw [mu_pred_eq_nu, Zp_row_eq_zeta hq0.ne' a b p Y u (j + 1)
      (Finset.mem_range.mp hj)]
    have hind : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
    rw [hind]
    rfl
  rw [l1_tMulVec_eq_L1, ICGEqualParity.L1_potential hq, hcells, hcoeff, mu_pred_eq_nu]
  field_simp [hq0.ne']

lemma matrix_potential {q : ℝ} (hq : 1 < q) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) :
    q * Challenge.l1Mat a b (Challenge.triple a b p q Y) =
      q ^ b * ((∑ j ∈ range b, coeff q j * colNorm a p Y j) +
        q * Challenge.mu q ((b : ℤ) - 1) * colNorm a p Y b +
        ∑ j ∈ range b, cellSum a b p q Y j) := by
  have h1 : (∑ u ∈ range (a + 1), ∑ j ∈ range b, coeff q j * |row a p Y u j|) =
      ∑ j ∈ range b, coeff q j * colNorm a p Y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    rfl
  have h2 : (∑ u ∈ range (a + 1),
      q * Challenge.mu q ((b : ℤ) - 1) * |row a p Y u b|) =
      q * Challenge.mu q ((b : ℤ) - 1) * colNorm a p Y b := by
    rw [← Finset.mul_sum]
    rfl
  have h3 : (∑ u ∈ range (a + 1), ∑ j ∈ range b, cell a b p q Y u j) =
      ∑ j ∈ range b, cellSum a b p q Y j := by
    rw [Finset.sum_comm]
    rfl
  rw [matrix_norm_rows, Finset.mul_sum]
  simp_rw [row_potential hq a b p Y]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3]

lemma alternating_budget {q : ℝ} (hq : 2 < q) (b : ℕ) :
    q * Challenge.dNorm b q =
      q ^ b * ((∑ j ∈ range b, coeff q j) + q * Challenge.mu q ((b : ℤ) - 1)) := by
  have hq0 : 0 < q := by linarith
  have hc : (∑ j ∈ range b, coeff q j) = q * ∑ j ∈ range b, ICGGeneral.cc q j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact coeff_eq hq0.ne' j
  rw [dNorm_eq_L1, ICGGeneral.L1_sgnv hq, hc, mu_pred_eq_nu]
  ring

lemma psiCol_eq (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (j : ℕ) :
    Challenge.psiCol a b p q Y j =
      coeff q j * (Challenge.dNorm a p - colNorm a p Y j) - cellSum a b p q Y j := rfl

lemma psi_sum (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) :
    (∑ j ∈ range b, Challenge.psiCol a b p q Y j) =
      Challenge.dNorm a p * (∑ j ∈ range b, coeff q j) -
        (∑ j ∈ range b, coeff q j * colNorm a p Y j) -
        ∑ j ∈ range b, cellSum a b p q Y j := by
  simp only [psiCol_eq, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

lemma norm_deficit {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) :
    q * (Challenge.dNorm a p * Challenge.dNorm b q -
      Challenge.l1Mat a b (Challenge.triple a b p q Y)) =
      q ^ b * ((∑ j ∈ range b, Challenge.psiCol a b p q Y j) +
        q * Challenge.mu q ((b : ℤ) - 1) * Challenge.DeltaC a p (Challenge.col Y b)) := by
  have hn := matrix_potential (show 1 < q by linarith) a b p Y
  have hd := alternating_budget hq b
  rw [psi_sum]
  change q * (Challenge.dNorm a p * Challenge.dNorm b q -
      Challenge.l1Mat a b (Challenge.triple a b p q Y)) =
    q ^ b * (Challenge.dNorm a p * (∑ j ∈ range b, coeff q j) -
      (∑ j ∈ range b, coeff q j * colNorm a p Y j) -
      (∑ j ∈ range b, cellSum a b p q Y j) +
      q * Challenge.mu q ((b : ℤ) - 1) * (Challenge.dNorm a p - colNorm a p Y b))
  linear_combination Challenge.dNorm a p * hd - hn

lemma abs_sub_self (t : ℝ) : |t| - t = 2 * Challenge.negPt t := by
  unfold Challenge.negPt
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, max_eq_right (by linarith)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', max_eq_left (by linarith)]
    ring

lemma negPt_mul {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    Challenge.negPt (c * t) = c * Challenge.negPt t := by
  unfold Challenge.negPt
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (by nlinarith : -(c * t) ≤ 0), max_eq_right (by linarith : -t ≤ 0)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_left (by nlinarith : 0 ≤ -(c * t)), max_eq_left (by linarith : 0 ≤ -t)]
    ring

lemma Gval_corner (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) :
    Challenge.Gval a b p q Y = Challenge.l1Mat a b (Challenge.triple a b p q Y) -
      2 * Challenge.negPt (Challenge.triple a b p q Y a b) := by
  classical
  have hf (u v : ℕ) :
      (if u = a ∧ v = b then Challenge.triple a b p q Y u v else |Challenge.triple a b p q Y u v|) =
      |Challenge.triple a b p q Y u v| -
        (if u = a ∧ v = b then |Challenge.triple a b p q Y u v| -
          Challenge.triple a b p q Y u v else 0) := by
    split_ifs <;> ring
  have hs : (∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
      if u = a ∧ v = b then |Challenge.triple a b p q Y u v| -
        Challenge.triple a b p q Y u v else 0) =
      |Challenge.triple a b p q Y a b| - Challenge.triple a b p q Y a b := by
    simp [ite_and]
  unfold Challenge.Gval Challenge.l1Mat
  simp_rw [hf, Finset.sum_sub_distrib]
  rw [hs, abs_sub_self]

lemma corner_eq {q : ℝ} (hq : q ≠ 0) (a b : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) :
    Challenge.triple a b p q Y a b =
      q ^ b * Challenge.tMulVec a p (Challenge.zetaPath b q Y (-1)) a := by
  rw [triple_row, tMulVec_eq_Tv q b (row a p Y a) b le_rfl, ICGGeneral.Tv_last hq,
    Zp_row_eq_zeta hq a b p Y a 0 (Nat.zero_le _)]
  norm_num only [Int.natCast_zero, zero_sub]

lemma Gval_eq {q : ℝ} (hq : 0 < q) (a b : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) :
    Challenge.Gval a b p q Y = Challenge.l1Mat a b (Challenge.triple a b p q Y) -
      2 * q ^ b * Challenge.negPt (Challenge.tMulVec a p (Challenge.zetaPath b q Y (-1)) a) := by
  rw [Gval_corner, corner_eq hq.ne', negPt_mul (pow_pos hq b).le]
  ring

lemma identity {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ) (Y : ℕ → ℕ → ℝ) :
    q ^ (1 - (b : ℤ)) * (Challenge.Theta a b p q - Challenge.Gval a b p q Y) =
      (∑ j ∈ range b, Challenge.psiCol a b p q Y j) +
        q * Challenge.mu q ((b : ℤ) - 1) *
          (Challenge.DeltaC a p (Challenge.col Y b) - 2 * Challenge.deltaK a p) +
        2 * q * Challenge.negPt (Challenge.tMulVec a p (Challenge.zetaPath b q Y (-1)) a) := by
  have hq0 : 0 < q := by linarith
  have hQ : q ^ b ≠ 0 := (pow_pos hq0 b).ne'
  have hn := norm_deficit hq a b p Y
  have hd := ClosedForms.weighted_mu_eq_deltaK hq b
  let R := (∑ j ∈ range b, Challenge.psiCol a b p q Y j) +
    q * Challenge.mu q ((b : ℤ) - 1) *
      (Challenge.DeltaC a p (Challenge.col Y b) - 2 * Challenge.deltaK a p) +
    2 * q * Challenge.negPt (Challenge.tMulVec a p (Challenge.zetaPath b q Y (-1)) a)
  have htotal : q * (Challenge.Theta a b p q - Challenge.Gval a b p q Y) = q ^ b * R := by
    dsimp only [R]
    rw [Challenge.Theta, Gval_eq hq0, ← hd]
    linear_combination hn
  change q ^ (1 - (b : ℤ)) * (Challenge.Theta a b p q - Challenge.Gval a b p q Y) = R
  rw [zpow_sub₀ hq0.ne', zpow_one, zpow_natCast]
  calc
    q / q ^ b * (Challenge.Theta a b p q - Challenge.Gval a b p q Y) =
        (q * (Challenge.Theta a b p q - Challenge.Gval a b p q Y)) / q ^ b := by ring
    _ = (q ^ b * R) / q ^ b := by rw [htotal]
    _ = R := mul_div_cancel_left₀ _ hQ

end ColumnIdentity

theorem check_Lemma21 : Challenge.Lemma21 := by
  intro a b _ha _hb _hab p q hregions Y _hY
  have hq : 2 < q := by
    rcases hregions with h | h
    · rcases h with ⟨_, hq⟩
      linarith
    · rcases h with ⟨_, hq⟩
      linarith
  exact ColumnIdentity.identity hq a b p Y

#print axioms check_Lemma21

end CodexPaper1
