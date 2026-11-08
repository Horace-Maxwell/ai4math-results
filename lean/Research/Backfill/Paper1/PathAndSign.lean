import Research.Backfill.Paper1.Additional

/-!
Exact bridges for the complete frozen Paper 1 targets Lemma7, Lemma8,
Theorem12 and Remark13. The imported Additional module supplies the verified
coordinate and path interfaces. This file does not change any frozen statement.
-/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset
open Additional

namespace PathAndSign

/-- Uniform path conversion, including the bottom endpoint i = 0 (j = -1)
and the top endpoint i = k (j = k-1). -/
lemma z_pred_eq_Zp {x : ℝ} (hx : x ≠ 0) (k : ℕ) (w : ℕ → ℝ)
    (i : ℕ) (hi : i ≤ k) :
    Challenge.z x k w ((i : ℤ) - 1) = ICGGeneral.Zp x k w i := by
  have hidx : ((k : ℤ) - 1 - ((i : ℤ) - 1)).toNat = k - i := by omega
  rw [Challenge.z, hidx, zRev_eq_Zp hx k w (k - i) (by omega),
    show k - (k - i) = i by omega]

lemma cc_sum_eq (x : ℝ) (k : ℕ) :
    (∑ j ∈ range k, Challenge.cc x j) = ∑ j ∈ range k, ICGGeneral.cc x j := by
  apply Finset.sum_congr rfl
  intro j _
  exact cc_eq x j

lemma slack_eq_NA {x : ℝ} (hx : x ≠ 0) (k : ℕ) (y : ℕ → ℝ) :
    ICGGeneral.slack x k y =
      ∑ j ∈ Challenge.NA k y, 2 * Challenge.mu x j * |Challenge.z x k y j| := by
  rw [slack_eq_two_sigma hx k y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact entry bridge on the finite matrix rectangle. -/
lemma triple_eq_Mentry (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ)
    (u v : ℕ) (hu : u ≤ a) (hv : v ≤ b) :
    Challenge.triple a b p q Y u v = ICGGeneral.Mentry p q a b Y u v := by
  unfold Challenge.triple ICGGeneral.Mentry
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [tEntry_eq_Tent p a u i hu (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
    tEntry_eq_Tent q b v j hv (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

lemma l1Mat_triple_eq_L1mat (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    Challenge.l1Mat a b (Challenge.triple a b p q Y) = ICGGeneral.L1mat p q a b Y := by
  unfold Challenge.l1Mat ICGGeneral.L1mat
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [triple_eq_Mentry p q a b Y u v
    (Nat.le_of_lt_succ (Finset.mem_range.mp hu))
    (Nat.le_of_lt_succ (Finset.mem_range.mp hv))]

/-- Both checkerboard signs attain the full product, not merely the upper bound. -/
lemma checkerboard_value (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ)
    (hY : Challenge.IsPmCheckerboard a b Y) :
    ICGGeneral.L1mat p q a b Y =
      ICGGeneral.L1 p a ICGGeneral.sgnv * ICGGeneral.L1 q b ICGGeneral.sgnv := by
  rcases hY with hY | hY
  · exact ICGGeneral.L1mat_prod p q a b hY
  · have hprod : ∀ i ≤ a, ∀ j ≤ b,
        Y i j = (-ICGGeneral.sgnv i) * ICGGeneral.sgnv j := by
      intro i hi j hj
      rw [hY i hi j hj]
      change -(ICGGeneral.sgnv i * ICGGeneral.sgnv j) =
        (-ICGGeneral.sgnv i) * ICGGeneral.sgnv j
      ring
    rw [ICGGeneral.L1mat_prod p q a b hprod, ICGGeneral.L1_neg_sgnv]

lemma triple_transpose (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) :
    Challenge.triple a b p q Y u v =
      Challenge.triple b a q p (fun j i => Y i j) v u := by
  unfold Challenge.triple
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma l1Mat_triple_transpose (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    Challenge.l1Mat a b (Challenge.triple a b p q Y) =
      Challenge.l1Mat b a (Challenge.triple b a q p (fun j i => Y i j)) := by
  unfold Challenge.l1Mat
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  rw [triple_transpose]

lemma checkerboard_transpose_iff (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    Challenge.IsPmCheckerboard b a (fun j i => Y i j) ↔
      Challenge.IsPmCheckerboard a b Y := by
  constructor
  · rintro (h | h)
    · left
      intro i hi j hj
      simpa only [mul_comm] using h j hj i hi
    · right
      intro i hi j hj
      simpa only [mul_comm] using h j hj i hi
  · rintro (h | h)
    · left
      intro j hj i hi
      simpa only [mul_comm] using h i hi j hj
    · right
      intro j hj i hi
      simpa only [mul_comm] using h i hi j hj

end PathAndSign
open PathAndSign

theorem check_Lemma7 : Challenge.Lemma7 := by
  intro x hx k _hk w
  have hx0 : 0 < x := by linarith
  rw [l1_tMulVec_eq_L1, ICGGeneral.L1_path hx0]
  congr 1
  have hz0 : Challenge.z x k w (-1) = ICGGeneral.Zp x k w 0 := by
    simpa using z_pred_eq_Zp hx0.ne' k w 0 (Nat.zero_le k)
  rw [hz0]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  rw [z_pred_eq_Zp hx0.ne' k w j hjk.le, z_nat_eq_Zp hx0.ne' k w j hjk]

theorem check_Lemma8 : Challenge.Lemma8 := by
  intro x hx k _hk y hy
  have hx0 : 0 < x := by linarith
  have hyG : ICGGeneral.IsSign k y := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [z_pred_eq_Zp hx0.ne' k y i hi]
    have hsign := ICGGeneral.Zp_sign hx.le hyG i hi
    have hpos : 0 < (x - 2) / x := div_pos (by linarith) hx0
    refine ⟨lt_of_lt_of_le hpos hsign, ?_, ?_⟩
    · rw [ICGGeneral.Zp_abs_eq hx.le hyG hi]
      exact hsign
    · exact ICGGeneral.Zp_abs_le (by linarith) (ICGGeneral.isSign_abs_le hyG) i hi
  · rw [l1_tMulVec_eq_L1, cc_sum_eq, mu_pred_eq_nu,
      ← slack_eq_NA hx0.ne' k y, ICGGeneral.L1_sign hx hyG]
    field_simp [hx0.ne']
  · rw [l1_tMulVec_eq_L1, dNorm_eq_L1]
    exact ICGGeneral.L1_le_sgnv hx hyG
  · rw [l1_tMulVec_eq_L1, dNorm_eq_L1]
    constructor
    · intro h
      exact ICGGeneral.L1_eq_sgnv hx hyG h
    · rintro (h | h)
      · exact ICGGeneral.L1_congr x k h
      · exact (ICGGeneral.L1_congr x k h).trans (ICGGeneral.L1_neg_sgnv x k)
  · rw [dNorm_eq_L1, cc_sum_eq, mu_pred_eq_nu]
    exact ICGGeneral.L1_sgnv hx k
  · rw [tMulVec_eq_Tv x k Challenge.sAlt k le_rfl]
    exact ICGGeneral.Tv_sgnv_last_pos hx k

theorem check_Theorem12 : Challenge.Theorem12 := by
  intro p q hp hq a b _ha _hb Y hY
  have hYG : ∀ i ≤ a, ICGGeneral.IsSign b (Y i) := hY
  rw [l1Mat_triple_eq_L1mat, dNorm_eq_L1, dNorm_eq_L1]
  refine ⟨ICGGeneral.thm5_le hp hq hYG, ?_⟩
  constructor
  · intro h
    exact ICGGeneral.thm5_eq hp hq hYG h
  · exact checkerboard_value p q a b Y

theorem check_Remark13 : Challenge.Remark13 := by
  intro p q hmin hmax a b ha hb Y hY
  have hp3 : 3 ≤ p := le_trans hmin (min_le_left p q)
  have hq3 : 3 ≤ q := le_trans hmin (min_le_right p q)
  rcases le_max_iff.mp hmax with hp5 | hq5
  · exact check_Theorem12 p q hp5 hq3 a b ha hb Y hY
  · have hYT : Challenge.IsSignMat b a (fun j i => Y i j) := by
      intro j hj i hi
      exact hY i hi j hj
    have ht := check_Theorem12 q p hq5 hp3 b a hb ha (fun j i => Y i j) hYT
    simpa only [← l1Mat_triple_transpose p q a b Y,
      mul_comm (Challenge.dNorm b q) (Challenge.dNorm a p),
      checkerboard_transpose_iff a b Y] using ht

#print axioms check_Lemma7
#print axioms check_Lemma8
#print axioms check_Theorem12
#print axioms check_Remark13
end CodexPaper1
