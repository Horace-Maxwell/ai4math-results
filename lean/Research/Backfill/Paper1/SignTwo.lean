import Research.Backfill.Paper1.PathAndSign
import Research.Backfill.Paper1.ClosedForms
import Research.ICGEqualParityBGraph

/-!
Exact bridges for the complete frozen Paper 1 Theorem25.
Compilation and acceptance status are recorded separately by check_signtwo.py.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.

The finite transform, signed-corner correction, scalar bound and two extremal
matrices are bridged explicitly to the previously proved ICGEqualParityB.thmB'.
No graph-energy theorem or additional claim is introduced here.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral

namespace SignTwo

lemma signed_last_sum {q : ℝ} (hq : 0 < q) (b : ℕ) (w : ℕ → ℝ) :
    (∑ v ∈ range (b + 1), if v = b then Tv q b w v else |Tv q b w v|) =
      L1 q b w - 2 * q ^ b * max 0 (-Zp q b w 0) := by
  unfold L1
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hrest :
      (∑ v ∈ range b, if v = b then Tv q b w v else |Tv q b w v|) =
        ∑ v ∈ range b, |Tv q b w v| := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [ite_eq_right (Nat.ne_of_lt (Finset.mem_range.mp hv))]
  rw [hrest, ite_eq_left rfl]
  simp only [Tv_last hq.ne']
  rw [abs_mul, abs_of_pos (pow_pos hq b)]
  by_cases hz : 0 ≤ Zp q b w 0
  · rw [abs_of_nonneg hz, max_eq_left (neg_nonpos.mpr hz)]
    ring
  · have hz' : Zp q b w 0 ≤ 0 := le_of_not_ge hz
    rw [abs_of_nonpos hz', max_eq_right (neg_nonneg.mpr hz')]
    ring

lemma Gval_eq_Gfun {q : ℝ} (hq : 0 < q) (p : ℝ) (b : ℕ)
    (Y : ℕ → ℕ → ℝ) : Challenge.Gval 2 b p q Y = ICGEqualParityB.Gfun p q b Y := by
  have hrow : ∀ u : ℕ, u < 2 → ∀ w : ℕ → ℝ,
      (∀ v, Mentry p q 2 b Y u v = Tv q b w v) →
      (∑ v ∈ range (b + 1),
        if u = 2 ∧ v = b then Challenge.triple 2 b p q Y u v
        else |Challenge.triple 2 b p q Y u v|) = L1 q b w := by
    intro u hu w hw
    unfold L1
    apply Finset.sum_congr rfl
    intro v hv
    rw [ite_eq_right (by omega),
      PathAndSign.triple_eq_Mentry p q 2 b Y u v hu.le
        (Nat.le_of_lt_succ (Finset.mem_range.mp hv)), hw]
  have hrow2 :
      (∑ v ∈ range (b + 1),
        if (2 : ℕ) = 2 ∧ v = b then Challenge.triple 2 b p q Y 2 v
        else |Challenge.triple 2 b p q Y 2 v|) =
      L1 q b (ICGEqualParityB.rw2 p Y) -
        2 * q ^ b * max 0 (-Zp q b (ICGEqualParityB.rw2 p Y) 0) := by
    rw [← signed_last_sum hq b (ICGEqualParityB.rw2 p Y)]
    apply Finset.sum_congr rfl
    intro v hv
    simp [PathAndSign.triple_eq_Mentry p q 2 b Y 2 v le_rfl
      (Nat.le_of_lt_succ (Finset.mem_range.mp hv)),
      (ICGEqualParityB.Mentry_rows2 p q b Y v).2.2]
  unfold Challenge.Gval
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hrow 0 (by norm_num) (ICGEqualParityB.rw0 p Y)
      (fun v => (ICGEqualParityB.Mentry_rows2 p q b Y v).1),
    hrow 1 (by norm_num) (ICGEqualParityB.rw1 p Y)
      (fun v => (ICGEqualParityB.Mentry_rows2 p q b Y v).2.1), hrow2]
  unfold ICGEqualParityB.Gfun
  ring

lemma dNorm_two {p : ℝ} (hp : 2 < p) :
    Challenge.dNorm 2 p = ICGEqualParityB.Dp (p - 1) := by
  rw [ClosedForms.dNorm_eq_dClosed hp]
  norm_num [Challenge.dClosed, Finset.sum_range_succ, ICGEqualParityB.Dp]
  ring

lemma deltaK_two {p : ℝ} (hp : 2 < p) :
    Challenge.deltaK 2 p = (p - 1) ^ 2 + 1 := by
  rw [ClosedForms.deltaK_eq_polynomial hp]
  norm_num [ClosedForms.altSum, Finset.sum_range_succ]
  ring

lemma Theta_eq_Theta {p q : ℝ} (hp : 2 < p) (hq : 2 < q) (b : ℕ) :
    Challenge.Theta 2 b p q = ICGEqualParityB.Theta p q b := by
  have hlast : Tv q b sgnv b = Challenge.deltaK b q := by
    have h := ClosedForms.last_alt_eq_deltaK hq b
    rw [Additional.tMulVec_eq_Tv q b Challenge.sAlt b le_rfl] at h
    exact h
  unfold Challenge.Theta ICGEqualParityB.Theta
  rw [dNorm_two hp, Additional.dNorm_eq_L1 q b, deltaK_two hp, ← hlast]

lemma Yminus_eq_Ym : Challenge.Yminus = ICGEqualParityB.Ym := rfl

lemma Yplus_eq_Yp {b : ℕ} (hb : Even b) :
    Challenge.Yplus 2 b = ICGEqualParityB.Yp b := by
  funext i j
  change sgnv i * sgnv j - (if i = 2 ∧ j = b then 2 else 0) =
    (if i = 2 ∧ j = b then -1 else sgnv i * sgnv j)
  by_cases h : i = 2 ∧ j = b
  · rcases h with ⟨rfl, rfl⟩
    norm_num [ICGEqualParityB.sgnv_two', ICGEqualParityB.sgnv_of_even hb]
  · simp only [ite_eq_right h, sub_zero]

end SignTwo

theorem check_Theorem25 : Challenge.Theorem25 := by
  intro b hb2 hb p q hpq Y hY hcorner
  have hp : 2 < p := by
    rcases hpq with h | h
    · linarith [h.1]
    · rw [h.1]
      norm_num
  have hq : 2 < q := by
    rcases hpq with h | h <;> linarith [h.2]
  have h := ICGEqualParityB.thmB'
    (show ICGEqualParityB.ParamB p q from hpq) hb hb2
    (show ICGEqualParityB.SignMat b Y from hY) hcorner
  simp only [← SignTwo.Gval_eq_Gfun (show 0 < q by linarith) p b Y,
    ← SignTwo.Theta_eq_Theta hp hq b] at h
  simpa only [Challenge.MatEq, SignTwo.Yminus_eq_Ym, SignTwo.Yplus_eq_Yp hb] using h

#print axioms check_Theorem25
end CodexPaper1
