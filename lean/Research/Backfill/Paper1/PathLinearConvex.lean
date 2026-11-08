import Research.Backfill.Paper1.PathAndSign
import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset
namespace NarrowPath

lemma z_eq_Zp {x : ℝ} (hx : x ≠ 0) (k : ℕ) (j : ℤ)
    (hj : -1 ≤ j) (hjk : j ≤ (k : ℤ) - 1) (w : ℕ → ℝ) :
    Challenge.z x k w j = ICGGeneral.Zp x k w (j + 1).toNat := by
  have hi : (j + 1).toNat ≤ k := by omega
  have he : ((j + 1).toNat : ℤ) - 1 = j := by omega
  simpa only [he] using PathAndSign.z_pred_eq_Zp hx k w (j + 1).toNat hi

end NarrowPath

theorem check_PathLinear : NarrowSupplement.PathLinear := by
  intro x hx k _hk j hj hjk r s v w
  have hx0 : x ≠ 0 := by linarith
  rw [NarrowPath.z_eq_Zp hx0 k j hj hjk, NarrowPath.z_eq_Zp hx0 k j hj hjk,
    NarrowPath.z_eq_Zp hx0 k j hj hjk]
  exact ICGGeneral.Zp_linear x k r s v w (j + 1).toNat

theorem check_PathConvex : NarrowSupplement.PathConvex := by
  intro x hx k _hk j hj hjk
  have hx0 : x ≠ 0 := by linarith
  let r : ℕ := (j + 1).toNat
  have hr : r ≤ k := by dsimp [r]; omega
  let c : ℕ → ℝ := fun i => ICGGeneral.phiX x (k - i) / x ^ (k - r)
  have hsets : Ico r (k + 1) = Icc r k := by
    ext i
    simp only [mem_Ico, mem_Icc]
    omega
  have hz (w : ℕ → ℝ) : ICGGeneral.Zp x k w r = ∑ i ∈ Icc r k, c i * w i := by
    unfold ICGGeneral.Zp ICGGeneral.Wp
    rw [hsets]
    dsimp only [c]
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i _hi
    dsimp only [c]
    apply div_nonneg _ (pow_nonneg (by linarith) _)
    unfold ICGGeneral.phiX
    split_ifs <;> positivity
  · have h := hz (fun _ => 1)
    simp only [mul_one] at h
    exact h.symm.trans (ICGGeneral.Zp_one hx0 k r hr)
  · intro w
    rw [NarrowPath.z_eq_Zp hx0 k j hj hjk]
    exact hz w

#print axioms check_PathLinear
#print axioms check_PathConvex
end CodexPaper1
