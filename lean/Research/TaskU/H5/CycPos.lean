import Research.TaskU.H5.CycEval

namespace TaskU.H5.Cyc5
open scoped ComplexConjugate

lemma val_complex_conj (v : V) (z : ℂ) : (starRingEnd ℂ) (val v z) = val v ((starRingEnd ℂ) z) := by
  simp [val]

lemma conj_character (j : ZMod 5) : (starRingEnd ℂ) (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,← Circle.coe_inv_eq_conj,AddChar.map_neg_eq_inv]

lemma norm_nonneg (v : V) : 0 ≤ norm v := by
  have h₁ : (starRingEnd ℂ) zeta = zeta^4 := by
    rw [zeta_pow,zeta,conj_character]; rfl
  have h₂ : (starRingEnd ℂ) (zeta^2) = zeta^3 := by
    rw [zeta_pow,zeta_pow,conj_character]; rfl
  have h : (norm v : ℂ) = ↑(‖val v zeta‖^2 * ‖val v (zeta^2)‖^2 : ℝ) := by
    rw [norm_embeddings v zeta zeta_rel,← h₁,← h₂,← val_complex_conj,← val_complex_conj]
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj']
    ring
  have hr : (norm v : ℝ) = ‖val v zeta‖^2 * ‖val v (zeta^2)‖^2 := by
    simpa only [Complex.intCast_re,Complex.ofReal_re] using congrArg Complex.re h
  have hpos : 0 ≤ (norm v : ℝ) := hr ▸ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact_mod_cast hpos

end TaskU.H5.Cyc5
