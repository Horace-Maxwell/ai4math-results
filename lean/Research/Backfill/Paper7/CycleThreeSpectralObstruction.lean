import Research.Backfill.Paper7.CycleThreePolynomial
import Research.Backfill.Paper7.SpectrumGraphBasics

/-! A structural three-cycle obstruction valid for every choice of pendant
parameters: outside 0 and ±1, opposite real numbers cannot both be eigenvalues. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem triangle_eval_zero_of_spec (p q : Fin 3 → ℕ) (x : ℝ)
    (hx : x ∈ spec (SG 3 p q)) (hx0 : x ≠ 0) (hx1 : x ^ 2 - 1 ≠ 0) :
    (trianglePolynomial p q).eval₂ (Int.castRingHom ℝ) x = 0 := by
  let ev : Polynomial ℤ →+* ℝ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) x
  have hevX : ev X = x := Polynomial.eval₂_X _ _
  have hroot : Polynomial.IsRoot ((SG 3 p q).adjMatrix ℝ).charpoly x :=
    Polynomial.isRoot_of_mem_roots hx
  rw [← Paper7Spectrum.graphPhi_map (SG 3 p q) ℝ] at hroot
  have hphi : ev (graphPhi (SG 3 p q)) = 0 := by
    change (graphPhi (SG 3 p q)).eval₂ (Int.castRingHom ℝ) x = 0
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hroot
  have hid := congrArg ev (Paper7Cleared.cleared_identity 3 p q (by omega))
  have hzero : (x ^ totalP 3 p * (x ^ 2 - 1) ^ totalQ 3 q) *
      ev (clearedF 3 p q) = 0 := by
    simpa only [map_mul, map_pow, map_sub, map_one, hevX, hphi, mul_zero] using hid
  have hden : x ^ totalP 3 p * (x ^ 2 - 1) ^ totalQ 3 q ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hx1)
  have hF := (mul_eq_zero.mp hzero).resolve_left hden
  rw [triangle_clearedF] at hF
  exact hF
#print axioms Paper7CycleThree.triangle_eval_zero_of_spec

theorem triangle_no_opposite_spectrum (p q : Fin 3 → ℕ) (x : ℝ)
    (hx0 : x ≠ 0) (hx1 : x ^ 2 - 1 ≠ 0) :
    ¬ (x ∈ spec (SG 3 p q) ∧ -x ∈ spec (SG 3 p q)) := by
  rintro ⟨hx, hnx⟩
  have hpx := triangle_eval_zero_of_spec p q x hx hx0 hx1
  have hnx0 : -x ≠ 0 := neg_ne_zero.mpr hx0
  have hnx1 : (-x) ^ 2 - 1 ≠ 0 := by simpa only [neg_sq] using hx1
  have hpnx := triangle_eval_zero_of_spec p q (-x) hnx hnx0 hnx1
  have hdiff := triangle_eval_neg_sub (Int.castRingHom ℝ) p q x
  rw [hpx, hpnx, sub_self] at hdiff
  have hnonzero : -4 * x ^ 3 * (x ^ 2 - 1) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx0)) (pow_ne_zero _ hx1)
  exact hnonzero hdiff.symm
#print axioms Paper7CycleThree.triangle_no_opposite_spectrum

end Paper7CycleThree
