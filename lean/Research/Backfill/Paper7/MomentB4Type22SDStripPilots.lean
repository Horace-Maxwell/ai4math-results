import Research.Backfill.Paper7.MomentB4Type22SumDifference

/-! SOURCE ONLY. Three complete S-strips, each certified over all nineteen
D values and all ten R values. These are proposed proof bodies, not executed
numeric observations. They retain every original catalogue guard. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open scoped BigOperators Classical

theorem type22_sd_strip_four_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    ((0 < D.val ∧ D.val ≤ 4 ∧ (4-D.val)%2 = 0) ∧
      b4Type22SDAccept 4 D.val R.val) ↔ D = 4 ∧ R = 4 := by
  simp only [b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_sd_strip_four_certificate

theorem type22_sd_strip_five_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    ((0 < D.val ∧ D.val ≤ 5 ∧ (5-D.val)%2 = 0) ∧
      b4Type22SDAccept 5 D.val R.val) ↔ D = 3 ∧ R = 5 := by
  simp only [b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_sd_strip_five_certificate

theorem type22_sd_strip_six_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    ((0 < D.val ∧ D.val ≤ 6 ∧ (6-D.val)%2 = 0) ∧
      b4Type22SDAccept 6 D.val R.val) ↔ D = 2 ∧ R = 2 := by
  simp only [b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_sd_strip_six_certificate

theorem b4_type22_sd_strip_four : b4Type22SDStrip 4 = 1 := by
  change (∑ D : Fin 19, ∑ R : Fin 10,
    if ((0 < D.val ∧ D.val ≤ 4 ∧ (4-D.val)%2 = 0) ∧
      b4Type22SDAccept 4 D.val R.val) then
      min ((4-D.val)/2) R.val+1-(R.val-(4+D.val)/2) else 0) = 1
  simp_rw [type22_sd_strip_four_certificate]
  rw [Finset.sum_eq_single (4 : Fin 19)]
  · rw [Finset.sum_eq_single (4 : Fin 10)]
    · norm_num
    · intro R _ hR
      simp [hR]
    · simp
  · intro D _ hD
    simp [hD]
  · simp
#print axioms Paper7MomentCanonicalNumeric.b4_type22_sd_strip_four

theorem b4_type22_sd_strip_five : b4Type22SDStrip 5 = 1 := by
  change (∑ D : Fin 19, ∑ R : Fin 10,
    if ((0 < D.val ∧ D.val ≤ 5 ∧ (5-D.val)%2 = 0) ∧
      b4Type22SDAccept 5 D.val R.val) then
      min ((5-D.val)/2) R.val+1-(R.val-(5+D.val)/2) else 0) = 1
  simp_rw [type22_sd_strip_five_certificate]
  rw [Finset.sum_eq_single (3 : Fin 19)]
  · rw [Finset.sum_eq_single (5 : Fin 10)]
    · norm_num
    · intro R _ hR
      simp [hR]
    · simp
  · intro D _ hD
    simp [hD]
  · simp
#print axioms Paper7MomentCanonicalNumeric.b4_type22_sd_strip_five

theorem b4_type22_sd_strip_six : b4Type22SDStrip 6 = 3 := by
  change (∑ D : Fin 19, ∑ R : Fin 10,
    if ((0 < D.val ∧ D.val ≤ 6 ∧ (6-D.val)%2 = 0) ∧
      b4Type22SDAccept 6 D.val R.val) then
      min ((6-D.val)/2) R.val+1-(R.val-(6+D.val)/2) else 0) = 3
  simp_rw [type22_sd_strip_six_certificate]
  rw [Finset.sum_eq_single (2 : Fin 19)]
  · rw [Finset.sum_eq_single (2 : Fin 10)]
    · norm_num
    · intro R _ hR
      simp [hR]
    · simp
  · intro D _ hD
    simp [hD]
  · simp
#print axioms Paper7MomentCanonicalNumeric.b4_type22_sd_strip_six

end Paper7MomentCanonicalNumeric
