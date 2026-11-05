import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Uncompiled analytic exclusion of four original spectral catalogue pairs.
The full original catalogue is untouched.  Q=0 and Q=1 are retained in a
separate bound; Q<=18 is derived from the real original budget below. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6ExcludedFeatureCatalog : Finset (ℤ × ℤ) :=
  {(9,72), (16,240), (25,600), (36,1260)}
#print axioms Paper7MomentCounts.b6ExcludedFeatureCatalog

def b6ExcludedTheta : Finset ℤ := {72,240,600,1260}
#print axioms Paper7MomentCounts.b6ExcludedTheta

/-- The actual lower load constraint supplies the Z bound in each Q branch. -/
theorem b6_feature_quadratic_upper (Z Q : ℕ) (R S : ℤ) (hQ : Q ≤ 18)
    (hR : R ≤ (Z : ℤ)^2)
    (hload : (6 + (Z : ℤ) + (Q : ℤ)) - max (Q : ℤ) 2 ≤ S) :
    12 + 3 * (Z : ℤ) + 2 * (Q : ℤ) + R ≤
      if Q ≤ 1 then (S-4)^2 + 3*(S-4) + 14
      else (S-6)^2 + 3*(S-6) + 48 := by
  have hZ0 : (0 : ℤ) ≤ Z := Int.natCast_nonneg Z
  have hQ0 : (0 : ℤ) ≤ Q := Int.natCast_nonneg Q
  have hQ18 : (Q : ℤ) ≤ 18 := by exact_mod_cast hQ
  by_cases hsmall : Q ≤ 1
  · rw [ite_eq_left hsmall]
    have hQ1 : (Q : ℤ) ≤ 1 := by exact_mod_cast hsmall
    have hm : max (Q : ℤ) 2 = 2 := max_eq_right (by omega)
    rw [hm] at hload
    have hZ : (Z : ℤ) ≤ S-4 := by omega
    have hS0 : 0 ≤ S-4 := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hZ) (add_nonneg hS0 hZ0)
    nlinarith only [hR, hQ1, hZ, hp]
  · rw [ite_eq_right hsmall]
    have hQ2 : (2 : ℤ) ≤ Q := by omega
    have hm : max (Q : ℤ) 2 = Q := max_eq_left hQ2
    rw [hm] at hload
    have hZ : (Z : ℤ) ≤ S-6 := by omega
    have hS0 : 0 ≤ S-6 := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hZ) (add_nonneg hS0 hZ0)
    nlinarith only [hR, hQ18, hZ, hp]
#print axioms Paper7MomentCounts.b6_feature_quadratic_upper

theorem b6_excluded_feature_impossible (Z Q : ℕ) (R : ℤ) (sm : ℤ × ℤ)
    (hQ : Q ≤ 18) (hR : R ≤ (Z : ℤ)^2)
    (hload : (6 + (Z : ℤ) + (Q : ℤ)) - max (Q : ℤ) 2 ≤ sm.1)
    (htheta : 12 + 3 * (Z : ℤ) + 2 * (Q : ℤ) + R = sm.2) :
    sm ∉ b6ExcludedFeatureCatalog := by
  intro hsm
  have hu := b6_feature_quadratic_upper Z Q R sm.1 hQ hR hload
  simp only [b6ExcludedFeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl <;>
    (by_cases hsmall : Q ≤ 1 <;> norm_num [hsmall] at hu <;> norm_num at htheta <;> omega)
#print axioms Paper7MomentCounts.b6_excluded_feature_impossible

/-- Exact original PQ statistics and budget instantiate the scalar exclusion. -/
theorem b6_budget_feature_not_excluded (x : PQ 6) (hx : Budget 6 42 x)
    (sm : ℤ × ℤ) (htheta : sm.2 = theta x)
    (hload : (6 + (weight x : ℤ)) - max (qSum x : ℤ) 2 ≤ sm.1) :
    sm ∉ b6ExcludedFeatureCatalog := by
  let v := pqToZQ x
  have hback : zqToPQ v = x := (pqEquivZQ 6).left_inv x
  have hw := zq_weight 6 v
  have hq := zq_qSum 6 v
  have ht := b6_zq_theta v
  rw [hback] at hw hq ht
  have hQ : (∑ i, v.val.2 i) ≤ 18 := by
    have h := (budget_sum_bounds 6 42 x hx).2
    simpa only [hq] using h
  have hR : (∑ i, (v.val.1 i : ℤ)^2) ≤ ((∑ i, v.val.1 i : ℕ) : ℤ)^2 := by
    simpa only [Nat.cast_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin 6)))
        (f := fun i => (v.val.1 i : ℤ)) (fun i _ => Int.natCast_nonneg (v.val.1 i)))
  have hload' : (6 + ((∑ i, v.val.1 i : ℕ) : ℤ) + ((∑ i, v.val.2 i : ℕ) : ℤ)) -
      max ((∑ i, v.val.2 i : ℕ) : ℤ) 2 ≤ sm.1 := by
    rw [hw, hq, Nat.cast_add] at hload
    simpa only [add_assoc] using hload
  exact b6_excluded_feature_impossible (∑ i, v.val.1 i) (∑ i, v.val.2 i)
    (∑ i, (v.val.1 i : ℤ)^2) sm hQ hR hload' (ht.symm.trans htheta.symm)
#print axioms Paper7MomentCounts.b6_budget_feature_not_excluded

/-- Each of these four theta values has only its displayed original catalogue pair. -/
theorem b6FeatureCatalog_excludedTheta_iff (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    sm.2 ∈ b6ExcludedTheta ↔ sm ∈ b6ExcludedFeatureCatalog := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    norm_num [b6ExcludedTheta, b6ExcludedFeatureCatalog]
#print axioms Paper7MomentCounts.b6FeatureCatalog_excludedTheta_iff

end Paper7MomentCounts
