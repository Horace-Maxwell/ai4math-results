import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Uncompiled analytic candidate.  The original budget and theta=1272 force
one coordinate z=34, all other z=0, and Q=1.  No catalogue support table or
numerical total is assumed.  Root suggested isolating the last catalogue
entry; this source uses the author's shorter concentration argument. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

/-- A complete concentration argument for all six ordered nonnegative coordinates. -/
theorem b6_top_moment_shape (z : Fin 6 → ℕ) (Q : ℕ)
    (hbudget : (∑ i, z i) + Q ≤ 36)
    (htheta : 12 + 3 * ((∑ i, z i : ℕ) : ℤ) + 2 * (Q : ℤ) +
      ∑ i, (z i : ℤ)^2 = 1272) :
    Q = 1 ∧ ∃ i : Fin 6, z i = 34 ∧ ∀ j, j ≠ i → z j = 0 := by
  have hbudgetZ : ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ) ≤ 36 := by
    exact_mod_cast hbudget
  have hQ0 : (0 : ℤ) ≤ Q := Int.natCast_nonneg Q
  have hZ36 : ((∑ i, z i : ℕ) : ℤ) ≤ 36 := by omega
  have hRlow : (1152 : ℤ) ≤ ∑ i, (z i : ℤ)^2 := by omega
  have hex : ∃ i : Fin 6, 32 ≤ z i := by
    by_contra h
    have hall : ∀ i : Fin 6, z i ≤ 31 := by
      intro i
      by_contra hi
      exact h ⟨i, by omega⟩
    have hpoint (i : Fin 6) : (z i : ℤ)^2 ≤ 31 * (z i : ℤ) := by
      have hi : (z i : ℤ) ≤ 31 := by exact_mod_cast hall i
      have hp := mul_nonneg (Int.natCast_nonneg (z i)) (sub_nonneg.mpr hi)
      nlinarith only [hp]
    have hu := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 6))) => hpoint i)
    have hu' : (∑ i, (z i : ℤ)^2) ≤ 31 * ((∑ i, z i : ℕ) : ℤ) := by
      simpa only [Finset.mul_sum, Nat.cast_sum] using hu
    omega
  obtain ⟨i, hi32⟩ := hex
  let r : ℕ := ∑ j ∈ Finset.univ.erase i, z j
  let U : ℤ := ∑ j ∈ Finset.univ.erase i, (z j : ℤ)^2
  have hsplitN : r + z i = ∑ j, z j := by
    exact Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hsplitZ : (r : ℤ) + (z i : ℤ) = ((∑ j, z j : ℕ) : ℤ) := by
    exact_mod_cast hsplitN
  have hsplitR : U + (z i : ℤ)^2 = ∑ j, (z j : ℤ)^2 := by
    exact Finset.sum_erase_add Finset.univ (fun j => (z j : ℤ)^2) (Finset.mem_univ i)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun j _ => sq_nonneg (z j : ℤ))
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hm0 : (0 : ℤ) ≤ z i := Int.natCast_nonneg _
  have hm32 : (32 : ℤ) ≤ z i := by exact_mod_cast hi32
  have hr4 : (r : ℤ) ≤ 4 := by omega
  have hUsq : U ≤ (r : ℤ)^2 := by
    simpa only [r, U, Nat.cast_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ.erase i)
        (f := fun j => (z j : ℤ)) (fun j _ => Int.natCast_nonneg (z j)))
  have hm34 : (34 : ℤ) ≤ z i := by
    by_contra h
    have hm33 : (z i : ℤ) ≤ 33 := by omega
    have hpm := mul_nonneg (sub_nonneg.mpr hm33)
      (add_nonneg (show (0 : ℤ) ≤ 33 by norm_num) hm0)
    have hpr := mul_nonneg (sub_nonneg.mpr hr4)
      (add_nonneg (show (0 : ℤ) ≤ 4 by norm_num) hr0)
    nlinarith only [hRlow, hsplitR, hUsq, hpm, hpr]
  have hmle : (z i : ℤ) ≤ 34 := by
    by_contra h
    have hm35 : (35 : ℤ) ≤ z i := by omega
    have hpm := mul_nonneg (sub_nonneg.mpr hm35)
      (add_nonneg hm0 (show (0 : ℤ) ≤ 35 by norm_num))
    nlinarith only [htheta, hsplitZ, hsplitR, hU0, hr0, hQ0, hm35, hpm]
  have hm : (z i : ℤ) = 34 := by omega
  have hsmall : 3 * (r : ℤ) + 2 * (Q : ℤ) + U = 2 := by
    nlinarith only [htheta, hsplitZ, hsplitR, hm]
  have hrzero : r = 0 := by
    have : (r : ℤ) = 0 := by omega
    exact_mod_cast this
  have hUzero : U = 0 := by
    rw [hrzero] at hUsq
    norm_num at hUsq
    omega
  have hQ : Q = 1 := by omega
  refine ⟨hQ, i, by exact_mod_cast hm, ?_⟩
  intro j hji
  have hj : z j ≤ r :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (z k))
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  omega
#print axioms Paper7MomentCounts.b6_top_moment_shape

end Paper7MomentCounts
