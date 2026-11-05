import Research.Backfill.Paper7.ChallengeV2

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
These are bounds for the frozen sigmaSq definition, including its nonpositive
integer arguments. No compilation or kernel acceptance is claimed. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Paper7Rank
open BackfillPaper7.Challenge

theorem sigmaSq_eq_zero_of_nonpos (t : ℤ) (ht : t ≤ 0) : sigmaSq t = 0 := by
  simp only [sigmaSq, Int.toNat_of_nonpos ht, Finset.range_zero, Finset.sum_empty]
#print axioms Paper7Rank.sigmaSq_eq_zero_of_nonpos

theorem sigmaSq_monotone : Monotone sigmaSq := by
  intro u v huv
  unfold sigmaSq
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Int.toNat_le_toNat huv))
  intro i _ _
  exact Nat.zero_le _
#print axioms Paper7Rank.sigmaSq_monotone

theorem sigmaSq_nat_slope (u v : ℕ) (huv : u ≤ v) :
    4 * (v - u) + sigmaSq (u : ℤ) ≤ sigmaSq (v : ℤ) := by
  unfold sigmaSq
  simp only [Int.toNat_natCast]
  have hsplit := Finset.sum_range_add (fun i : ℕ => (i / 4 + 2) ^ 2) u (v - u)
  have hadd : u + (v - u) = v := by omega
  rw [hadd] at hsplit
  rw [hsplit]
  have htail : 4 * (v - u) ≤
      ∑ i ∈ Finset.range (v - u), ((u + i) / 4 + 2) ^ 2 := by
    calc
      4 * (v - u) = ∑ _i ∈ Finset.range (v - u), (4 : ℕ) := by
        simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hi : 2 ≤ (u + i) / 4 + 2 := by omega
        simpa only [pow_two] using Nat.mul_le_mul hi hi
  omega
#print axioms Paper7Rank.sigmaSq_nat_slope

theorem sigmaSq_slope (u v : ℤ) (hu : 0 ≤ u) (huv : u ≤ v) :
    4 * (v - u) + (sigmaSq u : ℤ) ≤ (sigmaSq v : ℤ) := by
  have h := sigmaSq_nat_slope u.toNat v.toNat (Int.toNat_le_toNat huv)
  have hu' : (u.toNat : ℤ) = u := by omega
  have hv' : (v.toNat : ℤ) = v := by omega
  rw [hu', hv'] at h
  omega
#print axioms Paper7Rank.sigmaSq_slope

theorem sigmaSq_nine : sigmaSq 9 = 68 := by
  norm_num [sigmaSq, Finset.sum_range_succ]
#print axioms Paper7Rank.sigmaSq_nine

theorem sigmaSq_ten : sigmaSq 10 = 84 := by
  norm_num [sigmaSq, Finset.sum_range_succ]
#print axioms Paper7Rank.sigmaSq_ten

theorem sigmaSq_eleven : sigmaSq 11 = 100 := by
  norm_num [sigmaSq, Finset.sum_range_succ]
#print axioms Paper7Rank.sigmaSq_eleven

theorem sigmaSq_fourteen : sigmaSq 14 = 166 := by
  norm_num [sigmaSq, Finset.sum_range_succ]
#print axioms Paper7Rank.sigmaSq_fourteen

end Paper7Rank
