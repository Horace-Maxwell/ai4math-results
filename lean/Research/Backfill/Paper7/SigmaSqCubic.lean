import Research.Backfill.Paper7.SigmaSqBounds

/-! Exact cubic estimates for the frozen floor-defined sigmaSq sequence. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7Section6
open BackfillPaper7.Challenge Paper7Rank

theorem sigmaSq_four_step (k : ℕ) :
    sigmaSq ((4*(k+1) : ℕ) : ℤ) =
      sigmaSq ((4*k : ℕ) : ℤ) + 4*(k+2)^2 := by
  have hd0 : (4*k)/4 = k := by omega
  have hd1 : (4*k+1)/4 = k := by omega
  have hd2 : (4*k+2)/4 = k := by omega
  have hd3 : (4*k+3)/4 = k := by omega
  unfold sigmaSq
  simp only [Int.toNat_natCast]
  rw [show 4*(k+1) = 4*k+4 by omega, Finset.sum_range_add]
  congr 1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.add_zero, hd0, hd1, hd2, hd3]
  omega
#print axioms Paper7Section6.sigmaSq_four_step

theorem sigmaSq_four_cubic (k : ℕ) :
    4*k^3 ≤ 3*sigmaSq ((4*k : ℕ) : ℤ) := by
  induction k with
  | zero => norm_num [sigmaSq]
  | succ k ih =>
    rw [sigmaSq_four_step]
    nlinarith
#print axioms Paper7Section6.sigmaSq_four_cubic

theorem sigmaSq_rank_cube_budget (r n : ℕ)
    (hs : sigmaSq (r : ℤ) ≤ 2*n) : (4*(r/4))^3 ≤ 96*n := by
  have harg : ((4*(r/4) : ℕ) : ℤ) ≤ (r : ℤ) := by
    exact_mod_cast (show 4*(r/4) ≤ r by omega)
  have hm := sigmaSq_monotone harg
  have hc := sigmaSq_four_cubic (r/4)
  nlinarith
#print axioms Paper7Section6.sigmaSq_rank_cube_budget

end Paper7Section6
