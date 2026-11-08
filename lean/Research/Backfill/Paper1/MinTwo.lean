import Research.Backfill.Paper1.EqualParityMax
import Research.Backfill.Paper1.OppositeParity
import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1
namespace MinTwo

lemma dclosed_one (x : ℝ) : Challenge.dClosed 1 x = 3 * x - 4 := by
  simp [Challenge.dClosed]; ring

lemma dclosed_two (x : ℝ) : Challenge.dClosed 2 x = 5 * x ^ 2 - 8 * x + 4 := by
  simp [Challenge.dClosed, Finset.sum_range_succ]; ring

lemma delta_one (x : ℝ) (hx : x + 1 ≠ 0) : Challenge.deltaK 1 x = x - 2 := by
  rw [Challenge.deltaK, div_eq_iff hx]; ring

lemma delta_two (x : ℝ) (hx : x + 1 ≠ 0) :
    Challenge.deltaK 2 x = x ^ 2 - 2 * x + 2 := by
  rw [Challenge.deltaK, div_eq_iff hx]; ring

end MinTwo

/-- Both orientations of each boundary, with no upper bound on the other exponent. -/
theorem check_Theorem5MinTwo : Challenge.Theorem5MinTwo := by
  intro a b ha hb hab hmin p q hpq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpq.1.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hpq.2.1.pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hcases : a = 1 ∨ a = 2 ∨ b = 1 ∨ b = 2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hbo : Odd b := by
      obtain ⟨k, hk⟩ := hab
      exact ⟨k - 1, by omega⟩
    simpa only [MinTwo.dclosed_one, MinTwo.delta_one _ hp1] using
      EqualParityMax.maximum_one hpq hbo
  · have hbe : Even b := by
      obtain ⟨k, hk⟩ := hab
      exact ⟨k - 1, by omega⟩
    have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
    simpa only [MinTwo.dclosed_two, MinTwo.delta_two _ hp1] using
      EqualParityMax.maximum_two hpq hbe hb2
  · have hao : Odd a := by
      obtain ⟨k, hk⟩ := hab
      exact ⟨k - 1, by omega⟩
    have h := EqualParityMax.maximum_one (EqualParityMax.distinctOddPrimes_swap hpq) hao
    rw [EqualParityMax.oddSet_swap, EqualParityMax.evenSet_swap] at h
    simpa only [MinTwo.dclosed_one, MinTwo.delta_one _ hq1, mul_comm] using h
  · have hae : Even a := by
      obtain ⟨k, hk⟩ := hab
      exact ⟨k - 1, by omega⟩
    have ha2 : 2 ≤ a := by obtain ⟨k, hk⟩ := hae; omega
    have h := EqualParityMax.maximum_two (EqualParityMax.distinctOddPrimes_swap hpq) hae ha2
    rw [EqualParityMax.oddSet_swap, EqualParityMax.evenSet_swap] at h
    simpa only [MinTwo.dclosed_two, MinTwo.delta_two _ hq1, mul_comm] using h

/-- The complete retained introduction claim, including both parity classes. -/
theorem check_CompleteMinTwo : NarrowSupplement.CompleteMinTwo := by
  intro p q a b hpq ha hb hmin
  split_ifs with hpar
  · exact check_Theorem5MinTwo a b ha hb hpar hmin p q hpq
  · have ho : Odd (a + b) := (Nat.even_or_odd (a + b)).resolve_left hpar
    exact check_SummaryOppositeParity p q a b hpq ha hb ho

#print axioms check_Theorem5MinTwo
#print axioms check_CompleteMinTwo
end CodexPaper1
