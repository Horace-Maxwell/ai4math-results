import Research.Backfill.Paper7.C61SixMonodromySharp
import Research.Backfill.Paper7.C61PerronFiveBetaEight
import Research.Backfill.Paper7.C61TwoSiteExclusion

/-! Source-only exclusion of the whole zero-q, beta-eight remainder for
Perron three and Perron four. Other exponent domains remain open. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Sharp
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61BetaEight Paper7Lemma22Periodic
open scoped Matrix BigOperators Classical

/-- A full two-dimensional exceptional eigenspace on this six-cycle
forces at most twelve pendant vertices when q is zero. -/
theorem beta_eight_qzero_totalP_le_twelve (p q : Fin 6 → ℕ)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 8) : totalP 6 p ≤ 12 := by
  have hm := beta_eight_qzero_monodromy p q hq hb
  have hp : sixProduct (1-(p 0 : ℤ)) (1-(p 1 : ℤ)) (1-(p 2 : ℤ))
      (1-(p 3 : ℤ)) (1-(p 4 : ℤ)) (1-(p 5 : ℤ)) = 1 := by
    calc
      _ = monodromy 6 (fun k => 1-(p k : ℝ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [sixProduct,intTransfer,monodromy,transfer,List.finRange_succ] <;> ring
      _ = 1 := hm
  have hs := six_product_sharp_sum_lower
    (1-(p 0 : ℤ)) (1-(p 1 : ℤ)) (1-(p 2 : ℤ))
    (1-(p 3 : ℤ)) (1-(p 4 : ℤ)) (1-(p 5 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hp
  have htotal : (totalP 6 p : ℤ) =
      (p 0 : ℤ)+p 1+p 2+p 3+p 4+p 5 := by
    simp [totalP,Fin.sum_univ_succ]; ring
  have hbound : (totalP 6 p : ℤ) ≤ 12 := by rw [htotal]; omega
  exact_mod_cast hbound
#print axioms Paper7C61Sharp.beta_eight_qzero_totalP_le_twelve

theorem root_three_qzero_beta_eight_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 8) : False := by
  have h0 := root_three_has_two_twos p q hn hG h3
  have hbound := beta_eight_qzero_totalP_le_twelve p q hq hb
  rcases root_three_qzero_two_twos_cases p q hn hG h3 h0 hq with
    ⟨hb6,_hP,_hS⟩ | ⟨hb7,_hP,_hS⟩ | ⟨_hb8,hP,_hS⟩
  · omega
  · omega
  · omega
#print axioms Paper7C61Sharp.root_three_qzero_beta_eight_impossible

/-- This removes the beta-eight domain; the two displayed domains are
necessary conditions, not completed classifications or existence claims. -/
theorem root_three_qzero_remaining_cases (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hq : q = (fun _ => 0)) :
    (unitExponent p q = 6 ∧ totalP 6 p = 11 ∧ squares 6 p = 51) ∨
    (unitExponent p q = 7 ∧ totalP 6 p = 12 ∧ squares 6 p = 48) := by
  have h0 := root_three_has_two_twos p q hn hG h3
  rcases root_three_qzero_two_twos_cases p q hn hG h3 h0 hq with h6 | h7 | h8
  · exact Or.inl h6
  · exact Or.inr h7
  · exact (root_three_qzero_beta_eight_impossible p q hn hG h3 hq h8.1).elim
#print axioms Paper7C61Sharp.root_three_qzero_remaining_cases

/-- This covers all Perron-four profiles, including the non-saturated
profiles containing 3, without fixing their coordinate positions. -/
theorem root_four_qzero_beta_eight_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 8) : False := by
  have hbound := beta_eight_qzero_totalP_le_twelve p q hq hb
  have hc := root_four_card_at_least_three p q hn hG h4
  have hcard := (root_four_profile (actual p q) h4).1
  have hsum := (root_four_parameter_relations p q hn hG h4).1
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  omega
#print axioms Paper7C61Sharp.root_four_qzero_beta_eight_impossible

/-- The remaining no-3 zero-q Perron-four branch is now exactly beta seven.
Its position/polynomial exclusion is not asserted by this theorem. -/
theorem root_four_without_three_qzero_remaining_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0)
    (hq : q = (fun _ => 0)) :
    unitExponent p q = 7 ∧ totalP 6 p = 19 ∧ squares 6 p = 195 := by
  rcases root_four_without_three_qzero_cases p q hn hG h4 h1 hq with h7 | h8
  · exact h7
  · exact (root_four_qzero_beta_eight_impossible p q hn hG h4 hq h8.1).elim
#print axioms Paper7C61Sharp.root_four_without_three_qzero_remaining_data

end Paper7C61Sharp
