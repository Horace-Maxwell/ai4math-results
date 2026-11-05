import Research.Backfill.Paper7.C61SixMonodromyBound
import Research.Backfill.Paper7.C61HigherRemainderData
import Research.Backfill.Paper7.Lemma22EmptyQ

/-! Source-only exclusion of the beta-eight, zero-q Perron-five branch.
The monodromy identity is derived from the actual exceptional eigenspace.
No finite parameter table, added monodromy assumption, or acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61BetaEight
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7Lemma22Periodic Paper7Lemma22Gaps
open scoped Matrix BigOperators Classical

/-- At beta eight and q zero the actual exceptional recurrence has all two
initial states periodic, hence its transfer monodromy is the identity. -/
theorem beta_eight_qzero_monodromy (p q : Fin 6 → ℕ)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 8) :
    monodromy 6 (fun k => 1-(p k : ℝ)) = 1 := by
  have hK : Kq 6 q = ∅ := by
    ext k
    simp [Kq,hq]
  have hd : deltaE 6 p q 1 = 2 := by
    simp only [unitExponent,hK,Finset.card_empty,Nat.sub_zero] at hb
    omega
  have heq := (wmatKernelEquivFixedOfEmpty 6 p q (by decide) 1 hK).finrank_eq
  have hrank : Module.finrank ℝ
      (fixedSpace 6 (fun k => 1*(1-(p k : ℝ)))) = 2 := by
    rw [← heq]
    exact hd
  have htop : fixedSpace 6 (fun k => 1*(1-(p k : ℝ))) = ⊤ :=
    Submodule.eq_top_of_finrank_eq
      (by simpa only [Module.finrank_fin_fun] using hrank)
  have hz : monodromy 6 (fun k => 1*(1-(p k : ℝ))) - 1 = 0 := by
    apply Matrix.toLin'.injective
    have hker : LinearMap.ker (Matrix.toLin'
        (monodromy 6 (fun k => 1*(1-(p k : ℝ))) - 1)) = ⊤ := htop
    simpa only [map_zero] using LinearMap.ker_eq_top.mp hker
  simpa only [one_mul] using sub_eq_zero.mp hz
#print axioms Paper7C61BetaEight.beta_eight_qzero_monodromy

/-- This bound uses the full two-dimensional exceptional eigenspace, beyond
the first and second moment identities. -/
theorem beta_eight_qzero_totalP_le_twenty_four (p q : Fin 6 → ℕ)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 8) : totalP 6 p ≤ 24 := by
  have hm := beta_eight_qzero_monodromy p q hq hb
  have hp : sixProduct (1-(p 0 : ℤ)) (1-(p 1 : ℤ)) (1-(p 2 : ℤ))
      (1-(p 3 : ℤ)) (1-(p 4 : ℤ)) (1-(p 5 : ℤ)) = 1 := by
    calc
      _ = monodromy 6 (fun k => 1-(p k : ℝ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [sixProduct,intTransfer,monodromy,transfer,List.finRange_succ] <;> ring
      _ = 1 := hm
  have hs := six_product_sum_lower
    (1-(p 0 : ℤ)) (1-(p 1 : ℤ)) (1-(p 2 : ℤ))
    (1-(p 3 : ℤ)) (1-(p 4 : ℤ)) (1-(p 5 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hp
  have htotal : (totalP 6 p : ℤ) =
      (p 0 : ℤ)+p 1+p 2+p 3+p 4+p 5 := by
    simp [totalP,Fin.sum_univ_succ]; ring
  have hbound : (totalP 6 p : ℤ) ≤ 24 := by rw [htotal]; omega
  exact_mod_cast hbound
#print axioms Paper7C61BetaEight.beta_eight_qzero_totalP_le_twenty_four

/-- Full beta-eight exclusion under the original parameter/profile hypotheses.
The endpoint adds no search, recurrence, or support assumption. -/
theorem root_five_three_qzero_beta_eight_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 8) : False := by
  have hPbound := beta_eight_qzero_totalP_le_twenty_four p q hq hb
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hP := (root_five_three_parameter_relations p q hn hG h5 h1 h2).1
  rw [h0] at hP
  omega
#print axioms Paper7C61BetaEight.root_five_three_qzero_beta_eight_impossible

end Paper7C61BetaEight
