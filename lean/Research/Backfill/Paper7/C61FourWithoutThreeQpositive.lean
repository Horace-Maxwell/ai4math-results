import Research.Backfill.Paper7.C61AlternatingQpositiveRotation
import Research.Backfill.Paper7.C61AlphaSixParity
import Research.Backfill.Paper7.C61RootFourReduction
import Research.Backfill.Paper7.C61PerronDegreeBound

/-! NEW SOURCE ONLY. The original no-three Perron-four q-positive branch,
without any added monodromy, parity, or parameter-coverage assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Higher Paper7C61Three
open scoped Classical

theorem actual_two_twice_pair_two (p q : Fin 6 → ℕ)
    (h0 : (actual p q 0).val = 2) : PairTwo p q := by
  have hm : mult (SG 6 p q) 2 = 2 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  have hmono : Mono 6 p q 2 = 1 :=
    (Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
      2 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
  rw [mono_two_six_product] at hmono
  have ht := real_six_triple_data _ _ _ _ _ _ hmono
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ hmono)
  exact ⟨ht.1, ht.2.1, (real_six_triple_data _ _ _ _ _ _ hr).1⟩
#print axioms Paper7C61Four.actual_two_twice_pair_two

theorem root_four_without_three_qpositive_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0)
    (hK : (Kq 6 q).Nonempty) : False := by
  obtain ⟨h0, hb, ha, hL, _hS, _hpc, _hqc⟩ :=
    root_four_without_three_qpositive_data p q hn hG h4 h1 hK
  have hq : ∃ k, 0 < q k := by
    obtain ⟨k, hk⟩ := hK
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  have hbound := alternating_qpositive_total_bound p q 13
    (alpha_six_parity p ha) (beta_six_full_unit_witness p q hb)
    (actual_two_twice_pair_two p q h0)
    (root_four_load_le_thirteen p q hn hG h4) hq
  omega
#print axioms Paper7C61Four.root_four_without_three_qpositive_impossible

end Paper7C61Four
