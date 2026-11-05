import Research.Backfill.Paper7.C61ThreeQzero
import Research.Backfill.Paper7.C61ThreeQpositiveRotation

/-! SOURCE ONLY. Complete Perron-three exclusion with precisely the original
graph, size and profile premises. No extra monodromy or coverage premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Small
open scoped Classical

theorem root_three_qpositive_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hK : (Kq 6 q).Nonempty) : False := by
  obtain ⟨_h0,hb,ha,hs,_hS,_hpc,_hqc⟩ :=
    root_three_qpositive_data p q hn hG h3 hK
  apply alternating_qpositive_impossible p q (alpha_six_parity p ha)
    (beta_six_full_unit_witness p q hb)
    (root_three_coefficient_pairs p q hn hG h3) hs
    (root_three_load_le_six p q hn hG h3)
  obtain ⟨k,hk⟩ := hK
  exact ⟨k,(Finset.mem_filter.mp hk).2⟩
#print axioms Paper7C61Three.root_three_qpositive_impossible

theorem root_three_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) : False := by
  by_cases hq : q = (fun _ => 0)
  · exact root_three_qzero_impossible p q hn hG h3 hq
  · have hex : ∃ k, 0 < q k := by
      by_contra! hz
      apply hq
      funext k
      exact Nat.eq_zero_of_le_zero (hz k)
    obtain ⟨k,hk⟩ := hex
    exact root_three_qpositive_impossible p q hn hG h3
      ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ k,hk⟩⟩
#print axioms Paper7C61Three.root_three_impossible

end Paper7C61Three
