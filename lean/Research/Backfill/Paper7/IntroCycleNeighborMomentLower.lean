import Research.Backfill.Paper7.IntroFourthMomentNeighborLower
import Research.Backfill.Paper7.IntroUnicyclicContinuation
import Research.Backfill.Paper7.SunCycleSupport

/-! The two actual cycle neighbors and one actual outside neighbor form
three distinct neighbors. Their degree excess gives the extra moment mass. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroCycleMomentLower
open Matrix SimpleGraph Paper7SunMoments Paper7IntroFour

theorem cycle_vertex_external_neighbor_moment_lower
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : V} (w : G.Walk r r) (hw : w.IsCycle)
    (c a : V) (hc : c ∈ w.support) (ha : a ∉ w.support) (hca : G.Adj c a) :
    3 ≤ G.degree c ∧
      (G.degree c : ℝ) ^ 2 + (G.degree a : ℝ) + 1 ≤
        ((G.adjMatrix ℝ) ^ 4) c c := by
  obtain ⟨p, hp, q, hq, hcp, hcq, hpq⟩ := cycle_two_neighbors w hw c hc
  have hap : a ≠ p := fun h => ha (h.symm ▸ hp)
  have haq : a ≠ q := fun h => ha (h.symm ▸ hq)
  have hsub : ({a, p, q} : Finset V) ⊆ G.neighborFinset c := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hza | hzp | hzq
    · rw [hza]
      exact (G.mem_neighborFinset c a).mpr hca
    · rw [hzp]
      exact (G.mem_neighborFinset c p).mpr hcp
    · rw [hzq]
      exact (G.mem_neighborFinset c q).mpr hcq
  have hcard : ({a, p, q} : Finset V).card = 3 := by simp [hap, haq, hpq]
  have hdeg : 3 ≤ G.degree c := by
    have hs := Finset.card_le_card hsub
    rw [hcard, G.card_neighborFinset_eq_degree] at hs
    exact hs
  have hp2 : (2 : ℝ) ≤ G.degree p := by
    exact_mod_cast cycle_vertex_degree_ge_two G w hw p hp
  have hq2 : (2 : ℝ) ≤ G.degree q := by
    exact_mod_cast cycle_vertex_degree_ge_two G w hw q hq
  have hsum : (∑ u ∈ ({a, p, q} : Finset V), ((G.degree u : ℝ) - 1)) ≤
      ∑ u ∈ G.neighborFinset c, ((G.degree u : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro u hu _
    have hn : 1 ≤ G.degree u := ((G.mem_neighborFinset c u).mp hu).degree_pos_right
    have hr : (1 : ℝ) ≤ G.degree u := by exact_mod_cast hn
    linarith
  have hsmall : (∑ u ∈ ({a, p, q} : Finset V), ((G.degree u : ℝ) - 1)) =
      ((G.degree a : ℝ) - 1) + ((G.degree p : ℝ) - 1) +
        ((G.degree q : ℝ) - 1) := by
    simp [hap, haq, hpq, add_assoc]; ring
  rw [hsmall] at hsum
  have hmoment := fourth_moment_neighbor_excess_lower G c
  exact ⟨hdeg, by linarith⟩
#print axioms Paper7IntroCycleMomentLower.cycle_vertex_external_neighbor_moment_lower

end Paper7IntroCycleMomentLower
