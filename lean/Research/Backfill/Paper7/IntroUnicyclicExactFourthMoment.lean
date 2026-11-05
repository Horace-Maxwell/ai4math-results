import Research.Backfill.Paper7.IntroExactFourthMomentBinaryRows
import Research.Backfill.Paper7.IntroUnicyclicCircleTwoStep

/-! Exact fourth moments from actual common-neighbor fibres of the unique
cycle. No prescribed matrix entry or off-diagonal coverage is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroUnicyclicExactFourth
open SimpleGraph BackfillPaper7.Challenge
open Paper7IntroExactFourthMoment Paper7IntroTwoStepTopology
open Paper7IntroTwoWalkCollision Paper7IntroPendantFour

theorem unicyclic_nonfour_fourth_moment_exact
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b ≠ 4) (c : V) :
    ((G.adjMatrix ℝ) ^ 4) c c = (G.degree c : ℝ) ^ 2 +
      ∑ u ∈ G.neighborFinset c, ((G.degree u : ℝ) - 1) := by
  apply fourth_moment_binary_off_diagonal G c
  intro j hj
  have hcard : ((G.neighborFinset c).filter (fun p => G.Adj p j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpN, hpj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqN, hqj⟩ := Finset.mem_filter.mp hq
    by_contra hpq
    have hfour := unicyclic_double_common_forces_four_cycle G b hG r w hw hlen
      c p j q hj.symm hpq ((G.mem_neighborFinset c p).mp hpN) hpj
      ((G.mem_neighborFinset c q).mp hqN) hqj
    exact hb4 hfour.1
  have hcases : ((G.neighborFinset c).filter (fun p => G.Adj p j)).card = 0 ∨
      ((G.neighborFinset c).filter (fun p => G.Adj p j)).card = 1 := by omega
  rw [adjacency_square_common_card]
  rcases hcases with h | h
  · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inr (by rw [h]; norm_num)
#print axioms Paper7IntroUnicyclicExactFourth.unicyclic_nonfour_fourth_moment_exact

theorem unicyclic_four_fourth_moment_exact
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b = 4) (c : V) (hc : c ∈ w.support) :
    ((G.adjMatrix ℝ) ^ 4) c c = (G.degree c : ℝ) ^ 2 +
      (∑ u ∈ G.neighborFinset c, ((G.degree u : ℝ) - 1)) + 2 := by
  obtain ⟨p, j₀, q, _hcp, hcj₀, _hcq, _hpj₀, hpq, _hj₀q,
    _hcpA, _hpj₀A, _hj₀qA, _hqcA, _hsupp, _hcommon, hfilter, hdouble,
    _hdoubleRev, _hnotcj₀, _hnotpq⟩ :=
    unicyclic_four_circle_at_vertex G b hG r w hw hlen hb4 c hc
  have hb : Even b := by rw [hb4]; decide
  have htriangle := even_unicyclic_no_triangle G b hG hb
  obtain ⟨q₀, hbudget⟩ := unicyclic_common_card_one_exception G b hG htriangle c
  have htwo : ((G.neighborFinset c).filter (fun p => G.Adj p j₀)).card = 2 := by
    rw [hfilter, Finset.card_pair hpq]
  have hq₀ : q₀ = j₀ := by
    by_contra hne
    have h := hbudget j₀ hcj₀.symm
    rw [htwo] at h
    have hne' : j₀ ≠ q₀ := fun he => hne he.symm
    simp only [ite_eq_right hne'] at h
    omega
  subst q₀
  apply fourth_moment_one_double_off_diagonal G c j₀ hcj₀.symm hdouble
  intro j hj hj₀
  have hcard := hbudget j hj
  simp only [ite_eq_right hj₀] at hcard
  have hcases : ((G.neighborFinset c).filter (fun p => G.Adj p j)).card = 0 ∨
      ((G.neighborFinset c).filter (fun p => G.Adj p j)).card = 1 := by omega
  rw [adjacency_square_common_card]
  rcases hcases with h | h
  · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inr (by rw [h]; norm_num)
#print axioms Paper7IntroUnicyclicExactFourth.unicyclic_four_fourth_moment_exact

end Paper7IntroUnicyclicExactFourth
