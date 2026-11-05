import Research.Backfill.Paper7.C61PerronDegreeBound
import Research.Backfill.Paper7.UnicyclicBareCycleIso
import Research.Backfill.Paper7.IntroUnicyclicSpectralWindow

/-! Universal local graph facts for the original arbitrary unicyclic graph.
The previously successful strict star bound is reused through its generic API. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroFour
open SimpleGraph BackfillPaper7.Challenge Paper7Unicyclic Paper7IntroGeneral

theorem cycle_vertex_degree_ge_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : V} (w : G.Walk r r)
    (hw : w.IsCycle) (v : V) (hv : v ∈ w.support) : 2 ≤ G.degree v := by
  have h := Set.ncard_le_ncard (w.toSubgraph.neighborSet_subset v)
  rw [hw.ncard_neighborSet_toSubgraph_eq_two hv, G.ncard_neighborSet] at h
  exact h
#print axioms Paper7IntroFour.cycle_vertex_degree_ge_two

theorem unicyclic_positive_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (v : V) : 1 ≤ G.degree v := by
  have hn := unicyclic_card_ge_three G hG
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact hG.1.preconnected.degree_pos_of_nontrivial v
#print axioms Paper7IntroFour.unicyclic_positive_degree

theorem unicyclic_two_step_continuation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (i : V) :
    ∃ j z : V, G.Adj i j ∧ G.Adj j z ∧ z ≠ i := by
  by_contra hno
  have hclosed : ∀ {u v : V} (p : G.Walk u v),
      (u = i ∨ G.Adj i u) → (v = i ∨ G.Adj i v) := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v z huv p ih =>
      intro hu
      apply ih
      rcases hu with rfl | hiu
      · exact Or.inr huv
      · left
        by_contra hvi
        exact hno ⟨u, v, hiu, huv, hvi⟩
  obtain ⟨s, ⟨r, w, hw, _hlen, _hs⟩, _hu⟩ := hG.2
  obtain ⟨j, hj, hji⟩ : ∃ j : V, j ∈ w.support ∧ j ≠ i := by
    by_contra hn
    have hsub : w.support.toFinset ⊆ {i} := by
      intro j hj
      apply Finset.mem_singleton.mpr
      by_contra hji
      exact hn ⟨j, List.mem_toFinset.mp hj, hji⟩
    have hc := Finset.card_le_card hsub
    rw [Paper7Cycles.cycle_support_card w hw, Finset.card_singleton] at hc
    have hthree := hw.three_le_length
    omega
  obtain ⟨p⟩ := hG.1 i j
  have hij : G.Adj i j := (hclosed p (Or.inl rfl)).resolve_left hji
  have hsub : G.neighborFinset j ⊆ {i} := by
    intro z hz
    apply Finset.mem_singleton.mpr
    by_contra hzi
    exact hno ⟨j, z, hij, (G.mem_neighborFinset j z).mp hz, hzi⟩
  have hc := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_singleton] at hc
  have htwo := cycle_vertex_degree_ge_two G w hw j hj
  omega
#print axioms Paper7IntroFour.unicyclic_two_step_continuation

theorem unicyclic_degree_lt_spectral_bound_sq
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ spec G, x ≤ R) (i : V) : (G.degree i : ℝ) < R ^ 2 := by
  let : Nonempty V := hG.1.nonempty
  obtain ⟨r, hr, v, hv, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron G hG.1
  obtain ⟨j, z, hij, hjz, hzi⟩ := unicyclic_two_step_continuation G b hG i
  have hd := Paper7C61Higher.degree_lt_eigenvalue_sq G r v hv he i j z hij hjz hzi
  have hrR := hbound r hr
  have hsq : r ^ 2 ≤ R ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (add_nonneg hR hr0)]
  exact hd.trans_le hsq
#print axioms Paper7IntroFour.unicyclic_degree_lt_spectral_bound_sq

theorem intro21_degree_le_fifteen
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (i : V) : G.degree i ≤ 15 := by
  have hd := unicyclic_degree_lt_spectral_bound_sq G b hG 4 (by norm_num) (by
    intro x hx
    obtain ⟨z, hz, _hlo, hhi⟩ := integral_unicyclic21_spectrum_window G hG hI hn x hx
    rw [hz]
    exact_mod_cast hhi) i
  norm_num at hd
  have hi : G.degree i < 16 := by exact_mod_cast hd
  omega
#print axioms Paper7IntroFour.intro21_degree_le_fifteen

theorem unicyclic_leaves_independent
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (i j : V)
    (hi : G.degree i = 1) (hj : G.degree j = 1) : ¬ G.Adj i j := by
  intro hij
  obtain ⟨k, z, hik, hkz, hzi⟩ := unicyclic_two_step_continuation G b hG i
  obtain ⟨a, _hia, hua⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hi
  have hkj : k = j := (hua k hik).trans (hua j hij).symm
  subst k
  obtain ⟨a, _hja, hua⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hj
  exact hzi ((hua z hkz).trans (hua i hij.symm).symm)
#print axioms Paper7IntroFour.unicyclic_leaves_independent

end Paper7IntroFour
