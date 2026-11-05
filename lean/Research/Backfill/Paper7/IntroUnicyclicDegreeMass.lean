import Research.Backfill.Paper7.UnicyclicCardinality
import Mathlib

/-! Source-only necessary constraints for every actual unicyclic graph.
No assumption about the shape or number of off-cycle branches is made. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Paper7IntroGeneral
open SimpleGraph BackfillPaper7.Challenge Paper7Unicyclic

theorem unicyclic_card_ge_three {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) : 3 ≤ Fintype.card V := by
  obtain ⟨s, hs, _⟩ := hG.2
  obtain ⟨u, w, hw, _hlen, _hedges⟩ := hs
  have hlen := hw.isTrail.length_le_card_edgeFinset
  rw [unicyclic_card_edges G hG] at hlen
  exact hw.three_le_length.trans hlen
#print axioms Paper7IntroGeneral.unicyclic_card_ge_three

/-- The loss from the uniform `n+1` row-sum bound is exactly the degree
excess at vertices outside the closed neighborhood. Natural subtraction
is justified by connectedness and the actual cycle. -/
theorem unicyclic_neighbor_degree_excess {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) (v : V) :
    (∑ u ∈ G.neighborFinset v, G.degree u) +
      (∑ u ∈ (Finset.univ.erase v) \ G.neighborFinset v, (G.degree u - 1)) =
        Fintype.card V + 1 := by
  have hn := unicyclic_card_ge_three G hG
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos (u : V) : 1 ≤ G.degree u :=
    hG.1.preconnected.degree_pos_of_nontrivial u
  let t := (Finset.univ.erase v) \ G.neighborFinset v
  have hs : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ u⟩
    intro huv
    subst u
    exact G.notMem_neighborFinset_self v hu
  have hpart : (∑ u ∈ t, G.degree u) +
      (∑ u ∈ G.neighborFinset v, G.degree u) =
        ∑ u ∈ Finset.univ.erase v, G.degree u := Finset.sum_sdiff hs
  have htotal : (∑ u ∈ Finset.univ.erase v, G.degree u) + G.degree v =
      2 * Fintype.card V := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ v),
      G.sum_degrees_eq_twice_card_edges, unicyclic_card_edges G hG]
  have hcard : t.card + G.degree v = Fintype.card V - 1 := by
    simpa only [t, G.card_neighborFinset_eq_degree,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card hs
  have hexcess : (∑ u ∈ t, G.degree u) =
      (∑ u ∈ t, (G.degree u - 1)) + t.card := by
    calc
      _ = ∑ u ∈ t, ((G.degree u - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro u _hu
        have := hpos u
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  change (∑ u ∈ G.neighborFinset v, G.degree u) +
    (∑ u ∈ t, (G.degree u - 1)) = Fintype.card V + 1
  omega
#print axioms Paper7IntroGeneral.unicyclic_neighbor_degree_excess

theorem unicyclic_neighbor_degree_sum_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) (v : V) :
    (∑ u ∈ G.neighborFinset v, G.degree u) ≤ Fintype.card V + 1 := by
  have := unicyclic_neighbor_degree_excess G hG v
  omega
#print axioms Paper7IntroGeneral.unicyclic_neighbor_degree_sum_le

/-- Every nonadjacent vertex, including every off-cycle branch, consumes
its full `degree-1` amount of the row-sum budget. -/
theorem unicyclic_branch_degree_deficit {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) (v w : V) (hne : w ≠ v)
    (hnadj : ¬ G.Adj v w) :
    (∑ u ∈ G.neighborFinset v, G.degree u) + (G.degree w - 1) ≤
      Fintype.card V + 1 := by
  have hw : w ∈ (Finset.univ.erase v) \ G.neighborFinset v := by
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ,
      and_true, G.mem_neighborFinset]
    exact ⟨hne, hnadj⟩
  have hterm : G.degree w - 1 ≤
      ∑ u ∈ (Finset.univ.erase v) \ G.neighborFinset v, (G.degree u - 1) :=
    Finset.single_le_sum (f := fun u : V => G.degree u - 1) (fun _ _ => Nat.zero_le _) hw
  have hmass := unicyclic_neighbor_degree_excess G hG v
  omega
#print axioms Paper7IntroGeneral.unicyclic_branch_degree_deficit

end Paper7IntroGeneral
