import Research.Backfill.Paper7.IntroDeletedBareCycleLength
import Research.Backfill.Paper7.IntroPendantFourExclusion
import Research.Backfill.Paper7.IntroPendantSixExclusion
import Research.Backfill.Paper7.IntroTwoRegularBoundary

/-! Combine the successful bare-cycle length reduction and the actual C4/C6
exclusions for an arbitrary even cycle attached through exactly one bridge. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCycleNeighborhood
open SimpleGraph BackfillPaper7.Challenge Paper7IntroCutGap Paper7IntroHighBranch

theorem cycle_iso_degree_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hb : 3 ≤ b)
    (e : G ≃g cycleGraph b) : ∀ v, G.degree v = 2 := by
  intro v
  have hcycle : (cycleGraph b).degree (e v) = 2 := by
    obtain ⟨n, hn⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
    subst b
    exact SimpleGraph.cycleGraph_degree_three_le
  exact (e.degree_eq v).symm.trans hcycle
#print axioms Paper7IntroCycleNeighborhood.cycle_iso_degree_two

def induce_away_deleted_vertex_iso
    {V : Type} (G : SimpleGraph V) (v : V) (S : Set V) (hv : v ∉ S) :
    (vertexDeletedGraph G v).induce {x : {w : V // w ≠ v} | x.val ∈ S} ≃g G.induce S where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, fun h => hv (h ▸ x.property)⟩, x.property⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by intro x y; rfl
#print axioms Paper7IntroCycleNeighborhood.induce_away_deleted_vertex_iso

theorem intro21_even_no_single_bridge_cycle_side
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (S : Set V) (u v : V) (hu : u ∈ S) (hv : v ∉ S) (huv : G.Adj u v)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → i = u ∧ j = v)
    (e : G.induce S ≃g cycleGraph b) : False := by
  have hb3 := Paper7Unicyclic.unicyclic_three_le hG
  let T : Set {w : V // w ≠ v} := {x | x.val ∈ S}
  have hsep : ∀ i ∈ T, ∀ j ∉ T, ¬(vertexDeletedGraph G v).Adj i j := by
    intro i hi j hj hij
    have he := (hcross i.val hi j.val hj hij).2
    exact j.property he
  let eT : (vertexDeletedGraph G v).induce T ≃g cycleGraph b :=
    (induce_away_deleted_vertex_iso G v S hv).trans e
  have hlen := Paper7IntroBareSide.integral_deleted_isolated_even_cycle_four_or_six
    G hI v T hsep b hb3 hb eT
  rcases hlen with hfour | hsix
  · subst b
    exact Paper7IntroPendantFour.intro21_no_single_bridge_four_side
      G hG hI hn S u v hu hv huv hcross e
  · subst b
    have hpos : 0 < Ngt G 2 := by
      by_contra hnot
      have hzero : Ngt G 2 = 0 := by omega
      exact Ngt_two_zero_two_regular_no_boundary G hzero (G.induce S) Subtype.val
        Subtype.val_injective (by intro i j; rfl)
        (cycle_iso_degree_two (G.induce S) 6 (by omega) e) v
        (fun i h => hv (h.symm ▸ i.property)) ⟨u, hu⟩ huv.symm
    obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hsmem, hs2⟩ := Multiset.mem_filter.mp hs
    exact Paper7IntroLocalQuartic.integral_connected_no_single_attachment_six_side
      G hG.1 hI s hsmem hs2 S ⟨u, hu⟩ e (fun i hi j hj hij => (hcross i hi j hj hij).1)
#print axioms Paper7IntroCycleNeighborhood.intro21_even_no_single_bridge_cycle_side

end Paper7IntroCycleNeighborhood
