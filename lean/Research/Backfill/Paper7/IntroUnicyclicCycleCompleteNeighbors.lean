import Research.Backfill.Paper7.UnicyclicCoreCycle
import Research.Backfill.Paper7.IntroEvenSingleBridgeCycle
import Research.Backfill.Paper7.SunCycleSupport

/-! The actual induced graph on the given unique cycle is a true cycle.
Its degree two gives complete internal neighborhoods, not only existence
of two incident cycle vertices. No integrality, size, Sun or branch-profile
condition is assumed. The generic cycle_two_neighbors theorem is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCycleCompleteNeighbors
open SimpleGraph BackfillPaper7.Challenge
open Paper7SunAssembly Paper7SunMoments Paper7IntroCycleNeighborhood

theorem unicyclic_cycle_two_neighbors_complete
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (x : V) (hx : x ∈ w.support) :
    ∃ y z : V, y ∈ w.support ∧ z ∈ w.support ∧ y ≠ z ∧
      G.Adj x y ∧ G.Adj x z ∧
      (∀ v, v ∈ w.support → (G.Adj x v ↔ v = y ∨ v = z)) := by
  let S : Set V := {v | v ∈ w.support}
  let K := G.induce S
  let xs : S := ⟨x, hx⟩
  obtain ⟨e⟩ := unicyclic_core_iso_cycle G b hG r w hw hlen
  have hb3 : 3 ≤ b := Paper7Unicyclic.unicyclic_three_le hG
  have hd : K.degree xs = 2 := cycle_iso_degree_two K b hb3 e.symm xs
  obtain ⟨y, hy, z, hz, hxy, hxz, hyz⟩ := cycle_two_neighbors w hw x hx
  let ys : S := ⟨y, hy⟩
  let zs : S := ⟨z, hz⟩
  have hys : ys ≠ zs := by
    intro he
    exact hyz (congrArg Subtype.val he)
  have hsub : ({ys, zs} : Finset S) ⊆ K.neighborFinset xs := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvy | hvz
    · rw [hvy]
      exact (K.mem_neighborFinset xs ys).mpr hxy
    · rw [hvz]
      exact (K.mem_neighborFinset xs zs).mpr hxz
  have heq : ({ys, zs} : Finset S) = K.neighborFinset xs := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [K.card_neighborFinset_eq_degree, hd, Finset.card_pair hys]
  refine ⟨y, z, hy, hz, hyz, hxy, hxz, ?_⟩
  intro v hv
  constructor
  · intro hxv
    have hmem : (⟨v, hv⟩ : S) ∈ K.neighborFinset xs :=
      (K.mem_neighborFinset xs ⟨v, hv⟩).mpr hxv
    rw [← heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmy | hmz
    · exact Or.inl (congrArg Subtype.val hmy)
    · exact Or.inr (congrArg Subtype.val hmz)
  · rintro (hvy | hvz)
    · rw [hvy]
      exact hxy
    · rw [hvz]
      exact hxz
#print axioms Paper7IntroCycleCompleteNeighbors.unicyclic_cycle_two_neighbors_complete

theorem unicyclic_cycle_neighbor_continuation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (x y : V) (hx : x ∈ w.support) (hy : y ∈ w.support) (hxy : G.Adj x y) :
    ∃ z : V, z ∈ w.support ∧ z ≠ y ∧ G.Adj x z ∧
      (∀ v, v ∈ w.support → (G.Adj x v ↔ v = y ∨ v = z)) := by
  obtain ⟨p, q, hp, hq, hpq, hxp, hxq, hfull⟩ :=
    unicyclic_cycle_two_neighbors_complete G b hG r w hw hlen x hx
  rcases (hfull y hy).mp hxy with hyp | hyq
  · refine ⟨q, hq, ?_, hxq, ?_⟩
    · intro hqy
      exact hpq (hyp.symm.trans hqy.symm)
    · intro v hv
      rw [hyp]
      exact hfull v hv
  · refine ⟨p, hp, ?_, hxp, ?_⟩
    · intro hpy
      exact hpq (hpy.trans hyq)
    · intro v hv
      rw [hyq]
      exact (hfull v hv).trans or_comm
#print axioms Paper7IntroCycleCompleteNeighbors.unicyclic_cycle_neighbor_continuation

end Paper7IntroCycleCompleteNeighbors
