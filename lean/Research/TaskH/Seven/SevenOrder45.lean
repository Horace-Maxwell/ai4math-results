import Research.TaskH.Seven.SevenHamiltonMissingEdge
import Research.TaskH.Seven.SevenSCCFamilyPartition

/-! Actual one-circle SCC exclusion and the direct order45 conclusion.
K5-freeness is an explicit internal lemma input, independently derived
elsewhere; no new premise is attached to the frozen CaseSeven statement. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def nonbadThroughFinset (G : SimpleGraph V) (x y z : V) :
    Finset (Finset (Sym2 V)) :=
  (nonbadCircleFinset G x y).filter (fun C => CycleContains C z)

theorem cycleDegree_le_bad_add_nonbadThrough (x y z : V) :
    cycleDegree G z ≤ (jointCircleFinset G x y).card + (nonbadThroughFinset G x y z).card := by
  classical
  have hsub : throughFinset G z ⊆ jointCircleFinset G x y ∪ nonbadThroughFinset G x y z := by
    intro C hC
    have hCm := (mem_throughFinset C z).mp hC
    by_cases hbad : CycleContains C x ∧ CycleContains C y
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨(mem_cycleFinset C).mpr hCm.1, hbad⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(mem_cycleFinset C).mpr hCm.1, hbad⟩, hCm.2⟩))
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (jointCircleFinset G x y) (nonbadThroughFinset G x y z)
  change (throughFinset G z).card ≤ _
  omega

theorem nonbadThrough_subset_sevenVertexCircleFinset
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    {x y : V} (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {Q : Finset V}
    (hQ : Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π))
    {z : V} (hzQ : z ∈ Q) :
    nonbadThroughFinset G x y z ⊆ sevenVertexCircleFinset G Q := by
  classical
  obtain ⟨a, _ha, hQa⟩ := Finset.mem_image.mp hQ
  intro C hC
  have hnonbad := (Finset.mem_filter.mp hC).1
  have hzC := (Finset.mem_filter.mp hC).2
  have hcycle := (Finset.mem_filter.mp hnonbad).1
  have hbad := (Finset.mem_filter.mp hnonbad).2
  have hmod := (mem_cycleFinset C).mp hcycle
  obtain ⟨b, p, hp, hset, hdiv⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmod
  have hl := hs p hp hdiv
  have hzp : z ∈ p.support := by
    apply (cycleContains_edges_toFinset_iff p hp.not_nil z).mp
    simpa only [hset] using hzC
  have hav : x ∉ p.support ∨ y ∉ p.support := by
    by_cases hx : x ∈ p.support
    · right
      intro hy
      apply hbad
      constructor
      · rw [← hset]
        exact (cycleContains_edges_toFinset_iff p hp.not_nil x).mpr hx
      · rw [← hset]
        exact (cycleContains_edges_toFinset_iff p hp.not_nil y).mpr hy
    · exact Or.inl hx
  obtain ⟨f, hf, hfset⟩ := exists_heptagon_of_cycle_length_seven hp hl
  apply Finset.mem_filter.mpr
  refine ⟨(mem_actualSevenEdgeSets_iff C).mpr ⟨f, hf, hfset.trans hset⟩, ?_⟩
  intro w hw
  have hwp : w ∈ p.support := by
    apply (cycleContains_edges_toFinset_iff p hp.not_nil w).mp
    rw [hset]
    exact (TaskH.mem_cycleVertices C w).mp hw
  have hzw := nonbad_cycle_successorEquivalent hr p hp hl hav c π hzp hwp
  have haz := (mem_successorComponent c (orderedColorCycle π) a z).mp
    (hQa.symm ▸ hzQ)
  have haw := successorEquivalent_trans haz hzw
  have hwQ := (mem_successorComponent c (orderedColorCycle π) a w).mpr haw
  exact hQa ▸ hwQ

theorem seven_set_missing_edge_of_cliqueFree_five (hfree : G.CliqueFree 5)
    {Q : Finset V} (hQ : Q.card = 7) :
    ∃ u ∈ Q, ∃ v ∈ Q, u ≠ v ∧ ¬ G.Adj u v := by
  classical
  by_contra hnot
  push Not at hnot
  have hclique : G.IsClique (Q : Set V) := by
    intro u hu v hv hne
    have hcases : u = v ∨ u ≠ v := by
      let dec : DecidableEq V := (Fintype.equivFin V).decidableEq
      cases dec u v with
      | isTrue he => exact Or.inl he
      | isFalse hn => exact Or.inr hn
    rcases hcases with he | _hne
    · exact (hne he).elim
    exact hnot u hu v hv hne
  have hfree7 : G.CliqueFree 7 := SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 7) hfree
  exact hfree7 Q ⟨hclique, hQ⟩

theorem equality_componentCircleFinset_nonempty [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hxy : x ≠ y) (hbad : (jointCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {Q : Finset V}
    (hQ : Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)) :
    (componentCircleFinset G c π Q).Nonempty := by
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hQ
  rw [componentCircleFinset_eq_following hxy c (deletedEdge_coloring_endpoints hcrit c) π]
  apply sccFollowingCircleFinset_nonempty (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc)
    (equality_three_hundred_sixty_one_le_cycleDegree hcrit hc) _ c
    (deletedEdge_coloring_endpoints hcrit c) π a
  rw [sccBadCircleFinset_eq_jointCircleFinset]
  exact hbad

theorem equality_two_le_componentCircleFinset_card [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hfree : G.CliqueFree 5)
    {x y : V} (hxy : x ≠ y) (hbad : (jointCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {Q : Finset V}
    (hQ : Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)) :
    2 ≤ (componentCircleFinset G c π Q).card := by
  classical
  by_contra hnot
  have hsmall : (componentCircleFinset G c π Q).card ≤ 1 := by omega
  have hcover := equality_componentCircleFinset_cover hcrit hc hxy hbad c π hQ
  have hQle : Q.card ≤ 7 := by omega
  obtain ⟨C, hC⟩ := equality_componentCircleFinset_nonempty hcrit hc hxy hbad c π hQ
  have hglobal := (Finset.mem_filter.mp hC).1
  have hnonbad := (Finset.mem_filter.mp hglobal).1
  have hcycle := (Finset.mem_filter.mp hnonbad).1
  have hmod := (mem_cycleFinset C).mp hcycle
  have hsubset := (Finset.mem_filter.mp hC).2
  have hCcard := cycleVertices_card_seven_of_mem (equality_shortSevenCycles hcrit hc) hmod
  have hQge : 7 ≤ Q.card := by
    have h := Finset.card_le_card hsubset
    rw [hCcard] at h
    exact h
  have hQcard : Q.card = 7 := by omega
  obtain ⟨u, hu, v, hv, hne, hnon⟩ := seven_set_missing_edge_of_cliqueFree_five hfree hQcard
  have hcap := sevenVertexCircleFinset_card_le_240 (G := G) hQcard hu hv hne hnon
  have hsub := nonbadThrough_subset_sevenVertexCircleFinset
    (equality_shortSevenCycles hcrit hc) (equality_rainbowSevenCycles hcrit hc) c π hQ hu
  have hnonbadcard : (nonbadThroughFinset G x y u).card ≤ 240 :=
    (Finset.card_le_card hsub).trans hcap
  have hbudget := cycleDegree_le_bad_add_nonbadThrough (G := G) x y u
  have hdegree := equality_three_hundred_sixty_one_le_cycleDegree hcrit hc u
  omega

/-- This is the internal K5-free branch lemma. K5-freeness is to be
derived independently from the original noncomplete equality branch. -/
theorem equality_card_le_forty_five_of_cliqueFree_five [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hfree : G.CliqueFree 5) : Fintype.card V ≤ 45 := by
  classical
  by_contra hnot
  have hn : 46 ≤ Fintype.card V := by omega
  obtain ⟨x, y, hxy, c, π, _hpos, hbad, hsmall, _hsum, _hcover⟩ :=
    equality_exists_small_component_circle_system hcrit hc hn
  have hbound := equality_order45_of_component_circle_lower hcrit hc hxy.ne hbad c π hsmall
    (fun Q hQ => equality_two_le_componentCircleFinset_card hcrit hc hfree hxy.ne hbad c π hQ)
  omega

end TaskH.Seven

#print axioms TaskH.Seven.nonbadThroughFinset
#print axioms TaskH.Seven.cycleDegree_le_bad_add_nonbadThrough
#print axioms TaskH.Seven.nonbadThrough_subset_sevenVertexCircleFinset
#print axioms TaskH.Seven.seven_set_missing_edge_of_cliqueFree_five
#print axioms TaskH.Seven.equality_componentCircleFinset_nonempty
#print axioms TaskH.Seven.equality_two_le_componentCircleFinset_card
#print axioms TaskH.Seven.equality_card_le_forty_five_of_cliqueFree_five
