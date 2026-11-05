import Research.Backfill.Paper7.BoundaryTestRequirements

/-! Small graph tests only. The finite-walk bridge proves completeness of each
bounded cycle-edge enumeration; rotations and reversal are deduplicated by the
actual edge Finset. No paper contract is imported as a proved theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Paper7StatementTestsV3
open BackfillPaper7.Challenge SimpleGraph Finset

/-- Computable finite description of exactly the cycles of a fixed length. -/
def finiteCycleEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Finset (Finset (Sym2 V)) :=
  Finset.univ.biUnion fun u =>
    ((G.finsetWalkLength n u u).filter
      (fun w => w.tail.support.Nodup ∧ 3 ≤ w.length)).image (fun w => w.edges.toFinset)

 theorem finiteCycleEdges_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    (finiteCycleEdges G n : Set (Finset (Sym2 V))) = cycleEdgeSets G n := by
  ext s
  simp only [finiteCycleEdges, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff,
    cycleEdgeSets, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u,w,⟨hlen,hpath,hthree⟩,heq⟩
    refine ⟨u,w,?_,hlen,heq⟩
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨(SimpleGraph.Walk.isPath_def w.tail).mpr hpath,hthree⟩
  · rintro ⟨u,w,hcycle,hlen,heq⟩
    exact ⟨u,w,⟨hlen,(SimpleGraph.Walk.isPath_def w.tail).mp hcycle.isPath_tail,
      hcycle.three_le_length⟩,heq⟩
#print axioms Paper7StatementTestsV3.finiteCycleEdges_eq

theorem cycleCount_finite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    cycleCount G n = (finiteCycleEdges G n).card := by
  rw [cycleCount, ← finiteCycleEdges_eq]
  simp
#print axioms Paper7StatementTestsV3.cycleCount_finite

theorem cycle_exists_of_finite_nonempty {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (h : (finiteCycleEdges G n).Nonempty) :
    ∃ u, ∃ w : G.Walk u u, w.IsCycle ∧ w.length = n := by
  obtain ⟨s,hs⟩ := h
  have : s ∈ cycleEdgeSets G n := by
    rw [← finiteCycleEdges_eq]
    exact hs
  obtain ⟨u,w,hw,hlen,_⟩ := this
  exact ⟨u,w,hw,hlen⟩
#print axioms Paper7StatementTestsV3.cycle_exists_of_finite_nonempty

theorem no_cycle_of_finite_empty {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (h : finiteCycleEdges G n = ∅) (u : V) (w : G.Walk u u)
    (hc : w.IsCycle) : w.length ≠ n := by
  intro hl
  have hs : w.edges.toFinset ∈ cycleEdgeSets G n := ⟨u,w,hc,hl,rfl⟩
  rw [← finiteCycleEdges_eq, h] at hs
  simp at hs
#print axioms Paper7StatementTestsV3.no_cycle_of_finite_empty

theorem test085 : BackfillPaper7.BoundaryTestRequirements.test_085 := by
  have h : cycleCount (⊤ : SimpleGraph (Fin 3)) 3 = 1 := by
    rw [cycleCount_finite]
    decide +kernel
  exact ⟨h,by omega⟩
#print axioms Paper7StatementTestsV3.test085

theorem test086 : BackfillPaper7.BoundaryTestRequirements.test_086 := by
  constructor <;> rw [cycleCount_finite] <;> decide +kernel
#print axioms Paper7StatementTestsV3.test086

theorem test087 : BackfillPaper7.BoundaryTestRequirements.test_087 := by
  rw [BackfillPaper7.BoundaryTestRequirements.test_087, cycleCount_finite]
  decide +kernel
#print axioms Paper7StatementTestsV3.test087

theorem test088 : BackfillPaper7.BoundaryTestRequirements.test_088 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact cycle_exists_of_finite_nonempty _ 3 (by decide +kernel)
  · intro u w hw _
    exact hw.three_le_length
#print axioms Paper7StatementTestsV3.test088

theorem test089 : BackfillPaper7.BoundaryTestRequirements.test_089 := by
  have hnone : finiteCycleEdges (SimpleGraph.cycleGraph 5) 3 = ∅ := by decide +kernel
  constructor
  · refine ⟨by decide, ?_, ?_⟩
    · exact cycle_exists_of_finite_nonempty _ 5 (by decide +kernel)
    · intro u w hw hodd
      have hmin := hw.three_le_length
      have hne := no_cycle_of_finite_empty _ 3 hnone u w hw
      have hmod := Nat.odd_iff.mp hodd
      omega
  · rintro ⟨_,⟨u,w,hc,hl⟩,_⟩
    exact no_cycle_of_finite_empty _ 3 hnone u w hc hl
#print axioms Paper7StatementTestsV3.test089

theorem test090 : BackfillPaper7.BoundaryTestRequirements.test_090 := by
  intro g hg
  obtain ⟨hodd,⟨u,w,_,hlen⟩,_⟩ := hg
  let c := SimpleGraph.cycleGraph.bicoloring_of_even 4 (by decide)
  have heven : Even w.length := (c.even_length_iff_congr w).mpr Iff.rfl
  rw [hlen] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven
#print axioms Paper7StatementTestsV3.test090

theorem test091 : BackfillPaper7.BoundaryTestRequirements.test_091 := by
  have hcard : (finiteCycleEdges (SimpleGraph.cycleGraph 3) 3).card = 1 := by decide +kernel
  obtain ⟨s,hs⟩ := Finset.card_eq_one.mp hcard
  have hmem : s ∈ cycleEdgeSets (SimpleGraph.cycleGraph 3) 3 := by
    rw [← finiteCycleEdges_eq, hs]
    simp
  refine ⟨SimpleGraph.cycleGraph_connected, s, hmem, ?_⟩
  intro n t ht
  obtain ⟨u,w,hc,hlen,rfl⟩ := ht
  have hlo := hc.three_le_length
  have hhi := hc.isTrail.length_le_card_edgeFinset
  have he : (SimpleGraph.cycleGraph 3).edgeFinset.card = 3 := by decide
  rw [he] at hhi
  have hlen3 : w.length = 3 := by omega
  have : w.edges.toFinset ∈ cycleEdgeSets (SimpleGraph.cycleGraph 3) 3 :=
    ⟨u,w,hc,hlen3,rfl⟩
  rw [← finiteCycleEdges_eq, hs] at this
  exact Finset.mem_singleton.mp this
#print axioms Paper7StatementTestsV3.test091

theorem test092 : BackfillPaper7.BoundaryTestRequirements.test_092 := by
  rintro ⟨_,s,_,hall⟩
  have hle : (finiteCycleEdges (⊤ : SimpleGraph (Fin 4)) 3).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : a ∈ cycleEdgeSets (⊤ : SimpleGraph (Fin 4)) 3 := by
      rw [← finiteCycleEdges_eq]
      exact ha
    have hb' : b ∈ cycleEdgeSets (⊤ : SimpleGraph (Fin 4)) 3 := by
      rw [← finiteCycleEdges_eq]
      exact hb
    exact (hall 3 a ha').trans (hall 3 b hb').symm
  have hcard : (finiteCycleEdges (⊤ : SimpleGraph (Fin 4)) 3).card = 4 := by decide +kernel
  omega
#print axioms Paper7StatementTestsV3.test092

end Paper7StatementTestsV3
