import Research.TaskH.EdgeCyclesCount
import Research.TaskH.CycleFourWitness
import Research.TaskH.Degree
import Research.TaskH.FiniteBudget

/-!
Actual vertex-cycle incidence in the frozen modulo-four edge-set collection.
Every vertex lies on at least four cycles, while ShortFourCycles gives exactly
four vertices on each counted cycle. Their double count bounds the vertex set.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def modCyclesThrough (k : ℕ) (G : SimpleGraph V) (x : V) :
    Set (Finset (Sym2 V)) :=
  {s | s ∈ ModCycleEdgeSets k G ∧ CycleContains s x}

theorem modCyclesThrough_finite [Finite V] (k : ℕ) (G : SimpleGraph V) (x : V) :
    (modCyclesThrough k G x).Finite :=
  (Basics.modCycleEdgeSets_finite k G).subset (fun _ hs => hs.1)

/-- Choose a genuine cycle through v, then use its first neighbor to obtain
three other cycles avoiding that neighbor. The chosen cycle is the fourth. -/
theorem four_le_modCyclesThrough [Fintype V]
    (h : IsCriticalPlus 4 G) (hs : ShortFourCycles G) (v : V) :
    4 ≤ (modCyclesThrough 4 G v).ncard := by
  classical
  have hd := critical_degree_ge h v
  have hpos : 0 < (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  obtain ⟨P, hP, _⟩ := critical_edge_three_cycle_witnesses h hs hvw
  let p : G.Walk v v := P 0
  have hp : p.IsCycle := (hP 0).1
  have hl : p.length = 4 := (hP 0).2.1
  let z : V := p.snd
  have hvz : G.Adj v z := p.adj_snd hp.not_nil
  let C : Finset (Sym2 V) := p.edges.toFinset
  have hC : C ∈ modCyclesThrough 4 G v := by
    refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
    · simpa only [hl] using (dvd_refl 4)
    · exact (cycleContains_edges_toFinset_iff p hp.not_nil v).mpr p.start_mem_support
  have hCz : CycleContains C z :=
    (cycleContains_edges_toFinset_iff p hp.not_nil z).mpr (p.getVert_mem_support 1)
  let A := modCyclesThroughAvoid 4 G v z
  have hA : A.Finite :=
    (Basics.modCycleEdgeSets_finite 4 G).subset (fun _ hmem => hmem.1)
  have hnot : C ∉ A := by
    intro hmem
    exact hmem.2.2 hCz
  have hthree : 3 ≤ A.ncard := critical_edge_three_modCyclesThroughAvoid h hs hvz
  have hsub : insert C A ⊆ modCyclesThrough 4 G v := by
    intro s hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact hC
    · exact ⟨hmem.1, hmem.2.1⟩
  have hle := Set.ncard_le_ncard hsub (modCyclesThrough_finite 4 G v)
  rw [Set.ncard_insert_of_notMem hnot hA] at hle
  omega

noncomputable def cycleVertices [Fintype V] (s : Finset (Sym2 V)) : Finset V := by
  classical
  exact Finset.univ.filter (CycleContains s)

theorem mem_cycleVertices [Fintype V] (s : Finset (Sym2 V)) (v : V) :
    v ∈ cycleVertices s ↔ CycleContains s v := by
  classical
  simp [cycleVertices]

theorem cycleContains_quadEdges_iff [DecidableEq V] (f : Fin 4 → V) (v : V) :
    CycleContains (FourCount.quadEdges f) v ↔ ∃ i : Fin 4, f i = v := by
  constructor
  · rintro ⟨e, he, hve⟩
    simp only [FourCount.quadEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    all_goals simp only [Sym2.mem_iff] at hve
    · rcases hve with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · rcases hve with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases hve with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
    · rcases hve with h | h
      · exact ⟨3, h.symm⟩
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [CycleContains, FourCount.quadEdges]

theorem cycleVertices_quadEdges [Fintype V] [DecidableEq V] (f : Fin 4 → V) :
    cycleVertices (FourCount.quadEdges f) = Finset.univ.image f := by
  classical
  ext v
  simp only [mem_cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  exact cycleContains_quadEdges_iff f v

theorem cycleVertices_quadEdges_card [Fintype V] [DecidableEq V]
    (f : Fin 4 → V) (hf : Function.Injective f) :
    (cycleVertices (FourCount.quadEdges f)).card = 4 := by
  rw [cycleVertices_quadEdges, Finset.card_image_of_injective _ hf,
    Finset.card_univ, Fintype.card_fin]

/-- The four vertices are proved from a genuine cycle witness, not supplied
as a coverage hypothesis for the edge-set representation. -/
theorem cycleVertices_card_four_of_mem [Fintype V] (hs : ShortFourCycles G)
    {s : Finset (Sym2 V)} (hmem : s ∈ ModCycleEdgeSets 4 G) :
    (cycleVertices s).card = 4 := by
  classical
  obtain ⟨x, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := FourCount.exists_quad_of_cycle_length_four hp hl
  rw [← he, ← hfe]
  exact cycleVertices_quadEdges_card f hf.1

/-- The equality hypotheses force at most fifteen actual vertices at k=4. -/
theorem card_le_fifteen_of_short_critical_count [Fintype V]
    (h : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (hc : modCycleCount 4 G = 15) : Fintype.card V ≤ 15 := by
  classical
  let C : Finset (Finset (Sym2 V)) := (Basics.modCycleEdgeSets_finite 4 G).toFinset
  have hC : C.card = 15 := by
    calc
      C.card = (ModCycleEdgeSets 4 G).ncard :=
        (Set.ncard_eq_toFinset_card _ (Basics.modCycleEdgeSets_finite 4 G)).symm
      _ = 15 := hc
  have hrow : ∀ v : V, 4 ≤ (C.filter (fun s => CycleContains s v)).card := by
    intro v
    have he : modCyclesThrough 4 G v =
        ((C.filter (fun s => CycleContains s v) : Finset (Finset (Sym2 V))) :
          Set (Finset (Sym2 V))) := by
      ext s
      simp [modCyclesThrough, C]
    have hv := four_le_modCyclesThrough h hs v
    rwa [he, Set.ncard_coe_finset] at hv
  have hcol : ∀ s ∈ C,
      ((Finset.univ : Finset V).filter (fun v => CycleContains s v)).card = 4 := by
    intro s hmem
    change (cycleVertices s).card = 4
    exact cycleVertices_card_four_of_mem hs
      ((Basics.modCycleEdgeSets_finite 4 G).mem_toFinset.mp hmem)
  have hsum := FiniteBudget.relation_double_count (Finset.univ : Finset V) C
    (fun v s => CycleContains s v)
  have hbound : 4 * Fintype.card V ≤ 60 := by
    calc
      4 * Fintype.card V = ∑ _v : V, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : V, (C.filter (fun s => CycleContains s v)).card :=
        Finset.sum_le_sum (fun v _ => hrow v)
      _ = ∑ s ∈ C, ((Finset.univ : Finset V).filter (fun v => CycleContains s v)).card := hsum
      _ = ∑ _s ∈ C, 4 := Finset.sum_congr rfl hcol
      _ = 60 := by simp [hC]
  omega

end TaskH

#print axioms TaskH.four_le_modCyclesThrough
#print axioms TaskH.cycleVertices_card_four_of_mem
#print axioms TaskH.card_le_fifteen_of_short_critical_count
