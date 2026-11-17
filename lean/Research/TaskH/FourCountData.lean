import Research.TaskH.Basics

/-!
Four-cycle data used for the common-neighbour double count.
The representation below retains a starting point and direction temporarily;
its map to the frozen, undirected edge-set representation has fibres of size
at most eight. No enumeration of graphs is used.
-/

universe u

namespace TaskH.FourCount

open SimpleGraph

variable {V : Type u}

def quadEdges [DecidableEq V] (f : Fin 4 → V) : Finset (Sym2 V) :=
  {s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 0)}

def IsQuad (G : SimpleGraph V) (f : Fin 4 → V) : Prop :=
  Function.Injective f ∧ G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
    G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 0)

def quadWalk (G : SimpleGraph V) (f : Fin 4 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h30 : G.Adj (f 3) (f 0)) :
    G.Walk (f 0) (f 0) :=
  .cons h01 (.cons h12 (.cons h23 (.cons h30 .nil)))

theorem quadWalk_isCycle (G : SimpleGraph V) (f : Fin 4 → V)
    (hf : Function.Injective f)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h30 : G.Adj (f 3) (f 0)) :
    (quadWalk G f h01 h12 h23 h30).IsCycle := by
  rw [quadWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hf.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hf.eq_iff]

theorem quadWalk_edges [DecidableEq V] (G : SimpleGraph V) (f : Fin 4 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h30 : G.Adj (f 3) (f 0)) :
    (quadWalk G f h01 h12 h23 h30).edges.toFinset = quadEdges f := by
  simp [quadWalk, quadEdges, Walk.edges_cons]

theorem quadEdges_card [DecidableEq V] (G : SimpleGraph V) (f : Fin 4 → V)
    (hf : IsQuad G f) : (quadEdges f).card = 4 := by
  rw [← quadWalk_edges G f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2]
  rw [Basics.cycle_edges_toFinset_card
    (quadWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)]
  rfl

theorem quadEdges_mem_modCycleEdgeSets [DecidableEq V] (G : SimpleGraph V)
    (f : Fin 4 → V) (hf : IsQuad G f) :
    quadEdges f ∈ Challenge.ModCycleEdgeSets 4 G := by
  apply Basics.mem_modCycleEdgeSets_iff.mpr
  refine ⟨f 0, quadWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2,
    quadWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2,
    quadWalk_edges G f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2, ?_⟩
  exact dvd_refl 4

theorem image_quadEdges [DecidableEq V] {W : Type*} [DecidableEq W]
    (g : V → W) (f : Fin 4 → V) :
    (quadEdges f).image (Sym2.map g) = quadEdges (g ∘ f) := by
  simp [quadEdges]

/-- The eight possible starts and directions of the fixed four-cycle. -/
def fourReindexings : Finset (Fin 4 → Fin 4) :=
  Finset.univ.filter fun f => Function.Injective f ∧ quadEdges f = quadEdges id

theorem fourReindexings_card : fourReindexings.card = 8 := by
  decide +kernel

theorem range_of_quadEdges_eq [DecidableEq V] {f q : Fin 4 → V}
    (he : quadEdges f = quadEdges q) (i : Fin 4) : ∃ j, q j = f i := by
  have hmem : s(f i, f (i + 1)) ∈ quadEdges f := by
    fin_cases i <;> simp [quadEdges]
  rw [he] at hmem
  simp only [quadEdges, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;>
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  all_goals rcases h with h | h
  · exact ⟨0, h.1.symm⟩
  · exact ⟨1, h.1.symm⟩
  · exact ⟨1, h.1.symm⟩
  · exact ⟨2, h.1.symm⟩
  · exact ⟨2, h.1.symm⟩
  · exact ⟨3, h.1.symm⟩
  · exact ⟨3, h.1.symm⟩
  · exact ⟨0, h.1.symm⟩

noncomputable def quadCoordinates (q f : Fin 4 → V) : Fin 4 → Fin 4 :=
  fun i => Function.invFun q (f i)

theorem quadCoordinates_spec [DecidableEq V] {f q : Fin 4 → V}
    (he : quadEdges f = quadEdges q) (i : Fin 4) :
    q (quadCoordinates q f i) = f i :=
  Function.invFun_eq (range_of_quadEdges_eq he i)

theorem quadCoordinates_mem [DecidableEq V] {f q : Fin 4 → V}
    (hf : Function.Injective f) (hq : Function.Injective q)
    (he : quadEdges f = quadEdges q) :
    quadCoordinates q f ∈ fourReindexings := by
  have hs := quadCoordinates_spec he
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i j h
    apply hf
    rw [← hs i, ← hs j, h]
  · apply Finset.image_injective (Sym2.map.injective hq)
    rw [image_quadEdges, image_quadEdges]
    have hcomp : q ∘ quadCoordinates q f = f := funext hs
    simpa only [hcomp, Function.comp_id] using he

theorem quadCoordinates_injective [DecidableEq V] (q : Fin 4 → V)
    {f g : Fin 4 → V} (hf : quadEdges f = quadEdges q)
    (hg : quadEdges g = quadEdges q)
    (h : quadCoordinates q f = quadCoordinates q g) : f = g := by
  funext i
  rw [← quadCoordinates_spec hf i, ← quadCoordinates_spec hg i, h]

noncomputable def quadWords [Fintype V] (G : SimpleGraph V) : Finset (Fin 4 → V) := by
  classical
  exact Finset.univ.filter (IsQuad G)

/-- Each undirected four-cycle edge set has at most eight ordered witnesses. -/
theorem quadWords_fiber_card_le [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Finset (Sym2 V)) :
    ((quadWords G).filter fun f => quadEdges f = s).card ≤ 8 := by
  classical
  let T := (quadWords G).filter fun f => quadEdges f = s
  by_cases hT : T.Nonempty
  · obtain ⟨q, hq⟩ := hT
    have hqinj : Function.Injective q :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hqe : quadEdges q = s := (Finset.mem_filter.mp hq).2
    calc
      T.card ≤ fourReindexings.card := by
        apply Finset.card_le_card_of_injOn (quadCoordinates q)
        · intro f hf
          have hfinj : Function.Injective f :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2.1
          exact quadCoordinates_mem hfinj hqinj ((Finset.mem_filter.mp hf).2.trans hqe.symm)
        · intro f hf g hg hfg
          exact quadCoordinates_injective q
            ((Finset.mem_filter.mp hf).2.trans hqe.symm)
            ((Finset.mem_filter.mp hg).2.trans hqe.symm) hfg
      _ = 8 := fourReindexings_card
  · change T.card ≤ 8
    rw [Finset.not_nonempty_iff_eq_empty.mp hT]
    simp only [Finset.card_empty]
    exact Nat.zero_le 8

/-- Ordered four-cycles map to genuine modulo-four cycles in the frozen count. -/
theorem quadWords_card_le_eight_mul_modCycleCount [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (quadWords G).card ≤ 8 * Challenge.modCycleCount 4 G := by
  classical
  let C := (Basics.modCycleEdgeSets_finite 4 G).toFinset
  have hmap : ∀ f ∈ quadWords G, quadEdges f ∈ C := by
    intro f hf
    apply (Basics.modCycleEdgeSets_finite 4 G).mem_toFinset.mpr
    exact quadEdges_mem_modCycleEdgeSets G f (Finset.mem_filter.mp hf).2
  calc
    (quadWords G).card = ∑ s ∈ C, ((quadWords G).filter fun f => quadEdges f = s).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _s ∈ C, 8 := Finset.sum_le_sum fun s _ => quadWords_fiber_card_le G s
    _ = 8 * C.card := by simp [Nat.mul_comm]
    _ = 8 * Challenge.modCycleCount 4 G := by
      rw [Challenge.modCycleCount, Set.ncard_eq_toFinset_card]

end TaskH.FourCount

#print axioms TaskH.FourCount.quadWalk_isCycle
#print axioms TaskH.FourCount.quadEdges_mem_modCycleEdgeSets
#print axioms TaskH.FourCount.fourReindexings_card
#print axioms TaskH.FourCount.quadWords_fiber_card_le
#print axioms TaskH.FourCount.quadWords_card_le_eight_mul_modCycleCount
