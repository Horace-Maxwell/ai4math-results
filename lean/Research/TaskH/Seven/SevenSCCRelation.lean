import Research.TaskH.Seven.SevenSCCRainbow
import Research.TaskH.Seven.CycleSeven
import Research.TaskH.Seven.EdgeColorOrders

/-! Actual mutual-reachability components, represented by deduplicated
finite vertex sets. No Quiver instance or component coverage premise. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def SuccessorEquivalent (G : SimpleGraph V) (c : V → Fin 7)
    (σ : Equiv.Perm (Fin 7)) (a b : V) : Prop :=
  Relation.ReflTransGen (ColorStep G c σ) a b ∧
    Relation.ReflTransGen (ColorStep G c σ) b a

theorem successorEquivalent_refl (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) (a : V) :
    SuccessorEquivalent G c σ a a :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem successorEquivalent_symm {c : V → Fin 7} {σ : Equiv.Perm (Fin 7)}
    {a b : V} (h : SuccessorEquivalent G c σ a b) :
    SuccessorEquivalent G c σ b a := ⟨h.2, h.1⟩

theorem successorEquivalent_trans {c : V → Fin 7} {σ : Equiv.Perm (Fin 7)}
    {a b d : V} (hab : SuccessorEquivalent G c σ a b)
    (hbd : SuccessorEquivalent G c σ b d) : SuccessorEquivalent G c σ a d :=
  ⟨hab.1.trans hbd.1, hbd.2.trans hab.2⟩

noncomputable def successorComponent [Fintype V] (G : SimpleGraph V)
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter (SuccessorEquivalent G c σ a)

theorem mem_successorComponent [Fintype V] (c : V → Fin 7)
    (σ : Equiv.Perm (Fin 7)) (a b : V) :
    b ∈ successorComponent G c σ a ↔ SuccessorEquivalent G c σ a b := by
  simp [successorComponent]

theorem successorComponent_self [Fintype V] (c : V → Fin 7)
    (σ : Equiv.Perm (Fin 7)) (a : V) : a ∈ successorComponent G c σ a :=
  (mem_successorComponent c σ a a).mpr (successorEquivalent_refl c σ a)

theorem successorComponent_eq_of_equivalent [Fintype V]
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) {a b : V}
    (hab : SuccessorEquivalent G c σ a b) :
    successorComponent G c σ a = successorComponent G c σ b := by
  ext z
  rw [mem_successorComponent, mem_successorComponent]
  constructor
  · intro haz
    exact successorEquivalent_trans (successorEquivalent_symm hab) haz
  · intro hbz
    exact successorEquivalent_trans hab hbz

noncomputable def successorComponents [Fintype V] (G : SimpleGraph V)
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) : Finset (Finset V) := by
  classical
  exact Finset.univ.image (successorComponent G c σ)

theorem successorComponents_pairwiseDisjoint [Fintype V]
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) :
    (successorComponents G c σ : Set (Finset V)).PairwiseDisjoint id := by
  classical
  intro A hA B hB hne
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hB
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  have haz := (mem_successorComponent c σ a z).mp hza
  have hbz := (mem_successorComponent c σ b z).mp hzb
  have hab := successorEquivalent_trans haz (successorEquivalent_symm hbz)
  exact hne (successorComponent_eq_of_equivalent c σ hab)

theorem successorComponents_biUnion [Fintype V]
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) :
    (successorComponents G c σ).biUnion id = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro a
  apply Finset.mem_biUnion.mpr
  refine ⟨successorComponent G c σ a, ?_, successorComponent_self c σ a⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

theorem sum_successorComponent_card [Fintype V]
    (c : V → Fin 7) (σ : Equiv.Perm (Fin 7)) :
    (∑ Q ∈ successorComponents G c σ, Q.card) = Fintype.card V := by
  classical
  have h := Finset.card_biUnion (successorComponents_pairwiseDisjoint (G := G) c σ)
  rw [successorComponents_biUnion] at h
  simpa using h.symm

theorem orderedColorCycle_fullOrbit (π : Equiv.Perm (Fin 7))
    (a b : Fin 7) : ∃ n : ℕ, (orderedColorCycle π ^ n) a = b := by
  obtain ⟨r, hr⟩ := rotate_seven_orbit_surjective (π a) (π b)
  have hpow : ∀ n : ℕ, π ((orderedColorCycle π ^ n) a) =
      ((finRotate 7) ^ n) (π a) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply, orderedColorCycle_apply, ih]
  refine ⟨r.val, π.injective ?_⟩
  exact (hpow r.val).trans hr

theorem cycleSevenVertices_covers {z : V} (p : G.Walk z z)
    (hl : p.length = 7) {a : V} (ha : a ∈ p.support) :
    ∃ i : Fin 7, cycleSevenVertices p i = a := by
  obtain ⟨n, hn, hna⟩ := List.mem_iff_getElem.mp ha
  have hn' : n ≤ p.length := by
    rw [Walk.length_support] at hn
    omega
  have hget : p.getVert n = a := (p.getVert_eq_support_getElem hn').trans hna
  by_cases hn7 : n = 7
  · refine ⟨0, ?_⟩
    have hend : p.getVert 7 = z := by simpa only [hl] using p.getVert_length
    change p.getVert 0 = a
    rw [Walk.getVert_zero]
    exact hend.symm.trans (hn7 ▸ hget)
  · exact ⟨⟨n, by omega⟩, hget⟩

/-- Every actual nonbad circle lies in one component, for every rank order. -/
theorem nonbad_cycle_successorEquivalent (hr : RainbowSevenCycles G)
    {x y z : V} (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hav : x ∉ p.support ∨ y ∉ p.support)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {a b : V} (ha : a ∈ p.support)
    (hb : b ∈ p.support) :
    SuccessorEquivalent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a b := by
  obtain ⟨i, hi⟩ := cycleSevenVertices_covers p hl ha
  obtain ⟨j, hj⟩ := cycleSevenVertices_covers p hl hb
  have hf := cycleSevenVertices_injective hp hl
  have hm : ∀ i : Fin 7, cycleSevenVertices p i ∈ p.support :=
    fun i => p.getVert_mem_support i.val
  have hab := deletedEdge_trace_reachable hr p hp hl hav (cycleSevenVertices p)
    hf hm c (orderedColorCycle π) (orderedColorCycle_fullOrbit π) i j
  have hba := deletedEdge_trace_reachable hr p hp hl hav (cycleSevenVertices p)
    hf hm c (orderedColorCycle π) (orderedColorCycle_fullOrbit π) j i
  exact ⟨by simpa only [hi, hj] using hab, by simpa only [hi, hj] using hba⟩

end TaskH.Seven

#print axioms TaskH.Seven.SuccessorEquivalent
#print axioms TaskH.Seven.successorEquivalent_refl
#print axioms TaskH.Seven.successorEquivalent_symm
#print axioms TaskH.Seven.successorEquivalent_trans
#print axioms TaskH.Seven.successorComponent
#print axioms TaskH.Seven.mem_successorComponent
#print axioms TaskH.Seven.successorComponent_self
#print axioms TaskH.Seven.successorComponent_eq_of_equivalent
#print axioms TaskH.Seven.successorComponents
#print axioms TaskH.Seven.successorComponents_pairwiseDisjoint
#print axioms TaskH.Seven.successorComponents_biUnion
#print axioms TaskH.Seven.sum_successorComponent_card
#print axioms TaskH.Seven.orderedColorCycle_fullOrbit
#print axioms TaskH.Seven.cycleSevenVertices_covers
#print axioms TaskH.Seven.nonbad_cycle_successorEquivalent
