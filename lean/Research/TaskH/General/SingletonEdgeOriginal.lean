import Research.TaskH.General.EqualityEdgeOriginal

/-!
The first actual singleton-donor bridge. The singleton condition refers
only to the real neighbors of v in one fixed coloring of the whole G-v.
The edge-deleted coloring is constructed internally on the whole original
vertex type. No coloring of an auxiliary graph or supplying cycle is input.
Retention of a second singleton and ordered-list path extraction remain
separate, unproved debts; this file does not assert the minimum-degree bound.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def singletonEdgeColoring {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a) :
    (G.deleteEdges {s(v, a)}).Coloring (Fin k) := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun z => if hz : z = v then c ⟨a, hva.ne.symm⟩ else c ⟨z, hz⟩) ?_
  intro x y hxy
  have hG : G.Adj x y := (SimpleGraph.deleteEdges_adj.mp hxy).1
  have hnot : s(x, y) ∉ ({s(v, a)} : Set (Sym2 V)) :=
    (SimpleGraph.deleteEdges_adj.mp hxy).2
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := hG.ne.symm
    simp only [dite_eq_right hy]
    intro he
    have hya : y = a := hunique y hy hG he.symm
    exact hnot (Set.mem_singleton_iff.mpr (congrArg (fun z : V => s(v, z)) hya))
  · by_cases hy : y = v
    · subst y
      simp only [dite_eq_right hx]
      intro he
      have hxa : x = a := hunique x hx hG.symm he
      exact hnot (Set.mem_singleton_iff.mpr
        ((congrArg (fun z : V => s(z, v)) hxa).trans Sym2.eq_swap))
    · simp only [dite_eq_right hx, dite_eq_right hy]
      exact c.valid hG

omit [Fintype V] in
theorem singletonEdgeColoring_root {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a) :
    singletonEdgeColoring hva c hunique v = c ⟨a, hva.ne.symm⟩ := by
  classical
  change (if hz : v = v then c ⟨a, hva.ne.symm⟩ else c ⟨v, hz⟩) = c ⟨a, hva.ne.symm⟩
  exact dite_eq_left rfl

omit [Fintype V] in
theorem singletonEdgeColoring_outside {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (z : V) (hz : z ≠ v) :
    singletonEdgeColoring hva c hunique z = c ⟨z, hz⟩ := by
  classical
  change (if hzv : z = v then c ⟨a, hva.ne.symm⟩ else c ⟨z, hzv⟩) = c ⟨z, hz⟩
  exact dite_eq_right hz

/-- Every chosen color order supplies an actual original k-cycle at v,
avoiding the singleton neighbor, with precisely the original colors outside
v and the singleton color assigned to v. No donor family is assumed. -/
theorem equality_original_singleton_ordered_cycle (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (π : Equiv.Perm (Fin k)) :
    ∃ q : G.Walk v v, q.IsCycle ∧ q.length = k ∧
      Follows q (fun z => π (singletonEdgeColoring hva c hunique z)) (finRotate k) ∧
      a ∉ q.support ∧
      singletonEdgeColoring hva c hunique v = c ⟨a, hva.ne.symm⟩ ∧
      ∀ (z : V) (hz : z ≠ v), singletonEdgeColoring hva c hunique z = c ⟨z, hz⟩ := by
  obtain ⟨q, hq, hql, hqf, ha⟩ := equality_original_edge_ordered_cycle hk hcrit hcount
    hva (singletonEdgeColoring hva c hunique) π
  exact ⟨q, hq, hql, hqf, ha, singletonEdgeColoring_root hva c hunique,
    singletonEdgeColoring_outside hva c hunique⟩

end TaskH.General

#print axioms TaskH.General.singletonEdgeColoring
#print axioms TaskH.General.singletonEdgeColoring_root
#print axioms TaskH.General.singletonEdgeColoring_outside
#print axioms TaskH.General.equality_original_singleton_ordered_cycle
