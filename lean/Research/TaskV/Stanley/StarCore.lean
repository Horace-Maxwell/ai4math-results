import Research.TaskV.Stanley.StarBasics

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {n : ℕ} {G : SimpleGraph (Fin n)}

abbrev coreGraph (G : SimpleGraph (Fin n)) := G.induce (core G : Set (Fin n))

theorem starCenter_edge (hG : G.Connected) (hc : (core G).Nonempty)
    {x y : Fin n} (adj : G.Adj x y) :
    starCenter hG hc x = starCenter hG hc y ∨
      (coreGraph G).Adj (starCenter hG hc x) (starCenter hG hc y) := by
  classical
  by_cases hx : x ∈ core G
  · have xeq := starCenter_core hG hc ⟨x,hx⟩
    by_cases hy : y ∈ core G
    · have yeq := starCenter_core hG hc ⟨y,hy⟩
      right
      rw [xeq,yeq]
      exact adj
    · left
      rw [xeq]
      exact (Subtype.ext (starCenter_leaf_eq hG hc hy adj.symm)).symm
  · have hy := leaf_neighbor_in_core hG hc hx adj
    have yeq := starCenter_core hG hc ⟨y,hy⟩
    left
    rw [yeq]
    exact Subtype.ext (starCenter_leaf_eq hG hc hx adj)

theorem coreGraph_tree (hG : G.IsTree) (hc : (core G).Nonempty) :
    (coreGraph G).IsTree := by
  refine ⟨(SimpleGraph.connected_iff _).mpr ⟨?_,hc.to_subtype⟩,hG.isAcyclic.induce _⟩
  intro x y
  let c := starCenter hG.connected hc
  let p := fun v : Fin n => (coreGraph G).Reachable x (c v)
  have start : p x := by simp [p,c]
  have step : ∀ a b, p a → G.Adj a b → p b := by
    intro a b ha ab
    rcases starCenter_edge hG.connected hc ab with e | e
    · change (coreGraph G).Reachable x (starCenter hG.connected hc b)
      rw [← e]
      exact ha
    · exact ha.trans e.reachable
  simpa [p,c] using reachable_closed p (hG.connected.preconnected x y) start step

/-- Lift a set of core vertices by taking the entire star of each of its members. -/
def expandedCoreSet (hG : G.Connected) (hc : (core G).Nonempty) (s : Finset ↥(core G)) :
    Finset (Fin n) := by classical exact univ.filter fun x => starCenter hG hc x ∈ s

@[simp] theorem mem_expandedCoreSet (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) (x : Fin n) :
    x ∈ expandedCoreSet hG hc s ↔ starCenter hG hc x ∈ s := by
  classical simp [expandedCoreSet]

theorem card_expandedCoreSet (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) :
    (expandedCoreSet hG hc s).card = ∑ c ∈ s, coreWeight G c := by
  classical
  unfold expandedCoreSet
  rw [← sum_card_fiberwise_eq_card_filter]
  apply sum_congr rfl
  intro c _
  rw [← starCenter_fiber_card hG hc c,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem preconnected_of_centers (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) :
    (G.induce (expandedCoreSet hG hc s : Set (Fin n))).Preconnected ↔
      ((coreGraph G).induce (s : Set ↥(core G))).Preconnected := by
  classical
  let S := (expandedCoreSet hG hc s : Set (Fin n))
  let T := (s : Set ↥(core G))
  let f : S → T := fun x => ⟨starCenter hG hc x, (mem_expandedCoreSet ..).mp x.property⟩
  let g : T → S := fun c => ⟨c.val.val, (mem_expandedCoreSet ..).mpr
    (by simp)⟩
  have fg (v : T) : f (g v) = v := Subtype.ext (starCenter_core hG hc v.val)
  let incl : (coreGraph G).induce T →g G.induce S :=
    { toFun := g, map_rel' := fun hab => hab }
  have stay (x : S) : (G.induce S).Reachable x (g (f x)) := by
    rcases (starCenter_iff hG hc x (starCenter hG hc x)).mp rfl with he | he
    · have h : x = g (f x) := Subtype.ext he
      exact h ▸ (show (G.induce S).Reachable x x from .rfl)
    · exact SimpleGraph.Adj.reachable (show (G.induce S).Adj x (g (f x)) from he.2)
  constructor
  · intro h x y
    let P : S → Prop := fun v => ((coreGraph G).induce T).Reachable x (f v)
    have start : P (g x) := by simp [P,fg]
    have out := reachable_closed P (h (g x) (g y)) start (by
      intro a b ha ab
      rcases starCenter_edge hG hc (show G.Adj a b from ab) with he | he
      · have eq : f a = f b := Subtype.ext he
        change ((coreGraph G).induce T).Reachable x (f b)
        rw [← eq]
        exact ha
      · exact ha.trans (SimpleGraph.Adj.reachable (show ((coreGraph G).induce T).Adj (f a) (f b) from he)))
    simpa [P,fg] using out
  · intro h x y
    exact (stay x).trans (((h (f x) (f y)).map incl).trans (stay y).symm)

theorem connected_of_centers (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) :
    (G.induce (expandedCoreSet hG hc s : Set (Fin n))).Connected ↔
      ((coreGraph G).induce (s : Set ↥(core G))).Connected := by
  classical
  rw [SimpleGraph.connected_iff,SimpleGraph.connected_iff,preconnected_of_centers]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨x⟩
    exact ⟨⟨starCenter hG hc x,(mem_expandedCoreSet ..).mp x.property⟩⟩
  · rintro ⟨x⟩
    refine ⟨⟨x.val.val,(mem_expandedCoreSet ..).mpr ?_⟩⟩
    simp

end
end StanleyContinuation
