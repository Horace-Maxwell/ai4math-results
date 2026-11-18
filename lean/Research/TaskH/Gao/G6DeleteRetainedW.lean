import Research.TaskH.Gao.G6ComponentAttachment
import Research.TaskH.Gao.OneRootExtension

/-! The actual retained w is deleted; u and the fresh contracted root remain.
The added test edge is u--fresh-none, never a fabricated u--w edge. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def g6ActualTestGraph (G : SimpleGraph V) (A B : Set V) (y u w : V) :
    SimpleGraph (G6Vertex (g6SelectedRegion G A B y w)) :=
  g6Graph G (g6SelectedRegion G A B y w) A u w ⊔
    SimpleGraph.edge (some (Sum.inr false)) none

def g6ComponentIntoDeleteW (G : SimpleGraph V) (A B : Set V) (y w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C) (v : C.supp) :
    {q : G6Vertex (g6SelectedRegion G A B y w) // q ≠ some (Sum.inr true)} :=
  ⟨some (Sum.inl (g6ComponentPoint G A B y w C hC v)), by
    intro he
    cases Option.some.inj he⟩

def g6ComponentDeleteWHom (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C) :
    C.toSimpleGraph →g (g6ActualTestGraph G A B y u w).induce
      {q | q ≠ some (Sum.inr true)} where
  toFun := g6ComponentIntoDeleteW G A B y w C hC
  map_rel' := by
    intro a b e
    change G.Adj a.1.1 b.1.1 ∨ _
    exact Or.inl e

theorem g6_delete_retained_w_connected_of_actual_component_matchings
    (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (hMatching : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C) :
    ((g6ActualTestGraph G A B y u w).induce
      {q | q ≠ some (Sum.inr true)}).Connected := by
  let H : Set V := g6SelectedRegion G A B y w
  let D : SimpleGraph {q : G6Vertex H // q ≠ some (Sum.inr true)} :=
    (g6ActualTestGraph G A B y u w).induce {q | q ≠ some (Sum.inr true)}
  let RT : {q : G6Vertex H // q ≠ some (Sum.inr true)} :=
    ⟨none, by intro he; cases he⟩
  let RU : {q : G6Vertex H // q ≠ some (Sum.inr true)} :=
    ⟨some (Sum.inr false), by
      intro he
      have hb : (false : Bool) = true := Sum.inr.inj (Option.some.inj he)
      cases hb⟩
  have eUT : D.Adj RU RT := by
    change (g6Graph G H A u w).Adj (some (Sum.inr false)) none ∨
      (SimpleGraph.edge (some (Sum.inr false)) none).Adj (some (Sum.inr false)) none
    right
    apply (SimpleGraph.edge_adj (some (Sum.inr false)) none (some (Sum.inr false)) none).mpr
    exact ⟨Or.inl ⟨rfl, rfl⟩, by intro he; cases he⟩
  have hto : ∀ p : {q : G6Vertex H // q ≠ some (Sum.inr true)}, D.Reachable p RT := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact Reachable.rfl
    | some q =>
      cases q with
      | inr b =>
        cases b with
        | false => exact eUT.reachable
        | true => exact False.elim (hq rfl)
      | inl h =>
        obtain ⟨hv, C, hvC, t, htC, ewt⟩ :=
          (g6Selected_iff_actual_component G A B y w h.1).mp h.2
        let c : C.supp := ⟨⟨h.1, hv⟩, hvC⟩
        have hC : g6ComponentTouches G A B y w C := ⟨⟨t, htC⟩, ewt⟩
        obtain ⟨d, _e, a, _b, ha, _hb, _hde, _hab, eda, _eeb⟩ := hMatching C hC
        let f := g6ComponentDeleteWHom G A B y u w C hC
        have hr : D.Reachable (f c) (f d) := (C.connected_toSimpleGraph c d).map f
        have hec : f c = (⟨some (Sum.inl h), hq⟩ : {q : G6Vertex H // q ≠ some (Sum.inr true)}) := by
          apply Subtype.ext
          exact congrArg (fun z : H => some (Sum.inl z)) (Subtype.ext rfl)
        by_cases hau : a = u
        · have ed : D.Adj (f d) RU := by
            change G.Adj d.1.1 u ∨ _
            exact Or.inl (Eq.mp (congrArg (fun z : V => G.Adj d.1.1 z) hau) eda)
          exact Eq.mp (congrArg (fun z => D.Reachable z RT) hec)
            (hr.trans (ed.reachable.trans eUT.reachable))
        · have ed : D.Adj (f d) RT := by
            change (∃ a ∈ g6Boundary G H A u, G.Adj d.1.1 a) ∨ _
            exact Or.inl ⟨a, ⟨ha, hau, d.1.1,
              (g6ComponentPoint G A B y w C hC d).2, eda.symm⟩, eda⟩
          exact Eq.mp (congrArg (fun z => D.Reachable z RT) hec) (hr.trans ed.reachable)
  refine { preconnected := ?_, nonempty := ⟨RT⟩ }
  intro p q
  exact (hto p).trans (hto q).symm

theorem g6_actual_test_connected_of_actual_component_matchings
    (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (hu : u ∈ A) (hw : w ∈ B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hMatching : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C) :
    (g6ActualTestGraph G A B y u w).Connected := by
  let H : Set V := g6SelectedRegion G A B y w
  let K := g6ActualTestGraph G A B y u w
  let W : G6Vertex H := some (Sum.inr true)
  let U : {q : G6Vertex H // q ≠ W} := ⟨some (Sum.inr false), by
    intro he
    have hb : (false : Bool) = true := Sum.inr.inj (Option.some.inj he)
    cases hb⟩
  have hdel : (K.induce {q | q ≠ W}).Connected :=
    g6_delete_retained_w_connected_of_actual_component_matchings G A B y u w hMatching
  refine connected_of_one_extra_vertex (K.induce {q | q ≠ W}) K W Subtype.val hdel ?_ ?_ U ?_
  · intro a b e
    exact e
  · intro p
    by_cases hp : p = W
    · exact Or.inl hp
    · exact Or.inr ⟨⟨p, hp⟩, rfl⟩
  · change (g6Graph G H A u w).Adj (some (Sum.inr true)) (some (Sum.inr false)) ∨ _
    exact Or.inl (hcross u hu w hw).symm

#print axioms g6ActualTestGraph
#print axioms g6ComponentIntoDeleteW
#print axioms g6ComponentDeleteWHom
#print axioms g6_delete_retained_w_connected_of_actual_component_matchings
#print axioms g6_actual_test_connected_of_actual_component_matchings
end TaskH.Gao
