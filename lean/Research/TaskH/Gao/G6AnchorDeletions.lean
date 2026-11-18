import Research.TaskH.Gao.G6DeleteRetainedW

/-! Actual component homomorphisms into actual deleted test graphs. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def g6ComponentDeletedTestHom (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C)
    (r : G6Vertex (g6SelectedRegion G A B y w))
    (ha : ∀ v : C.supp, some (Sum.inl (g6ComponentPoint G A B y w C hC v)) ≠ r) :
    C.toSimpleGraph →g (g6ActualTestGraph G A B y u w).induce {q | q ≠ r} where
  toFun v := ⟨some (Sum.inl (g6ComponentPoint G A B y w C hC v)), ha v⟩
  map_rel' := by
    intro a b e
    change G.Adj a.1.1 b.1.1 ∨ _
    exact Or.inl e

def g6ComponentMinusPointHom (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C)
    (z : g6SelectedRegion G A B y w) (s : C.supp) (hs : s.1.1 = z.1) :
    (C.toSimpleGraph.induce {v | v ≠ s}) →g
      (g6ActualTestGraph G A B y u w).induce {q | q ≠ some (Sum.inl z)} where
  toFun v := ⟨some (Sum.inl (g6ComponentPoint G A B y w C hC v.1)), by
    intro he
    have heH : g6ComponentPoint G A B y w C hC v.1 = z :=
      Sum.inl.inj (Option.some.inj he)
    have heV : v.1.1.1 = z.1 := congrArg Subtype.val heH
    have hev : v.1 = s := Subtype.ext (Subtype.ext (heV.trans hs.symm))
    exact v.2 hev⟩
  map_rel' := by
    intro a b e
    change G.Adj a.1.1.1 b.1.1.1 ∨ _
    exact Or.inl e

theorem g6_matching_edge_avoiding_u (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hM : g6ComponentMatching G A B y C) :
    ∃ d : C.supp, ∃ a ∈ A, a ≠ u ∧ G.Adj d.1.1 a := by
  obtain ⟨d, e, a, b, ha, hb, _hde, hab, eda, eeb⟩ := hM
  by_cases hau : a = u
  · exact ⟨e, b, hb, fun hbu => hab (hau.trans hbu.symm), eeb⟩
  · exact ⟨d, a, ha, hau, eda⟩

theorem g6_delete_u_connected (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (hS : (g6Boundary G (g6SelectedRegion G A B y w) A u).Nonempty)
    (hcross : ∀ a ∈ A, G.Adj a w)
    (hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C) :
    ((g6ActualTestGraph G A B y u w).induce {q | q ≠ some (Sum.inr false)}).Connected := by
  let H := g6SelectedRegion G A B y w
  let U : G6Vertex H := some (Sum.inr false)
  let D := (g6ActualTestGraph G A B y u w).induce {q | q ≠ U}
  let T : {q : G6Vertex H // q ≠ U} := ⟨none, by
    change (none : G6Vertex H) ≠ some (Sum.inr false)
    intro he
    cases he⟩
  let W : {q : G6Vertex H // q ≠ U} := ⟨some (Sum.inr true), by
    intro he
    have hb : (true : Bool) = false := Sum.inr.inj (Option.some.inj he)
    cases hb⟩
  have eWT : D.Adj W T := by
    change (g6Graph G H A u w).Adj (some (Sum.inr true)) none ∨ _
    exact Or.inl (g6_tag_to_w G H A u w hS hcross).symm
  have hto : ∀ p : {q : G6Vertex H // q ≠ U}, D.Reachable p T := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact Reachable.rfl
    | some q =>
      cases q with
      | inr b =>
        cases b with
        | false => exact False.elim (hq rfl)
        | true => exact eWT.reachable
      | inl h =>
        obtain ⟨hv, C, hvC, t, htC, ewt⟩ :=
          (g6Selected_iff_actual_component G A B y w h.1).mp h.2
        let c : C.supp := ⟨⟨h.1, hv⟩, hvC⟩
        have hC : g6ComponentTouches G A B y w C := ⟨⟨t, htC⟩, ewt⟩
        have avoid : ∀ v : C.supp, some (Sum.inl (g6ComponentPoint G A B y w C hC v)) ≠ U := by
          intro v he
          cases Option.some.inj he
        let f := g6ComponentDeletedTestHom G A B y u w C hC U avoid
        obtain ⟨d, a, ha, hau, eda⟩ := g6_matching_edge_avoiding_u G A B y u C (hM C hC)
        have hr : D.Reachable (f c) (f d) := (C.connected_toSimpleGraph c d).map f
        have hec : f c = (⟨some (Sum.inl h), hq⟩ : {q : G6Vertex H // q ≠ U}) := by
          apply Subtype.ext
          exact congrArg (fun z : H => some (Sum.inl z)) (Subtype.ext rfl)
        have ed : D.Adj (f d) T := by
          change (∃ a ∈ g6Boundary G H A u, G.Adj d.1.1 a) ∨ _
          exact Or.inl ⟨a, ⟨ha, hau, d.1.1,
            (g6ComponentPoint G A B y w C hC d).2, eda.symm⟩, eda⟩
        exact Eq.mp (congrArg (fun z => D.Reachable z T) hec) (hr.trans ed.reachable)
  refine { preconnected := ?_, nonempty := ⟨T⟩ }
  intro p q
  exact (hto p).trans (hto q).symm

theorem g6_delete_none_connected (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (euw : G.Adj u w) :
    ((g6ActualTestGraph G A B y u w).induce {q | q ≠ none}).Connected := by
  let H := g6SelectedRegion G A B y w
  let D := (g6ActualTestGraph G A B y u w).induce {q | q ≠ none}
  let U : {q : G6Vertex H // q ≠ none} := ⟨some (Sum.inr false), by intro he; cases he⟩
  let W : {q : G6Vertex H // q ≠ none} := ⟨some (Sum.inr true), by intro he; cases he⟩
  have eUW : D.Adj U W := by
    change G.Adj u w ∨ _
    exact Or.inl euw
  have hto : ∀ p : {q : G6Vertex H // q ≠ none}, D.Reachable p W := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact False.elim (hq rfl)
    | some q =>
      cases q with
      | inr b =>
        cases b with
        | false => exact eUW.reachable
        | true => exact Reachable.rfl
      | inl h =>
        obtain ⟨hv, C, hvC, t, htC, ewt⟩ :=
          (g6Selected_iff_actual_component G A B y w h.1).mp h.2
        let c : C.supp := ⟨⟨h.1, hv⟩, hvC⟩
        let tr : C.supp := ⟨t, htC⟩
        have hC : g6ComponentTouches G A B y w C := ⟨tr, ewt⟩
        have avoid : ∀ v : C.supp,
            (some (Sum.inl (g6ComponentPoint G A B y w C hC v)) : G6Vertex H) ≠ none := by
          intro v he
          cases he
        let f := g6ComponentDeletedTestHom G A B y u w C hC none avoid
        have hr : D.Reachable (f c) (f tr) := (C.connected_toSimpleGraph c tr).map f
        have hec : f c = (⟨some (Sum.inl h), hq⟩ : {q : G6Vertex H // q ≠ none}) := by
          apply Subtype.ext
          exact congrArg (fun z : H => some (Sum.inl z)) (Subtype.ext rfl)
        have ed : D.Adj (f tr) W := by
          change G.Adj t.1 w ∨ _
          exact Or.inl ewt.symm
        exact Eq.mp (congrArg (fun z => D.Reachable z W) hec) (hr.trans ed.reachable)
  refine { preconnected := ?_, nonempty := ⟨W⟩ }
  intro p q
  exact (hto p).trans (hto q).symm

#print axioms g6ComponentDeletedTestHom
#print axioms g6ComponentMinusPointHom
#print axioms g6_matching_edge_avoiding_u
#print axioms g6_delete_u_connected
#print axioms g6_delete_none_connected
end TaskH.Gao
