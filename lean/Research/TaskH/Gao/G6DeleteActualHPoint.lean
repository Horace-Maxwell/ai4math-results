import Research.TaskH.Gao.G6AnchorDeletions

/-! Every actual H-point deletion is treated through its actual outside component. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem g6_delete_actual_h_point_connected [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (z : g6SelectedRegion G A B y w)
    (hS : (g6Boundary G (g6SelectedRegion G A B y w) A u).Nonempty)
    (euw : G.Adj u w) (hcross : ∀ a ∈ A, G.Adj a w)
    (hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C →
      ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a) :
    ((g6ActualTestGraph G A B y u w).induce {q | q ≠ some (Sum.inl z)}).Connected := by
  classical
  let H := g6SelectedRegion G A B y w
  let Z : G6Vertex H := some (Sum.inl z)
  let D := (g6ActualTestGraph G A B y u w).induce {q | q ≠ Z}
  let U : {q : G6Vertex H // q ≠ Z} := ⟨some (Sum.inr false), by
    intro he
    cases Option.some.inj he⟩
  let W : {q : G6Vertex H // q ≠ Z} := ⟨some (Sum.inr true), by
    intro he
    cases Option.some.inj he⟩
  let T : {q : G6Vertex H // q ≠ Z} := ⟨none, by
    change (none : G6Vertex H) ≠ some (Sum.inl z)
    intro he
    cases he⟩
  have eUW : D.Adj U W := by
    change G.Adj u w ∨ _
    exact Or.inl euw
  have eTW : D.Adj T W := by
    change (g6Graph G H A u w).Adj none (some (Sum.inr true)) ∨ _
    exact Or.inl (g6_tag_to_w G H A u w hS hcross)
  have hzOut : z.1 ∈ g6Outside A B y := g6Selected_subset_outside G A B y w z.2
  have hto : ∀ p : {q : G6Vertex H // q ≠ Z}, D.Reachable p W := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact eTW.reachable
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
        by_cases hzC : (⟨z.1, hzOut⟩ : g6Outside A B y) ∈ C.supp
        · let s : C.supp := ⟨⟨z.1, hzOut⟩, hzC⟩
          have hcs : c ≠ s := by
            intro he
            apply hq
            apply congrArg (fun a : H => some (Sum.inl a))
            apply Subtype.ext
            exact congrArg (fun a : C.supp => a.1.1) he
          let E := (C.toSimpleGraph.induce {v | v ≠ s}).connectedComponentMk ⟨c, hcs⟩
          let : Fintype C.supp := Fintype.ofFinite _
          obtain ⟨d, hds, hdE, a, ha, eda⟩ :=
            g6_cut_component_attachment_of_terminal_interiors G A B y C (hAttach C hC) s E
          have hrC : (C.toSimpleGraph.induce {v | v ≠ s}).Reachable
              ⟨c, hcs⟩ ⟨d, hds⟩ := E.reachable_of_mem_supp rfl hdE
          let f := g6ComponentMinusPointHom G A B y u w C hC z s (by rfl)
          have hr : D.Reachable (f ⟨c, hcs⟩) (f ⟨d, hds⟩) := hrC.map f
          have hec : f ⟨c, hcs⟩ =
              (⟨some (Sum.inl h), hq⟩ : {q : G6Vertex H // q ≠ Z}) := by
            apply Subtype.ext
            exact congrArg (fun a : H => some (Sum.inl a)) (Subtype.ext rfl)
          by_cases hau : a = u
          · have ed : D.Adj (f ⟨d, hds⟩) U := by
              change G.Adj d.1.1 u ∨ _
              exact Or.inl (Eq.mp (congrArg (fun v : V => G.Adj d.1.1 v) hau) eda)
            exact Eq.mp (congrArg (fun v => D.Reachable v W) hec)
              (hr.trans (ed.reachable.trans eUW.reachable))
          · have ed : D.Adj (f ⟨d, hds⟩) T := by
              change (∃ a ∈ g6Boundary G H A u, G.Adj d.1.1 a) ∨ _
              exact Or.inl ⟨a, ⟨ha, hau, d.1.1,
                (g6ComponentPoint G A B y w C hC d).2, eda.symm⟩, eda⟩
            exact Eq.mp (congrArg (fun v => D.Reachable v W) hec)
              (hr.trans (ed.reachable.trans eTW.reachable))
        · have avoid : ∀ v : C.supp,
              some (Sum.inl (g6ComponentPoint G A B y w C hC v)) ≠ Z := by
            intro v he
            have heH : g6ComponentPoint G A B y w C hC v = z :=
              Sum.inl.inj (Option.some.inj he)
            have heV : v.1.1 = z.1 := congrArg Subtype.val heH
            have heOut : v.1 = (⟨z.1, hzOut⟩ : g6Outside A B y) := Subtype.ext heV
            exact hzC (Eq.mp (congrArg (fun a : g6Outside A B y => a ∈ C.supp) heOut) v.2)
          let f := g6ComponentDeletedTestHom G A B y u w C hC Z avoid
          have hr : D.Reachable (f c) (f tr) := (C.connected_toSimpleGraph c tr).map f
          have hec : f c = (⟨some (Sum.inl h), hq⟩ : {q : G6Vertex H // q ≠ Z}) := by
            apply Subtype.ext
            exact congrArg (fun a : H => some (Sum.inl a)) (Subtype.ext rfl)
          have ed : D.Adj (f tr) W := by
            change G.Adj t.1 w ∨ _
            exact Or.inl ewt.symm
          exact Eq.mp (congrArg (fun v => D.Reachable v W) hec) (hr.trans ed.reachable)
  refine { preconnected := ?_, nonempty := ⟨W⟩ }
  intro p q
  exact (hto p).trans (hto q).symm

#print axioms g6_delete_actual_h_point_connected
end TaskH.Gao
