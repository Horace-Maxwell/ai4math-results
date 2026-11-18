import Research.TaskH.Gao.G6DeleteActualHPoint

/-! The actual G6 test graph, including its necessary nonempty H condition. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

@[instance_reducible]
noncomputable def g6ActualVertexFintype [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (y w : V) :
    Fintype (G6Vertex (g6SelectedRegion G A B y w)) := Fintype.ofFinite _

theorem g6_actual_test_twoConnected [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (hu : u ∈ A) (hw : w ∈ B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hH : (g6SelectedRegion G A B y w).Nonempty)
    (hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C)
    (hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C →
      ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a) :
    @TwoConnected (G6Vertex (g6SelectedRegion G A B y w))
      (g6ActualVertexFintype G A B y w) (g6ActualTestGraph G A B y u w) := by
  classical
  let H := g6SelectedRegion G A B y w
  let : Fintype (G6Vertex H) := g6ActualVertexFintype G A B y w
  let U : G6Vertex H := some (Sum.inr false)
  let W : G6Vertex H := some (Sum.inr true)
  have hUT : U ≠ none := by
    change (some (Sum.inr false) : G6Vertex H) ≠ none
    intro he
    cases he
  have hUW : U ≠ W := by
    intro he
    have hb : (false : Bool) = true := Sum.inr.inj (Option.some.inj he)
    cases hb
  have hTW : (none : G6Vertex H) ≠ W := by
    change (none : G6Vertex H) ≠ some (Sum.inr true)
    intro he
    cases he
  have hc : 2 < Fintype.card (G6Vertex H) :=
    Fintype.two_lt_card_iff.mpr ⟨U, none, W, hUT, hUW, hTW⟩
  obtain ⟨v, hvH⟩ := hH
  obtain ⟨hv, C, hvC, t, htC, ewt⟩ :=
    (g6Selected_iff_actual_component G A B y w v).mp hvH
  have hC : g6ComponentTouches G A B y w C := ⟨⟨t, htC⟩, ewt⟩
  have hS := g6_component_matching_boundary_nonempty G A B y w u C hC (hM C hC)
  have euw : G.Adj u w := hcross u hu w hw
  have hAw : ∀ a ∈ A, G.Adj a w := fun a ha => hcross a ha w hw
  have hcard : 3 ≤ Fintype.card (G6Vertex (g6SelectedRegion G A B y w)) := by
    change 3 ≤ Fintype.card (G6Vertex H)
    exact hc
  refine ⟨hcard, g6_actual_test_connected_of_actual_component_matchings
    G A B y u w hu hw hcross hM, ?_⟩
  intro r
  cases r with
  | none => exact g6_delete_none_connected G A B y u w euw
  | some r =>
    cases r with
    | inr b =>
      cases b with
      | false => exact g6_delete_u_connected G A B y u w hS hAw hM
      | true => exact g6_delete_retained_w_connected_of_actual_component_matchings G A B y u w hM
    | inl z => exact g6_delete_actual_h_point_connected G A B y u w z hS euw hAw hAttach

theorem g6_actual_rooted_twoConnected [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (y u w : V)
    (hu : u ∈ A) (hw : w ∈ B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hH : (g6SelectedRegion G A B y w).Nonempty)
    (hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C)
    (hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C →
      ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a) :
    @RootedTwoConnected (G6Vertex (g6SelectedRegion G A B y w))
      (g6ActualVertexFintype G A B y w)
      (g6Graph G (g6SelectedRegion G A B y w) A u w)
      (some (Sum.inr false)) none := by
  constructor
  · intro he
    cases he
  · exact g6_actual_test_twoConnected G A B y u w hu hw hcross hH hM hAttach

#print axioms g6ActualVertexFintype
#print axioms g6_actual_test_twoConnected
#print axioms g6_actual_rooted_twoConnected
end TaskH.Gao
