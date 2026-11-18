import Research.TaskH.Fan.RootedConnectivity

/-!
Actual root-cut separation for the frozen rooted two-path hypotheses.
Only the connectivity-test graph adds xy; components remain those of G-b.
No partition, component cover, torso, or two-path oracle is assumed.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem rooted_cut_ne_left [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) : b ≠ x := by
  intro he
  subst b
  exact hbad (rooted_delete_left_connected hroot)

theorem rooted_cut_ne_right [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) : b ≠ y := by
  intro he
  subst b
  exact hbad (rooted_delete_right_connected hroot)

theorem rooted_cut_vertex_cover [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (v : {a : V // a ≠ b}) :
    (G.induce {a | a ≠ b}).connectedComponentMk v =
        (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ∨
      (G.induce {a | a ≠ b}).connectedComponentMk v =
        (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ := by
  let K := G.induce {a | a ≠ b}
  let A := (G ⊔ SimpleGraph.edge x y).induce {a | a ≠ b}
  let rx : {a : V // a ≠ b} := ⟨x, hx⟩
  let ry : {a : V // a ≠ b} := ⟨y, hy⟩
  have hedge : ∀ {a d : {v : V // v ≠ b}}, A.Adj a d →
      (K.connectedComponentMk d = K.connectedComponentMk rx ∨
        K.connectedComponentMk d = K.connectedComponentMk ry) →
      (K.connectedComponentMk a = K.connectedComponentMk rx ∨
        K.connectedComponentMk a = K.connectedComponentMk ry) := by
    intro a d hadj hd
    change G.Adj a.1 d.1 ∨ (SimpleGraph.edge x y).Adj a.1 d.1 at hadj
    rcases hadj with hG | he
    · have hc : K.connectedComponentMk a = K.connectedComponentMk d :=
        ConnectedComponent.connectedComponentMk_eq_of_adj (G := K) (v := a) (w := d) hG
      rcases hd with hd | hd
      · exact Or.inl (hc.trans hd)
      · exact Or.inr (hc.trans hd)
    · rcases (SimpleGraph.edge_adj x y a.1 d.1).mp he with ⟨he, _hne⟩
      rcases he with he | he
      · exact Or.inl (congrArg K.connectedComponentMk (Subtype.ext he.1))
      · exact Or.inr (congrArg K.connectedComponentMk (Subtype.ext he.1))
  have hwalk : ∀ {a d : {v : V // v ≠ b}} (p : A.Walk a d),
      (K.connectedComponentMk d = K.connectedComponentMk rx ∨
        K.connectedComponentMk d = K.connectedComponentMk ry) →
      (K.connectedComponentMk a = K.connectedComponentMk rx ∨
        K.connectedComponentMk a = K.connectedComponentMk ry) := by
    intro a d p
    induction p with
    | nil => exact fun h => h
    | cons h _ ih => exact fun hd => hedge h (ih hd)
  have hA : A.Connected := hroot.2.2.2 b
  obtain ⟨p⟩ := hA v rx
  exact hwalk p (Or.inl rfl)

theorem rooted_cut_roots_distinct [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) :
    (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ≠
      (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ := by
  intro he
  apply hbad
  have hall : ∀ v : {a : V // a ≠ b},
      (G.induce {a | a ≠ b}).connectedComponentMk v =
        (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ := by
    intro v
    rcases rooted_cut_vertex_cover G x y b hroot hx hy v with hv | hv
    · exact hv
    · exact hv.trans he.symm
  refine { preconnected := ?_, nonempty := ⟨⟨x, hx⟩⟩ }
  intro a d
  exact ConnectedComponent.exact ((hall a).trans (hall d).symm)

theorem rooted_cut_all_components [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (C : (G.induce {a | a ≠ b}).ConnectedComponent) :
    C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ∨
      C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  change (G.induce {a | a ≠ b}).connectedComponentMk v = C at hv
  rcases rooted_cut_vertex_cover G x y b hroot hx hy v with hc | hc
  · exact Or.inl (hv.symm.trans hc)
  · exact Or.inr (hv.symm.trans hc)

theorem rooted_cut_exact_components [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) :
    (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ≠
        (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ ∧
      ∀ C : (G.induce {a | a ≠ b}).ConnectedComponent,
        C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ∨
          C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ := by
  exact ⟨rooted_cut_roots_distinct G x y b hroot hx hy hbad,
    rooted_cut_all_components G x y b hroot hx hy⟩

theorem rooted_cut_separation [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) :
    ∃ hx : x ≠ b, ∃ hy : y ≠ b,
      (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ≠
          (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ ∧
        ∀ C : (G.induce {a | a ≠ b}).ConnectedComponent,
          C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩ ∨
            C = (G.induce {a | a ≠ b}).connectedComponentMk ⟨y, hy⟩ := by
  have hx : x ≠ b := (rooted_cut_ne_left G x y b hroot hbad).symm
  have hy : y ≠ b := (rooted_cut_ne_right G x y b hroot hbad).symm
  exact ⟨hx, hy, rooted_cut_exact_components G x y b hroot hx hy hbad⟩

#print axioms rooted_cut_ne_left
#print axioms rooted_cut_ne_right
#print axioms rooted_cut_vertex_cover
#print axioms rooted_cut_roots_distinct
#print axioms rooted_cut_all_components
#print axioms rooted_cut_exact_components
#print axioms rooted_cut_separation
end TaskH.Fan
