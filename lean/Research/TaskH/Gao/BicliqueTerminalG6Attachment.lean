import Research.TaskH.Gao.BicliqueTerminalOriginalFamily
import Research.TaskH.Gao.G6ComponentAttachment

/-! Literal component-carrier transport gives the already-existing G6 attachment input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def g4ComponentSetTransport (G : SimpleGraph V) {U W : Set V} (h : U = W)
    (C : (G.induce U).ConnectedComponent) : (G.induce W).ConnectedComponent :=
  Eq.mp (congrArg (fun S : Set V => (G.induce S).ConnectedComponent) h) C

theorem g4_terminal_attachment_set_transport (G : SimpleGraph V) (A : Set V)
    {U W : Set V} (h : U = W) (C : (G.induce U).ConnectedComponent) :
    (∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a) ↔
    (∀ (I : Set (g4ComponentSetTransport G h C).supp) (b : (g4ComponentSetTransport G h C).supp),
      TerminalFragment (g4ComponentSetTransport G h C).toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a) := by
  cases h
  exact Iff.rfl

theorem g4_core_compl_eq_actual_outside (A B : Set V) (y : V) :
    (bicliqueSingletonCore A B y)ᶜ = g6Outside A B y := by
  ext z
  change (¬(z ∈ A ∪ B ∨ z = y)) ↔ (z ∉ A ∪ B ∧ z ≠ y)
  exact not_or

theorem biclique_singleton_actual_g6_terminal_attachment [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ∀ (I : Set (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).supp)
      (b : (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).supp),
      TerminalFragment (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a := by
  exact (g4_terminal_attachment_set_transport G A (g4_core_compl_eq_actual_outside A B y) C).mp
    (biclique_singleton_terminal_attachment G A B x y s k C hG hAB hc hx hy hs hsk hA hB
      hNx hNy hd ih hno)

theorem biclique_singleton_actual_g6_cut_attachment [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k)
    (z : (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).supp)
    (E : ((g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).toSimpleGraph.induce
      {v | v ≠ z}).ConnectedComponent) :
    ∃ (d : (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).supp) (hdz : d ≠ z),
      (⟨d, hdz⟩ : {v : (g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C).supp // v ≠ z}) ∈ E.supp ∧
      ∃ a ∈ A, G.Adj d.1.1 a := by
  classical
  let D := g4ComponentSetTransport G (g4_core_compl_eq_actual_outside A B y) C
  let : Fintype D.supp := Fintype.ofFinite _
  exact g6_cut_component_attachment_of_terminal_interiors G A B y D
    (biclique_singleton_actual_g6_terminal_attachment G A B x y s k C hG hAB hc hx hy hs hsk
      hA hB hNx hNy hd ih hno) z E

#print axioms g4ComponentSetTransport
#print axioms g4_terminal_attachment_set_transport
#print axioms g4_core_compl_eq_actual_outside
#print axioms biclique_singleton_actual_g6_terminal_attachment
#print axioms biclique_singleton_actual_g6_cut_attachment
end TaskH.Gao
