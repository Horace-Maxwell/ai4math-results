import Research.TaskH.Gao.G6ActualComponents
import Research.TaskH.Gao.TerminalFragmentExistence

/-! Actual component points, matching edges and terminal-interior attachments.
The earlier G1--G4 original-counterexample arguments are not assumed proved. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def g6ComponentTouches (G : SimpleGraph V) (A B : Set V) (y w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent) : Prop :=
  ∃ t : C.supp, G.Adj w t.1.1

def g6ComponentPoint (G : SimpleGraph V) (A B : Set V) (y w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C) (v : C.supp) : g6SelectedRegion G A B y w :=
  ⟨v.1.1, by
    obtain ⟨t, e⟩ := hC
    exact ⟨v.1.2, t.1, e, C.reachable_of_mem_supp v.2 t.2⟩⟩

def g6ComponentMatching (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent) : Prop :=
  ∃ d e : C.supp, ∃ a b : V,
    a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b

theorem g6ComponentPoint_val (G : SimpleGraph V) (A B : Set V) (y w : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C) (v : C.supp) :
    (g6ComponentPoint G A B y w C hC v).1 = v.1.1 := rfl

theorem g6_component_matching_boundary_nonempty (G : SimpleGraph V)
    (A B : Set V) (y w u : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent)
    (hC : g6ComponentTouches G A B y w C) (hM : g6ComponentMatching G A B y C) :
    (g6Boundary G (g6SelectedRegion G A B y w) A u).Nonempty := by
  obtain ⟨d, e, a, b, ha, hb, _hde, hab, eda, eeb⟩ := hM
  exact g6_actual_boundary_nonempty G (g6SelectedRegion G A B y w) A u
    ⟨a, ha, b, hb, hab,
      ⟨d.1.1, (g6ComponentPoint G A B y w C hC d).2, eda.symm⟩,
      ⟨e.1.1, (g6ComponentPoint G A B y w C hC e).2, eeb.symm⟩⟩

theorem terminalInterior_contains_of_delete_connected (F : SimpleGraph V)
    (I : Set V) (b : V) (hT : TerminalFragment F I b)
    (hdel : (F.induce {v | v ≠ b}).Connected) :
    ∀ d : V, d ≠ b → d ∈ I := by
  have hclosed : ∀ a d : {v : V // v ≠ b}, a.1 ∈ I →
      (F.induce {v | v ≠ b}).Adj a d → d.1 ∈ I := by
    intro a d ha e
    rcases hT.2.2.1 a.1 ha d.1 e with he | hd
    · exact False.elim (d.2 he)
    · exact hd
  have hwalk : ∀ {a d : {v : V // v ≠ b}},
      (F.induce {v | v ≠ b}).Walk a d → a.1 ∈ I → d.1 ∈ I := by
    intro a d p
    induction p with
    | nil => exact fun ha => ha
    | cons e _ ih => exact fun ha => ih (hclosed _ _ ha e)
  obtain ⟨a, ha⟩ := hT.1
  have hab : a ≠ b := fun he => hT.2.1 (Eq.mp (congrArg (fun z : V => z ∈ I) he) ha)
  intro d hdb
  obtain ⟨p⟩ := hdel ⟨a, hab⟩ ⟨d, hdb⟩
  exact hwalk p ha

theorem g6_terminal_attachment_of_twoConnected_matching (G : SimpleGraph V)
    (A B : Set V) (y : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent) [iC : Fintype C.supp]
    (hD : @TwoConnected C.supp iC C.toSimpleGraph) (hM : g6ComponentMatching G A B y C) :
    ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a := by
  obtain ⟨d, e, a, a', ha, ha', hde, _haa', eda, eea'⟩ := hM
  intro I b hT
  have hi := terminalInterior_contains_of_delete_connected C.toSimpleGraph I b hT (hD.2.2 b)
  by_cases hdb : d = b
  · have heb : e ≠ b := fun he => hde (hdb.trans he.symm)
    exact ⟨e, hi e heb, a', ha', eea'⟩
  · exact ⟨d, hi d hdb, a, ha, eda⟩

theorem g6_cut_component_attachment_of_terminal_interiors (G : SimpleGraph V)
    (A B : Set V) (y : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent) [iC : Fintype C.supp]
    (hAttach : ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a)
    (z : C.supp) (E : (C.toSimpleGraph.induce {v | v ≠ z}).ConnectedComponent) :
    ∃ (d : C.supp) (hdz : d ≠ z), (⟨d, hdz⟩ : {v : C.supp // v ≠ z}) ∈ E.supp ∧
      ∃ a ∈ A, G.Adj d.1.1 a := by
  obtain ⟨b, D, hsub, hT⟩ := terminal_fragment_in_deleted_component C.toSimpleGraph z E
    C.connected_toSimpleGraph
  obtain ⟨d, hdI, a, ha, eda⟩ := hAttach (deletedInterior C.toSimpleGraph b D) b hT
  obtain ⟨hdz, hdE⟩ := hsub hdI
  exact ⟨d, hdz, hdE, a, ha, eda⟩

theorem g6_cut_component_attachment_of_twoConnected_matching (G : SimpleGraph V)
    (A B : Set V) (y : V)
    (C : (G.induce (g6Outside A B y)).ConnectedComponent) [iC : Fintype C.supp]
    (hD : @TwoConnected C.supp iC C.toSimpleGraph) (hM : g6ComponentMatching G A B y C)
    (z : C.supp) (E : (C.toSimpleGraph.induce {v | v ≠ z}).ConnectedComponent) :
    ∃ (d : C.supp) (hdz : d ≠ z), (⟨d, hdz⟩ : {v : C.supp // v ≠ z}) ∈ E.supp ∧
      ∃ a ∈ A, G.Adj d.1.1 a := by
  exact g6_cut_component_attachment_of_terminal_interiors G A B y C
    (g6_terminal_attachment_of_twoConnected_matching G A B y C hD hM) z E

#print axioms g6ComponentTouches
#print axioms g6ComponentPoint
#print axioms g6ComponentMatching
#print axioms g6ComponentPoint_val
#print axioms g6_component_matching_boundary_nonempty
#print axioms terminalInterior_contains_of_delete_connected
#print axioms g6_terminal_attachment_of_twoConnected_matching
#print axioms g6_cut_component_attachment_of_terminal_interiors
#print axioms g6_cut_component_attachment_of_twoConnected_matching
end TaskH.Gao
