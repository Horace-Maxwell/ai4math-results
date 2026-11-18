import Research.TaskH.Gao.G5ExtensionConnectivity
import Research.TaskH.Gao.BicliqueSingletonFirstGeometry
import Research.TaskH.Gao.CliqueCoreDegree

/-! Actual G5: retain the actual outside component and u, collapse precisely
the other actual A-boundary points. B and y are absent. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def g5Retained (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) : Set V :=
  singletonG1Vertices G (bicliqueSingletonCore A B y) C ∪ {u}

def g5Collapse (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) : Set V :=
  {a | a ∈ A ∧ a ≠ u ∧ ∃ d : C.supp, G.Adj d.1.1 a}

theorem g5_retained_collapse_disjoint (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) :
    Disjoint (g5Retained G A B y u C) (g5Collapse G A B y u C) := by
  apply Set.disjoint_left.mpr
  intro a ha hs
  rcases ha with ha | ha
  · exact ha.1 (Or.inl (Or.inl hs.1))
  · exact hs.2.1 ha

def g5Root (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) :=
  regionRetainedVertex (g5Retained G A B y u C) (g5Collapse G A B y u C)
    (g5_retained_collapse_disjoint G A B y u C) ⟨u, Or.inr rfl⟩

def g5Point (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) (d : C.supp) :=
  regionRetainedVertex (g5Retained G A B y u C) (g5Collapse G A B y u C)
    (g5_retained_collapse_disjoint G A B y u C) ⟨d.1.1, Or.inl ⟨d.1.2, d.2⟩⟩

theorem g5_actual_quotient_rooted [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hu : u ∈ A) (hU : ∃ d : C.supp, G.Adj d.1.1 u)
    (hM : ∃ d e : C.supp, ∃ a b : V,
      a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b)
    (hAttach : ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a)
    [Fintype (IdentificationVertex
      {w : (g5Retained G A B y u C ∪ g5Collapse G A B y u C : Set V) |
        w.1 ∈ g5Collapse G A B y u C})] :
    RootedTwoConnected
      (regionIdentificationGraph G (g5Retained G A B y u C) (g5Collapse G A B y u C))
      (some (g5Root G A B y u C)) none := by
  classical
  let : Fintype C.supp := Fintype.ofFinite _
  let N := g5Retained G A B y u C
  let S := g5Collapse G A B y u C
  let J := regionIdentificationGraph G N S
  let U := some (g5Root G A B y u C)
  let f : C.supp → IdentificationVertex {w : (N ∪ S : Set V) | w.1 ∈ S} :=
    fun d => some (g5Point G A B y u C d)
  have hfi : Function.Injective f := by
    intro d e he
    have hv : d.1.1 = e.1.1 := congrArg (fun q => q.1.1) (Option.some.inj he)
    exact Subtype.ext (Subtype.ext hv)
  have hfU : ∀ d, f d ≠ U := by
    intro d he
    have hv : d.1.1 = u := congrArg (fun q => q.1.1) (Option.some.inj he)
    exact d.1.2 (Or.inl (Or.inl (hv.symm ▸ hu)))
  have hfT : ∀ d, f d ≠ none := by intro d he; cases he
  have hmap : ∀ {d e}, C.toSimpleGraph.Adj d e → J.Adj (f d) (f e) := by
    intro d e he
    exact he
  have hcover : ∀ q, q = U ∨ q = none ∨ ∃ d, f d = q := by
    intro q
    cases q with
    | none => exact Or.inr (Or.inl rfl)
    | some q =>
      have hqN : q.1.1 ∈ N := q.1.2.elim id (fun h => False.elim (q.2 h))
      rcases hqN with hqR | hqu
      · let d : C.supp := ⟨⟨q.1.1, hqR.1⟩, hqR.2⟩
        right; right
        refine ⟨d, congrArg Option.some ?_⟩
        exact Subtype.ext (Subtype.ext rfl)
      · left
        apply congrArg Option.some
        exact Subtype.ext (Subtype.ext hqu)
  have hU' : ∃ d, J.Adj (f d) U := by
    obtain ⟨d, ed⟩ := hU
    exact ⟨d, ed⟩
  have hT' : ∃ d, J.Adj (f d) none := by
    obtain ⟨d, e, a, b, ha, hb, _hde, hab, eda, eeb⟩ := hM
    by_cases hau : a = u
    · have hbu : b ≠ u := fun hbu => hab (hau.trans hbu.symm)
      exact ⟨e, ⟨⟨b, Or.inr ⟨hb, hbu, e, eeb⟩⟩, ⟨hb, hbu, e, eeb⟩, eeb⟩⟩
    · exact ⟨d, ⟨⟨a, Or.inr ⟨ha, hau, d, eda⟩⟩, ⟨ha, hau, d, eda⟩, eda⟩⟩
  have hcut : ∀ (z : C.supp)
      (E : (C.toSimpleGraph.induce {d | d ≠ z}).ConnectedComponent),
      ∃ (d : C.supp) (hdz : d ≠ z),
        (⟨d, hdz⟩ : {d : C.supp // d ≠ z}) ∈ E.supp ∧
          (J.Adj (f d) U ∨ J.Adj (f d) none) := by
    intro z E
    obtain ⟨b, D, hsub, hT⟩ := terminal_fragment_in_deleted_component C.toSimpleGraph z E
      C.connected_toSimpleGraph
    obtain ⟨d, hdI, a, ha, eda⟩ := hAttach (deletedInterior C.toSimpleGraph b D) b hT
    obtain ⟨hdz, hdE⟩ := hsub hdI
    refine ⟨d, hdz, hdE, ?_⟩
    by_cases hau : a = u
    · left
      exact Eq.mp (congrArg (fun v => G.Adj d.1.1 v) hau) eda
    · right
      exact ⟨⟨a, Or.inr ⟨ha, hau, d, eda⟩⟩, ⟨ha, hau, d, eda⟩, eda⟩
  exact g5_extension_rooted C.toSimpleGraph J f U none
    (by change some (g5Root G A B y u C) ≠ none; exact Option.some_ne_none _)
    hfi hfU hfT hmap hcover C.connected_toSimpleGraph hU' hT' hcut

#print axioms g5Retained
#print axioms g5Collapse
#print axioms g5_retained_collapse_disjoint
#print axioms g5Root
#print axioms g5Point
#print axioms g5_actual_quotient_rooted
end TaskH.Gao
