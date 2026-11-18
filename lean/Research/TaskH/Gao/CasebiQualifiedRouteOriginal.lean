import Research.TaskH.Gao.ActualQualifiedRouteHub
import Research.TaskH.Gao.ActualHubBothFamilyBranches

/-! Original normalized y-terminal qualified-route branch. Actual child
regions, cuts and two sides are now theorem conclusions supplied internally;
no desired path family, degree, strict order or side cover is a new input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_actual_qualified_route_hub_original_family [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b)
    (Y : Set C.supp) (bt : C.supp) (hT : TerminalFragment C.toSimpleGraph Y bt)
    (hyr : yr ∈ Y) (S : Set C.supp)
    (hHub : ActualQualifiedRouteHub C.toSimpleGraph I b yr S) :
    HasAdmissiblePaths G x y k := by
  rcases hHub with ⟨⟨iS, hS⟩, hmaxS, hne, hcap, hroute⟩
  let : Fintype S := iS
  obtain ⟨u, v, huv, hcut, hyS, E, hEu, hIE, hySide⟩ :=
    actual_qualified_route_side_data C.toSimpleGraph C.connected_toSimpleGraph
      I b hI Y bt yr hT hyr S hS hmaxS hne hcap hroute
  exact actual_maximal_hub_sides_original_contradiction G A B x y s k hmax hBs hk
    hG htri hquad hd ih C yr hY S u v huv hS hmaxS hcut hyS I b hI E hEu hIE hySide

theorem casebi_no_family_no_actual_qualified_route_hub [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b)
    (Y : Set C.supp) (bt : C.supp) (hT : TerminalFragment C.toSimpleGraph Y bt)
    (hyr : yr ∈ Y) (hno : ¬HasAdmissiblePaths G x y k) :
    ¬∃ S : Set C.supp, ActualQualifiedRouteHub C.toSimpleGraph I b yr S := by
  rintro ⟨S, hHub⟩
  exact hno (casebi_actual_qualified_route_hub_original_family G A B x y s k
    hmax hBs hk hG htri hquad hd ih C yr hY I b hI Y bt hT hyr S hHub)

#print axioms casebi_actual_qualified_route_hub_original_family
#print axioms casebi_no_family_no_actual_qualified_route_hub
end TaskH.Gao
