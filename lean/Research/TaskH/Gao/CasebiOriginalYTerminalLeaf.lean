import Research.TaskH.Gao.NoHubYTerminalLeaf
import Research.TaskH.Gao.CasebiOriginalLeafCommonPoint
import Research.TaskH.Gao.CasebiQualifiedRouteOriginal

/-! Actual original Case2/y-terminal transport. The initial exterior point,
noncut y, all hub/path/cut data, y-leaf and common terminal point are derived
inside the original normalized finite-graph domain. No desired-leaf premise. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_original_y_outside_first_terminal [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (L : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected L a d →
      NonrootDegreeAtLeast L a d (r + 1) → HasAdmissiblePaths L a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (J : Set C.supp) (bt : C.supp) (hJ : TerminalFragment C.toSimpleGraph J bt) (hyJ : yr ∈ J)
    (hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a) :
    yr ∉ fragmentBlock I b := by
  have hNoA := casebi_feasible_no_first_part G A B x y s k hmax hBs hk hG htri hquad
    hd hno ih C yr hY I b hI hyI
  obtain ⟨q, hqy, a, haA, eqa⟩ := hTouch
  have hqI : q ∉ I := fun hq => hNoA q hq a haA eqa
  have hyNoncut : (C.toSimpleGraph.induce {v | v ≠ yr}).Connected := by
    rcases hJ with ⟨_hne, _hbt, _hclosed, _hJC, _hcomp, _hBC, hglobal, _hdel⟩
    exact hglobal yr hyJ
  exact terminal_noncut_external_point_outside_block C.toSimpleGraph I b hI yr q
    hyI hqy hqI hyNoncut

theorem casebi_original_nohub_y_terminal_leaf [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (L : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected L a d →
      NonrootDegreeAtLeast L a d (r + 1) → HasAdmissiblePaths L a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (J : Set C.supp) (bt : C.supp) (hJ : TerminalFragment C.toSimpleGraph J bt) (hyJ : yr ∈ J)
    (hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a)
    (hnoHub : ¬∃ S : Set C.supp, ActualQualifiedRouteHub C.toSimpleGraph I b yr S) :
    J = {yr} ∧ C.toSimpleGraph.neighborSet yr = {bt} ∧ C.toSimpleGraph.Adj yr bt := by
  have hyB := casebi_original_y_outside_first_terminal G A B x y s k hmax hBs hk hG
    htri hquad hd hno ih C yr hY I b hI hyI J bt hJ hyJ hTouch
  exact no_actual_qualified_hub_y_terminal_singleton C.toSimpleGraph C.connected_toSimpleGraph
    I b hI J bt yr hJ hyJ hyB hnoHub

theorem casebi_original_y_terminal_leaf_and_common_point [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (hxy : ¬G.Adj x y)
    (htri : CasebiNoRootTriangle G x y) (htriY : CasebiNoRootTriangle G y x)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (L : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected L a d →
      NonrootDegreeAtLeast L a d (r + 1) → HasAdmissiblePaths L a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (J : Set C.supp) (bt : C.supp) (hJ : TerminalFragment C.toSimpleGraph J bt) (hyJ : yr ∈ J)
    (hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a) :
    J = {yr} ∧ C.toSimpleGraph.neighborSet yr = {bt} ∧ C.toSimpleGraph.Adj yr bt ∧
      ∃ p : C.supp,
        G.neighborSet x = insert (componentVertex C p) A ∧
        G.neighborSet y = insert (componentVertex C bt) A ∧
        (∀ (U : Set C.supp) (d : C.supp), TerminalFragment C.toSimpleGraph U d →
          yr ∉ U → p ∈ U) ∧
        ∀ (z : C.supp) (D : (C.toSimpleGraph.induce {v | v ≠ z}).ConnectedComponent),
          yr ∉ deletedInterior C.toSimpleGraph z D → p ∈ deletedInterior C.toSimpleGraph z D := by
  have hnoHub := casebi_no_family_no_actual_qualified_route_hub G A B x y s k hmax hBs hk
    hG htri hquad hd ih C yr hY I b hI J bt hJ hyJ hno
  obtain ⟨hJone, hNy, eyb⟩ := casebi_original_nohub_y_terminal_leaf G A B x y s k
    hmax hBs hk hG htri hquad hd hno ih C yr hY I b hI hyI J bt hJ hyJ hTouch hnoHub
  obtain ⟨r, hrI⟩ := hI.1
  have hbr : b ≠ r := fun he => hI.2.1
    (Eq.mpr (congrArg (fun z : C.supp => z ∈ I) he) hrI)
  have hC1 : 1 < Fintype.card C.supp := Fintype.one_lt_card_iff.mpr ⟨b, r, hbr⟩
  have hC : 2 ≤ Fintype.card C.supp := by omega
  obtain ⟨p, hNX, hNY, hCommon, hDeleted⟩ :=
    casebi_y_leaf_original_common_terminal_point G A B x y s k hmax hBs hk hG hxy
      htri htriY hquad hd hno horder ih C yr bt hY hC hNy
  exact ⟨hJone, hNy, eyb, p, hNX, hNY, hCommon, hDeleted⟩

#print axioms casebi_original_y_outside_first_terminal
#print axioms casebi_original_nohub_y_terminal_leaf
#print axioms casebi_original_y_terminal_leaf_and_common_point
end TaskH.Gao
