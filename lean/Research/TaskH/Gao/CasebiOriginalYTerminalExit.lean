import Research.TaskH.Gao.NoHubOutsideActualHub
import Research.TaskH.Gao.CasebiOriginalYLeafFirstBlockExit
import Research.TaskH.Gao.CasebiNoHubLowDegreeExit

/-! Complete original normalized y-terminal exit. The desired y-leaf, common
point, actual maximal carrier and qualified route are derived internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_original_y_leaf_boundary_outside_first_block_contradiction [Fintype V]
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
    (hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a)
    (hbtB : bt ∉ fragmentBlock I b) : False := by
  classical
  obtain ⟨hJone, hNy, _eybt, p, hNX, hNY, hCommon, _hDeleted⟩ :=
    casebi_original_y_terminal_leaf_and_common_point G A B x y s k hmax hBs hk hG hxy
      htri htriY hquad hd hno horder ih C yr hY I b hI hyI J bt hJ hyJ hTouch
  have hOne : TerminalFragment C.toSimpleGraph {yr} bt :=
    Eq.mp (congrArg (fun U : Set C.supp => TerminalFragment C.toSimpleGraph U bt) hJone) hJ
  have hpI : p ∈ I := hCommon I b hI hyI
  have hbp : bt ≠ p := fun he => hbtB (Or.inr
    (Eq.mpr (congrArg (fun z : C.supp => z ∈ I) he) hpI))
  by_cases hsmall : (C.toSimpleGraph.neighborSet bt).ncard ≤ 2
  · obtain ⟨hsone, _hBtouch⟩ := casebi_feasible_second_side_rigidity G A B x y s k hmax hBs hk
      hG htri hquad hd hno ih C yr hY I b hI hyI
    have hB2 : B.ncard = 2 := by omega
    exact casebi_y_leaf_boundary_low_degree_contradiction G A B x y k hmax.1 hB2 hk hd
      htriY C yr bt p hY hNy hbp hNX hNY hsmall
  · have hhigh : 3 ≤ (C.toSimpleGraph.neighborSet bt).ncard := by omega
    have hHub := singleton_terminal_high_degree_qualified_hub C.toSimpleGraph
      C.connected_toSimpleGraph I b hI yr p bt hyI hbtB hOne hCommon hhigh
    exact (casebi_no_family_no_actual_qualified_route_hub G A B x y s k hmax hBs hk
      hG htri hquad hd ih C yr hY I b hI J bt hJ hyJ hno) hHub

theorem casebi_original_y_terminal_contradiction [Fintype V]
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
    (hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a) : False := by
  classical
  by_cases hbtB : bt ∈ fragmentBlock I b
  · exact casebi_original_y_leaf_boundary_in_first_block_contradiction G A B x y s k hmax hBs hk
      hG hxy htri htriY hquad hd hno horder ih C yr hY I b hI hyI J bt hJ hyJ hTouch hbtB
  · exact casebi_original_y_leaf_boundary_outside_first_block_contradiction G A B x y s k hmax hBs hk
      hG hxy htri htriY hquad hd hno horder ih C yr hY I b hI hyI J bt hJ hyJ hTouch hbtB

#print axioms casebi_original_y_leaf_boundary_outside_first_block_contradiction
#print axioms casebi_original_y_terminal_contradiction
end TaskH.Gao
