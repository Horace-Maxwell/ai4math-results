import Research.TaskH.Gao.CasebiOriginalYTerminalLeaf

/-! When the y-leaf boundary belongs to the first genuine terminal block,
actual deleted components and common terminal extraction cover every vertex.
The original Case2 then closes by an actual forbidden y-triangle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem terminal_common_point_single_leaf_boundary_cover [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (I : Set V) (b y p : V) (hI : TerminalFragment G I b)
    (hY : TerminalFragment G {y} b) (hpI : p ∈ I)
    (hcommon : ∀ (U : Set V) (d : V), TerminalFragment G U d → y ∉ U → p ∈ U) :
    ∀ q : V, q = y ∨ q ∈ fragmentBlock I b := by
  classical
  intro q
  by_cases hqy : q = y
  · exact Or.inl hqy
  · right
    by_contra hqB
    have hqb : q ≠ b := fun he => hqB (Or.inl he)
    let D := (G.induce {v | v ≠ b}).connectedComponentMk ⟨q, hqb⟩
    have hyD : y ∉ deletedInterior G b D := by
      rintro ⟨hyb', he⟩
      have hr : (G.induce {v | v ≠ b}).Reachable ⟨y, hyb'⟩ ⟨q, hqb⟩ :=
        ConnectedComponent.exact he
      obtain ⟨r⟩ := hr
      have hqY := terminal_walk_stays_without_boundary G {y} b hY r
        (show y ∈ ({y} : Set V) from rfl)
      exact hqy hqY
    obtain ⟨hpb, hpD⟩ := terminal_common_point_in_deleted_component G y p b hG hcommon D hyD
    have hr : (G.induce {v | v ≠ b}).Reachable ⟨p, hpb⟩ ⟨q, hqb⟩ :=
      ConnectedComponent.exact hpD
    obtain ⟨r⟩ := hr
    exact hqB (Or.inr (terminal_walk_stays_without_boundary G I b hI r hpI))

theorem casebi_original_y_leaf_boundary_in_first_block_contradiction [Fintype V]
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
    (hbtB : bt ∈ fragmentBlock I b) : False := by
  obtain ⟨hJone, _hNy, eybt, p, _hNX, hNY, hCommon, _hDeleted⟩ :=
    casebi_original_y_terminal_leaf_and_common_point G A B x y s k hmax hBs hk hG hxy
      htri htriY hquad hd hno horder ih C yr hY I b hI hyI J bt hJ hyJ hTouch
  have hyB := casebi_original_y_outside_first_terminal G A B x y s k hmax hBs hk hG
    htri hquad hd hno ih C yr hY I b hI hyI J bt hJ hyJ hTouch
  have hbtb : bt = b := by
    rcases hbtB with he | hbtI
    · exact he
    · exact False.elim (hyB (hI.2.2.1 bt hbtI yr eybt.symm))
  have hOne : TerminalFragment C.toSimpleGraph {yr} bt :=
    Eq.mp (congrArg (fun U : Set C.supp => TerminalFragment C.toSimpleGraph U bt) hJone) hJ
  have hOneB : TerminalFragment C.toSimpleGraph {yr} b :=
    Eq.mp (congrArg (fun z : C.supp => TerminalFragment C.toSimpleGraph {yr} z) hbtb) hOne
  have hpI : p ∈ I := hCommon I b hI hyI
  have hcover := terminal_common_point_single_leaf_boundary_cover C.toSimpleGraph
    C.connected_toSimpleGraph I b yr p hI hOneB hpI hCommon
  have hNoA := casebi_feasible_no_first_part G A B x y s k hmax hBs hk hG htri hquad
    hd hno ih C yr hY I b hI hyI
  obtain ⟨q, hqy, a, haA, eqa⟩ := hTouch
  have hqb : q = b := by
    rcases hcover q with he | hqBlock
    · exact False.elim (hqy he)
    · rcases hqBlock with he | hqI
      · exact he
      · exact False.elim (hNoA q hqI a haA eqa)
  have eba : G.Adj (componentVertex C bt) a := by
    have hqbt : q = bt := hqb.trans hbtb.symm
    exact Eq.mp (congrArg (fun z : C.supp => G.Adj (componentVertex C z) a) hqbt) eqa
  have eyb : G.Adj y (componentVertex C bt) :=
    Eq.mp (congrArg (fun z : V => G.Adj z (componentVertex C bt)) hY) eybt
  have eya : G.Adj y a := by
    change a ∈ G.neighborSet y
    rw [hNY]
    exact Or.inr haA
  have hbtx : componentVertex C bt ≠ x := fun he => bt.1.2
    (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr hmax.1.2.2.1))
  have hax : a ≠ x := fun he => Set.disjoint_left.mp hmax.1.1
    (Eq.mp (congrArg (fun z : V => z ∈ A) he) haA) hmax.1.2.2.1
  exact htriY (componentVertex C bt) a hbtx hax eyb eba eya.symm

#print axioms terminal_common_point_single_leaf_boundary_cover
#print axioms casebi_original_y_leaf_boundary_in_first_block_contradiction
end TaskH.Gao
