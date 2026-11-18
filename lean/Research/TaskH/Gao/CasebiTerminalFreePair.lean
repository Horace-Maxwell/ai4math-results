import Research.TaskH.Gao.CasebiNoYTerminalCutCase

/-!
Exact original-counterexample consequence for the still-owed same-block case.
This says the two actual vertices survive in one component after other
single deletions; it does not assert all those deleted graphs are connected.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_no_y_terminal_pair_unseparated [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr w : C.supp) (hY : componentVertex C yr = y) (hwy : w ≠ yr)
    (hNoY : ∀ I b, TerminalFragment C.toSimpleGraph I b → yr ∉ I)
    (q : V) (hq : q ∈ A) (ewq : G.Adj (componentVertex C w) q) :
    (C.toSimpleGraph.induce {v | v ≠ w}).Connected ∧
      (C.toSimpleGraph.induce {v | v ≠ yr}).Connected ∧
      ∀ (z : C.supp) (hwz : w ≠ z) (hyz : yr ≠ z),
        (C.toSimpleGraph.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ =
          (C.toSimpleGraph.induce {v | v ≠ z}).connectedComponentMk ⟨yr, hyz⟩ := by
  classical
  have hCut := casebi_no_y_terminal_cut_case_contradiction G A B x y s k hmax hBs hk
    hG htri hquad hd hno ih C yr w hY hwy hNoY q hq ewq
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hCut (Or.inl h)
  · by_contra h
    exact hCut (Or.inr (Or.inl h))
  · intro z hwz hyz
    by_contra h
    exact hCut (Or.inr (Or.inr ⟨z, hwz, hyz, h⟩))

#print axioms casebi_no_y_terminal_pair_unseparated
end TaskH.Gao
