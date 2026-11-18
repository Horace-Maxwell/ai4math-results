import Research.TaskH.Gao.CasebiTwoTerminalContradiction

/-!
Closed original Case2 subcase: a real cut at w/y or a cut separating w and y
is impossible when y lies in no terminal interior. No terminal/path/block
certificate is supplied to this theorem; it is constructed in its proof.
The same-block, no-separating-cut case and the hub completion remain owed.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_no_y_terminal_cut_case_contradiction [Fintype V] (G : SimpleGraph V)
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
    (q : V) (hq : q ∈ A) (ewq : G.Adj (componentVertex C w) q)
    (hcase : (¬(C.toSimpleGraph.induce {v | v ≠ w}).Connected) ∨
      (¬(C.toSimpleGraph.induce {v | v ≠ yr}).Connected) ∨
      ∃ (z : C.supp) (hwz : w ≠ z) (hyz : yr ≠ z),
        (C.toSimpleGraph.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ ≠
          (C.toSimpleGraph.induce {v | v ≠ z}).connectedComponentMk ⟨yr, hyz⟩) : False := by
  have hwavoid : ∀ I b, TerminalFragment C.toSimpleGraph I b → w ∉ I := by
    intro I b hT hwI
    have hA := casebi_feasible_no_first_part G A B x y s k hmax hBs hk hG htri hquad
      hd hno ih C yr hY I b hT (hNoY I b hT)
    exact hA w hwI q hq ewq
  have hroutes := twoTerminalRoutes_of_actual_cut_cases C.toSimpleGraph w yr hwy
    C.connected_toSimpleGraph hwavoid hNoY hcase
  exact casebi_two_terminal_routes_contradiction G A B x y s k hmax hBs hk hG htri hquad
    hd hno ih C yr w hY hNoY q hq ewq hroutes

#print axioms casebi_no_y_terminal_cut_case_contradiction
end TaskH.Gao
