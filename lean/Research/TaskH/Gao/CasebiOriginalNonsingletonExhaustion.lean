import Research.TaskH.Gao.CasebiNoYTerminalOriginal
import Research.TaskH.Gao.CasebiOriginalYTerminalExit

/-! Original actual nonsingleton y-component: internally select the actual
A-touch, decide the intrinsic terminal branch, and choose all terminal data.
The existing complete no-y source is reused unchanged, not reproved here. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_nonsingleton_original_family [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (hxy : ¬G.Adj x y)
    (htri : CasebiNoRootTriangle G x y) (htriY : CasebiNoRootTriangle G y x)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (L : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected L a d →
      NonrootDegreeAtLeast L a d (r + 1) → HasAdmissiblePaths L a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (hC : 2 ≤ Fintype.card C.supp) : HasAdmissiblePaths G x y k := by
  classical
  by_contra hno
  have hTouch : ∃ q : C.supp, q ≠ yr ∧ ∃ a ∈ A, G.Adj (componentVertex C q) a := by
    by_contra hn
    have hcase : ∀ q : C.supp, q ≠ yr → ∀ a ∈ A, ¬G.Adj (componentVertex C q) a := by
      intro q hqy a ha eqa
      exact hn ⟨q, hqy, a, ha, eqa⟩
    exact casebi_nonsingleton_case_one_contradiction G A B x y s k hmax hBs hk
      hG htri hquad hd hno ih C yr hY hC hcase
  by_cases hYTerminal : ∃ (J : Set C.supp) (bt : C.supp),
      TerminalFragment C.toSimpleGraph J bt ∧ yr ∈ J
  · obtain ⟨J, bt, hJ, hyJ⟩ := hYTerminal
    obtain ⟨I, b, hI, hyI, _hI2, _hF, _R, _hR, _hRQ, _hRB⟩ :=
      casebi_actual_feasible_block_exists G A B x y s k hmax hBs hk htri hquad hd hno C yr hY hC
    exact casebi_original_y_terminal_contradiction G A B x y s k hmax hBs hk hG hxy
      htri htriY hquad hd hno horder ih C yr hY I b hI hyI J bt hJ hyJ hTouch
  · have hNoY : ∀ (J : Set C.supp) (bt : C.supp),
        TerminalFragment C.toSimpleGraph J bt → yr ∉ J := by
      intro J bt hJ hyJ
      exact hYTerminal ⟨J, bt, hJ, hyJ⟩
    exact hno (casebi_nonsingleton_no_y_terminal_original G A B x y s k hmax hBs hk
      hG htri hquad hd ih C yr hY hC hNoY)

theorem casebi_actual_y_component_nonsingleton_original_family [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (hxy : ¬G.Adj x y)
    (htri : CasebiNoRootTriangle G x y) (htriY : CasebiNoRootTriangle G y x)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (L : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected L a d →
      NonrootDegreeAtLeast L a d (r + 1) → HasAdmissiblePaths L a d r)
    (hC : 2 ≤ Nat.card ((G.induce (A ∪ B)ᶜ).connectedComponentMk
      ⟨y, hmax.1.2.2.2.1⟩).supp) : HasAdmissiblePaths G x y k := by
  classical
  let C := (G.induce (A ∪ B)ᶜ).connectedComponentMk ⟨y, hmax.1.2.2.2.1⟩
  let yr : C.supp := ⟨⟨y, hmax.1.2.2.2.1⟩, rfl⟩
  let : Fintype C.supp := Fintype.ofFinite _
  have hC' : 2 ≤ Fintype.card C.supp := by
    simpa only [Fintype.card_eq_nat_card] using hC
  exact casebi_nonsingleton_original_family G A B x y s k hmax hBs hk hG hxy htri htriY
    hquad hd horder ih C yr rfl hC'

#print axioms casebi_nonsingleton_original_family
#print axioms casebi_actual_y_component_nonsingleton_original_family
end TaskH.Gao
