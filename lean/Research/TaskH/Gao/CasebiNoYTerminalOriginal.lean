import Research.TaskH.Gao.CarrierCentralTerminalLinkage
import Research.TaskH.Gao.CasebiTerminalFreePair

/-! The original nonsingleton intrinsic no-y-terminal branch. The actual
w/A-neighbor, order bound, central carrier and both terminal routes are all
selected inside the proof, before applying the existing exact contradiction. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_nonsingleton_no_y_terminal_original [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (hC : 2 ≤ Fintype.card C.supp)
    (hNoY : ∀ I b, TerminalFragment C.toSimpleGraph I b → yr ∉ I) :
    HasAdmissiblePaths G x y k := by
  classical
  by_contra hno
  have hex : ∃ w : C.supp, w ≠ yr ∧ ∃ q ∈ A, G.Adj (componentVertex C w) q := by
    by_contra hn
    have hcase : ∀ w : C.supp, w ≠ yr → ∀ q ∈ A, ¬G.Adj (componentVertex C w) q := by
      intro w hwy q hq ewq
      exact hn ⟨w, hwy, q, hq, ewq⟩
    exact casebi_nonsingleton_case_one_contradiction G A B x y s k hmax hBs hk
      hG htri hquad hd hno ih C yr hY hC hcase
  obtain ⟨w, hwy, q, hq, ewq⟩ := hex
  have hwavoid : ∀ I b, TerminalFragment C.toSimpleGraph I b → w ∉ I := by
    intro I b hT hwI
    have hA := casebi_feasible_no_first_part G A B x y s k hmax hBs hk hG htri hquad
      hd hno ih C yr hY I b hT (hNoY I b hT)
    exact hA w hwI q hq ewq
  have hdeg := casebi_component_no_nonroot_leaf G A B x y s k hmax hBs hk
    htri hquad hd hno C yr hY w hwy
  have hself : w ∉ C.toSimpleGraph.neighborSet w := C.toSimpleGraph.irrefl
  have hbound := Set.ncard_le_card (insert w (C.toSimpleGraph.neighborSet w))
  rw [Set.ncard_insert_of_notMem hself] at hbound
  change (C.toSimpleGraph.neighborSet w).ncard + 1 ≤ Nat.card C.supp at hbound
  have hVnat : 3 ≤ Nat.card C.supp := by omega
  have hV : 3 ≤ Fintype.card C.supp := by
    simpa only [Fintype.card_eq_nat_card] using hVnat
  obtain ⟨hGw, hGy, hpair⟩ := casebi_no_y_terminal_pair_unseparated G A B x y s k
    hmax hBs hk hG htri hquad hd hno ih C yr w hY hwy hNoY q hq ewq
  have hroute := terminal_routes_from_intrinsic_terminal_free_pair C.toSimpleGraph w yr hwy
    C.connected_toSimpleGraph hV hGw hGy hpair hwavoid hNoY
  exact casebi_two_terminal_routes_contradiction G A B x y s k hmax hBs hk hG htri hquad
    hd hno ih C yr w hY hNoY q hq ewq hroute

#print axioms casebi_nonsingleton_no_y_terminal_original
end TaskH.Gao
