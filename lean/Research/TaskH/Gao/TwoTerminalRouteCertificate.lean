import Research.TaskH.Gao.TwoTerminalEndpointCut

/-! Intrinsic output certificate, selected from actual cut data; no block list input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def TwoTerminalRoutes (G : SimpleGraph V) (w y : V) : Prop :=
  ∃ (I J : Set V) (b c : V),
    TerminalFragment G I b ∧ TerminalFragment G J c ∧
    Disjoint (fragmentBlock I b) (fragmentBlock J c) ∧
    ∃ (P : G.Walk b w) (R : G.Walk c y), P.IsPath ∧ R.IsPath ∧
      (∀ v ∈ P.support, v ∉ I) ∧ (∀ v ∈ R.support, v ∉ J) ∧
      (∀ v ∈ P.support, v ∉ R.support) ∧
      (∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b) ∧
      (∀ v ∈ R.support, v ∈ fragmentBlock J c → v = c) ∧
      (∀ v ∈ P.support, v ∉ fragmentBlock J c) ∧
      (∀ v ∈ R.support, v ∉ fragmentBlock I b)

theorem twoTerminalRoutes_swap (G : SimpleGraph V) (w y : V)
    (h : TwoTerminalRoutes G w y) : TwoTerminalRoutes G y w := by
  obtain ⟨I, J, b, c, hI, hJ, hIJ, P, R, hP, hR, hPI, hRJ, hPR, hPB, hRB, hPJ, hRI⟩ := h
  refine ⟨J, I, c, b, hJ, hI, hIJ.symm, R, P, hR, hP, hRJ, hPI, ?_,
    hRB, hPB, hRI, hPJ⟩
  intro v hvR hvP
  exact hPR v hvP hvR

theorem twoTerminalRoutes_of_actual_cut_cases [Fintype V] (G : SimpleGraph V)
    (w y : V) (hwy : w ≠ y) (hG : G.Connected)
    (hwavoid : ∀ I b, TerminalFragment G I b → w ∉ I)
    (hyavoid : ∀ I b, TerminalFragment G I b → y ∉ I)
    (hcase : (¬(G.induce {v | v ≠ w}).Connected) ∨
      (¬(G.induce {v | v ≠ y}).Connected) ∨
      ∃ (z : V) (hwz : w ≠ z) (hyz : y ≠ z),
        (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ ≠
          (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩) :
    TwoTerminalRoutes G w y := by
  rcases hcase with hwcut | hycut | ⟨z, hwz, hyz, hsep⟩
  · exact terminal_routes_from_cut_at_first_endpoint G w y hwy.symm hG hwcut hyavoid
  · exact twoTerminalRoutes_swap G y w
      (terminal_routes_from_cut_at_first_endpoint G y w hwy hG hycut hwavoid)
  · obtain ⟨I, J, b, c, hI, hJ, hIJ, _hIS, _hJT, P, R, hP, hR,
      hPS, hRT, hPR, hPB, hRB, hPJ, hRI⟩ :=
        terminal_routes_across_actual_separating_cut G w y z hwz hyz hG hsep hwavoid hyavoid
    exact ⟨I, J, b, c, hI, hJ, hIJ, P, R, hP, hR,
      (fun v hv => (hPS v hv).2), (fun v hv => (hRT v hv).2), hPR, hPB, hRB, hPJ, hRI⟩

#print axioms TwoTerminalRoutes
#print axioms twoTerminalRoutes_swap
#print axioms twoTerminalRoutes_of_actual_cut_cases
end TaskH.Gao
