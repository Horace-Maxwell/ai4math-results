import Research.TaskV.Stanley.Cell
import Research.TaskV.Stanley.Forest

namespace StanleyContinuation
noncomputable section

private theorem grouped_forest {n k q : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsTree)
    (s : Fin k → ℕ) (hq : q ≥ 2) :
    Nat.card (GroupColor (D := Fin q) G s) =
      ∑ f : Sized (V := Fin n) s, shadeWeight q s (cells G f.1) := by
  apply groupColor_count
  intro f c
  have hh := forest_proper_card (Cell G f.1 c) (hG.isAcyclic.induce _) q hq
  have hs : Nat.card {v : Fin n // f.1 v = c} = s c := congrFun f.2 c
  rw [← hs]
  exact hh

/-- All ordered counts of connected vertex partitions follow from the ordinary proper-coloring
coefficients. Only the induced-forest counting theorem uses the tree assumption. -/
theorem sameConnected_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.IsTree) (hH : H.IsTree) (h : SameCSF G H) : SameConnected G H := by
  classical
  intro k s
  by_cases hs : ∀ c, 0 < s c
  · rw [connCard_count G s hs, connCard_count H s hs]
    apply recover_rows s (fun f : Sized (V:=Fin n) s => cells G f.1)
      (fun f : Sized (V:=Fin m) s => cells H f.1)
    · intro a i
      apply cell_card_pos
      rw [a.2]
      exact hs i
    · intro b i
      apply cell_card_pos
      rw [b.2]
      exact hs i
    · intro q hq
      rw [← grouped_forest G hG s hq, ← grouped_forest H hH s hq]
      exact sameRefinementCard h s
  · push Not at hs
    obtain ⟨i,hi⟩ := hs
    have hi' : s i = 0 := by omega
    rw [zero_cell_coefficient G s i hi', zero_cell_coefficient H s i hi']

end
end StanleyContinuation
