import Research.TaskN.Antichain.BridgeWeights

namespace TaskN.Antichain

open Polynomial SimpleGraph

private theorem subset_enum : (Finset.univ : Finset (Finset Unit)) = {∅, {()}} := by decide

theorem RT.polynomial_pair (t : RT) :
    Challenge.independencePolynomial t.graph = t.pair.1 ∧ excluded t.graph t.root = t.pair.2 := by
  classical
  induction t with
  | leaf =>
    change Challenge.independencePolynomial (⊥ : SimpleGraph Unit) = 1 + X ∧
      excluded (⊥ : SimpleGraph Unit) () = 1
    have hi (s : Finset Unit) : (⊥ : SimpleGraph Unit).IsIndepSet (s : Set Unit) := by
      rw [indep_no_edge]
      simp
    simp [Challenge.independencePolynomial, excluded, off, atom, hi, subset_enum]
  | link l r il ir =>
    change Challenge.independencePolynomial (bridge l.graph r.graph l.root r.root) = _ ∧
      excluded (bridge l.graph r.graph l.root r.root) (.inl l.root) = _
    rw [ip_bridge, excluded_bridge, il.1, il.2, ir.1, ir.2]
    exact ⟨rfl,rfl⟩

end TaskN.Antichain
