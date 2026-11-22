import Research.TaskN.Antichain.TreeCode

namespace TaskN.Antichain

open Polynomial SimpleGraph

variable {V W : Type*}

theorem indep_no_edge (G : SimpleGraph V) (a : Finset V) :
    G.IsIndepSet (a : Set V) ↔ ∀ i ∈ a, ∀ j ∈ a, ¬ G.Adj i j := by
  constructor
  · intro h i hi j hj
    by_cases he : i = j
    · subst j
      simp
    · exact h hi hj he
  · exact fun h i hi j hj _ ↦ h i hi j hj

theorem indep_bridge_iff (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W)
    (a : Finset V) (b : Finset W) :
    (bridge G H v w).IsIndepSet (a.disjSum b : Set (V ⊕ W)) ↔
      G.IsIndepSet (a : Set V) ∧ H.IsIndepSet (b : Set W) ∧ ¬ (v ∈ a ∧ w ∈ b) := by
  have hc (i : V) (j : W) : ¬ (G.sum H).Adj (.inr j) (.inl i) := by
    intro h
    exact SimpleGraph.not_adj_sum_inl_inr i j h.symm
  simp only [indep_no_edge, Sum.forall, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
    bridge, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  simp only [SimpleGraph.sum_adj_inl, SimpleGraph.sum_adj_inr, SimpleGraph.not_adj_sum_inl_inr, hc]
  grind

noncomputable def atom (G : SimpleGraph V) (s : Finset V) : ℝ[X] := by
  classical
  exact if G.IsIndepSet (s : Set V) then X ^ s.card else 0

noncomputable def off (G : SimpleGraph V) (v : V) (s : Finset V) : ℝ[X] := by
  classical
  exact if v ∈ s then 0 else atom G s

noncomputable def excluded [Fintype V] (G : SimpleGraph V) (v : V) : ℝ[X] := ∑ s, off G v s

theorem atom_bridge (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W)
    (a : Finset V) (b : Finset W) :
    atom (bridge G H v w) (a.disjSum b) =
      off G v a * atom H b + (atom G a - off G v a) * off H w b := by
  classical
  by_cases ha : G.IsIndepSet (a : Set V) <;> by_cases hb : H.IsIndepSet (b : Set W) <;>
    by_cases hv : v ∈ a <;> by_cases hw : w ∈ b <;>
    simp [atom, off, indep_bridge_iff, ha, hb, hv, hw, Finset.card_disjSum, pow_add]

theorem off_bridge (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W)
    (a : Finset V) (b : Finset W) :
    off (bridge G H v w) (.inl v) (a.disjSum b) = off G v a * atom H b := by
  classical
  by_cases hv : v ∈ a <;> simp [off, hv, atom_bridge]

theorem sum_bridge_atoms [Fintype V] [Fintype W] (f : Finset (V ⊕ W) → ℝ[X]) :
    ∑ s, f s = ∑ a : Finset V, ∑ b : Finset W, f (a.disjSum b) := by
  classical
  calc
    _ = ∑ z : Finset V × Finset W, f (z.1.disjSum z.2) :=
      (Equiv.sum_comp (Finset.sumEquiv.toEquiv.symm) f).symm
    _ = _ := Fintype.sum_prod_type _

theorem ip_bridge [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) :
    Challenge.independencePolynomial (bridge G H v w) =
      excluded G v * Challenge.independencePolynomial H +
      (Challenge.independencePolynomial G - excluded G v) * excluded H w := by
  classical
  change (∑ s, atom (bridge G H v w) s) = _
  rw [sum_bridge_atoms]
  simp_rw [atom_bridge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← Finset.sum_mul, ← Finset.sum_sub_distrib, excluded, Challenge.independencePolynomial, atom]

theorem excluded_bridge [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) :
    excluded (bridge G H v w) (.inl v) = excluded G v * Challenge.independencePolynomial H := by
  classical
  change (∑ s, off (bridge G H v w) (.inl v) s) = _
  rw [sum_bridge_atoms]
  simp_rw [off_bridge, ← Finset.mul_sum]
  simp only [← Finset.sum_mul, excluded, Challenge.independencePolynomial, atom]

end TaskN.Antichain
