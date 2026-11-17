import Research.TaskH.Six.TraceSixPairIdentity

/-!
The actual finite common-neighbor sets used by the path-pair identity.
The diamond quantity is indexed by ordered edges of the original graph.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u}

theorem trace_offDiag_card_eq_two_choose (s : Finset V) :
    s.offDiag.card = 2 * s.card.choose 2 := by
  calc
    s.offDiag.card = s.card * (s.card - 1) := by
      simp only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = s.card.descFactorial 2 := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_one]
      exact Nat.mul_comm _ _
    _ = 2 * s.card.choose 2 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      norm_num

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def traceCommonNeighbors (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) : Finset V := by
  classical
  exact G.neighborFinset a ∩ G.neighborFinset b

theorem mem_traceCommonNeighbors_iff (a b z : V) :
    z ∈ traceCommonNeighbors G a b ↔ G.Adj a z ∧ G.Adj b z := by
  classical
  simp [traceCommonNeighbors]

theorem traceCommonNeighbors_symm (a b : V) :
    traceCommonNeighbors G a b = traceCommonNeighbors G b a := by
  classical
  ext z
  simp only [mem_traceCommonNeighbors_iff, and_comm]

theorem traceCommonNeighbors_not_left (a b : V) :
    a ∉ traceCommonNeighbors G a b := by
  intro ha
  exact G.loopless.irrefl a ((mem_traceCommonNeighbors_iff a b a).mp ha).1

theorem traceCommonNeighbors_not_right (a b : V) :
    b ∉ traceCommonNeighbors G a b := by
  intro hb
  exact G.loopless.irrefl b ((mem_traceCommonNeighbors_iff a b b).mp hb).2

noncomputable def traceOrientedDiamondPairs (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  ∑ a : V, ∑ b ∈ G.neighborFinset a, (traceCommonNeighbors G a b).card.choose 2

end TaskH.Six

#print axioms TaskH.Six.trace_offDiag_card_eq_two_choose
#print axioms TaskH.Six.mem_traceCommonNeighbors_iff
#print axioms TaskH.Six.traceCommonNeighbors_symm
#print axioms TaskH.Six.traceCommonNeighbors_not_left
#print axioms TaskH.Six.traceCommonNeighbors_not_right
