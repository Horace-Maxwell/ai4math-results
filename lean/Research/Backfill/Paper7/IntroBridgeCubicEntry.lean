import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! Exact short-walk entries from actual bridge edges. No local tree profile
or list of allowed branches is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

theorem bridge_vertex_square_common_neighbor_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a))
    (j k : V) (hj : j ≠ v) (hvk : G.Adj v k) (hkj : G.Adj k j) :
    ((G.adjMatrix ℝ) ^ 2) v j = 1 := by
  have he : (G.neighborFinset v).filter (fun a => G.Adj a j) = {k} := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, haj⟩
      exact bridge_vertex_common_neighbor_unique G v hbridge j hj a k
        ((G.mem_neighborFinset v a).mp ha) haj hvk hkj
    · intro hak
      subst a
      exact ⟨(G.mem_neighborFinset v k).mpr hvk, hkj⟩
  rw [adjacency_square_common_card, he, Finset.card_singleton, Nat.cast_one]
#print axioms Paper7IntroTerminalFourRemote.bridge_vertex_square_common_neighbor_one

theorem bridge_vertex_cube_neighbor_entry
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a))
    (p : V) (hvp : G.Adj v p) :
    ((G.adjMatrix ℝ) ^ 3) v p = (G.degree v : ℝ) + (G.degree p : ℝ) - 1 := by
  have hvN : v ∈ G.neighborFinset p := (G.mem_neighborFinset p v).mpr hvp.symm
  have hdiag : ((G.adjMatrix ℝ) ^ 2) v v = (G.degree v : ℝ) := by
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hs : (∑ j ∈ (G.neighborFinset p).erase v, ((G.adjMatrix ℝ) ^ 2) v j) =
      (((G.neighborFinset p).erase v).card : ℝ) := by
    calc
      _ = ∑ _j ∈ (G.neighborFinset p).erase v, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        obtain ⟨hjv, hjN⟩ := Finset.mem_erase.mp hj
        exact bridge_vertex_square_common_neighbor_one G v hbridge j p hjv hvp
          ((G.mem_neighborFinset p j).mp hjN)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc := Finset.card_erase_add_one hvN
  rw [G.card_neighborFinset_eq_degree] at hc
  have hcR : (((G.neighborFinset p).erase v).card : ℝ) + 1 = (G.degree p : ℝ) := by
    exact_mod_cast hc
  rw [show (G.adjMatrix ℝ) ^ 3 = (G.adjMatrix ℝ) ^ 2 * G.adjMatrix ℝ from
    pow_succ (G.adjMatrix ℝ) 2, G.mul_adjMatrix_apply,
    ← Finset.add_sum_erase (G.neighborFinset p) (fun j => ((G.adjMatrix ℝ) ^ 2) v j) hvN,
    hdiag, hs]
  linarith
#print axioms Paper7IntroTerminalFourRemote.bridge_vertex_cube_neighbor_entry

end Paper7IntroTerminalFourRemote
