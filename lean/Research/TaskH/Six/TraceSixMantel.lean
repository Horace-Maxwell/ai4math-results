import Research.TaskH.Six.TraceSixMoments

/-! The local triangle count is the actual edge count of the induced neighborhood graph. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def traceLocalTriangleCount (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.induce (G.neighborSet v)).edgeFinset.card

noncomputable def traceTriangleMoment (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) : ℝ :=
  ∑ v : V, (traceLocalTriangleCount G v : ℝ) ^ r

omit [Fintype V] [DecidableRel G.Adj] in
theorem trace_neighbor_cliqueFree (hG : G.CliqueFree 4) (v : V) :
    (G.induce (G.neighborSet v)).CliqueFree 3 := by
  rw [SimpleGraph.cliqueFree_induce_iff]
  have hu : G.CliqueFreeOn Set.univ (3 + 1) := hG.cliqueFreeOn
  have hn := SimpleGraph.CliqueFreeOn.of_succ G hu (Set.mem_univ v)
  simpa only [Set.univ_inter] using hn

theorem trace_local_triangle_mantel (hG : G.CliqueFree 4) (v : V) :
    4 * traceLocalTriangleCount G v ≤ (G.degree v) ^ 2 := by
  have he := (trace_neighbor_cliqueFree hG v).card_edgeFinset_le
  have ht := SimpleGraph.mul_turanNumber_le (n := G.degree v) (r := 2)
  change traceLocalTriangleCount G v ≤
    SimpleGraph.turanNumber (Fintype.card (G.neighborSet v)) 2 at he
  rw [G.card_neighborSet_eq_degree] at he
  exact (Nat.mul_le_mul_left 4 he).trans (by simpa using ht)

theorem trace_local_triangle_square_bound (hG : G.CliqueFree 4) (v : V) :
    12 * (traceLocalTriangleCount G v : ℝ) ^ 2 ≤
      (3 / 4 : ℝ) * (G.degree v : ℝ) ^ 4 := by
  have hm : (4 : ℝ) * traceLocalTriangleCount G v ≤ (G.degree v : ℝ) ^ 2 := by
    exact_mod_cast trace_local_triangle_mantel hG v
  have hs := mul_self_le_mul_self (by positivity :
    (0 : ℝ) ≤ 4 * traceLocalTriangleCount G v) hm
  nlinarith [hs]

theorem trace_triangle_square_moment_bound (hG : G.CliqueFree 4) :
    12 * traceTriangleMoment G 2 ≤ (3 / 4 : ℝ) * traceDegreeMoment G 4 := by
  calc
    _ = ∑ v : V, 12 * (traceLocalTriangleCount G v : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]; rfl
    _ ≤ ∑ v : V, (3 / 4 : ℝ) * (G.degree v : ℝ) ^ 4 :=
      Finset.sum_le_sum (fun v _ => trace_local_triangle_square_bound hG v)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end TaskH.Six

#print axioms TaskH.Six.trace_neighbor_cliqueFree
#print axioms TaskH.Six.trace_local_triangle_mantel
#print axioms TaskH.Six.trace_local_triangle_square_bound
#print axioms TaskH.Six.trace_triangle_square_moment_bound
