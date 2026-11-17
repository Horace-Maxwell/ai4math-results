import Research.TaskH.Six.TraceSixDefectIdentity
import Research.TaskH.Six.SixTraceScalarBudget

/-!
The bare actual-graph trace bound.  Nonempty is explicit because the
normalization divides by the actual vertex cardinality.  All matrix,
overlap, degree and triangle facts are derived by the imported graph
modules; there are no abstract count, norm or trace-identity premises.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] [Nonempty V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_actual_six_cycle_rational_lower (hcf : G.CliqueFree 4)
    (hcard : Fintype.card V ≤ 37)
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) :
    (14586215 / 28 : ℝ) ≤ 12 * ((actualSixEdgeSets G).card : ℝ) := by
  let n : ℝ := Fintype.card V
  let h : ℝ := traceDegreeMoment G 2 / n
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos (α := V))
  have hn37 : n ≤ 37 := by
    change (Fintype.card V : ℝ) ≤ 37
    exact_mod_cast hcard
  have hsecond : 121 * n ≤ traceDegreeMoment G 2 :=
    trace_degree_second_moment_lower (G := G) hlo
  have hh : 121 ≤ h := by
    dsimp [h]
    exact (le_div_iff₀ hn).mpr hsecond
  have hrel : n * h = traceDegreeMoment G 2 := by
    dsimp [h]
    field_simp [ne_of_gt hn]
  have hnorm : (8 * h + 33) ^ 2 ≤ traceDefectSquare G :=
    trace_defect_square_lower (G := G) hlo
  have hc := trace_actual_six_cycle_frobenius_identity (G := G)
  have hQ := trace_ordered_degree_product_lower (G := G) hlo
  have h3 : 28 * traceDegreeMoment G 3 + 34969 * n ≤ 597 * traceDegreeMoment G 2 :=
    trace_degree_cube_moment_bound (G := G) hlo hhi
  have h4 : traceDegreeMoment G 4 + 34969 * n ≤ 410 * traceDegreeMoment G 2 :=
    trace_degree_fourth_moment_bound (G := G) hlo hhi
  have h1 : traceDegreeMoment G 1 ≤ 17 * n :=
    trace_degree_first_moment_upper (G := G) hhi
  have hMantel := trace_triangle_square_moment_bound (G := G) hcf
  have hT : 0 ≤ traceTriangleMoment G 1 := by
    unfold traceTriangleMoment
    positivity
  have hD : 0 ≤ (traceOrientedDiamondPairs G : ℝ) := by positivity
  have hbase : (8 * h + 33) ^ 2 - (10503 / 28) * traceDegreeMoment G 2 +
      (453407 / 14) * n ≤ 12 * ((actualSixEdgeSets G).card : ℝ) := by
    linarith only [hc, hnorm, hQ, h3, h4, h1, hMantel, hT, hD]
  have he : (8 * h + 33) ^ 2 + n * (-(10503 / 28) * h + 453407 / 14) =
      (8 * h + 33) ^ 2 - (10503 / 28) * traceDegreeMoment G 2 + (453407 / 14) * n := by
    nlinarith only [hrel]
  have hs := trace_six_scalar_lower_bound n h hn37 hh
  rw [he] at hs
  exact hs.trans hbase

theorem trace_actual_six_cycle_card_lower (hcf : G.CliqueFree 4)
    (hcard : Fintype.card V ≤ 37)
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) :
    43412 ≤ (actualSixEdgeSets G).card := by
  exact trace_six_integral_cycle_count_lower (actualSixEdgeSets G).card
    (trace_actual_six_cycle_rational_lower hcf hcard hlo hhi)

theorem trace_mod_six_cycle_count_lower (hcf : G.CliqueFree 4)
    (hcard : Fintype.card V ≤ 37)
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) :
    43412 ≤ modCycleCount 6 G := by
  exact (trace_actual_six_cycle_card_lower hcf hcard hlo hhi).trans
    (actualSixEdgeSets_card_le_modCycleCount (G := G))

end TaskH.Six

#print axioms TaskH.Six.trace_actual_six_cycle_rational_lower
#print axioms TaskH.Six.trace_actual_six_cycle_card_lower
#print axioms TaskH.Six.trace_mod_six_cycle_count_lower
