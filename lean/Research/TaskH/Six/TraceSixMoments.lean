import Mathlib

/-! Degree moments of the actual finite graph in the trace-six argument. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def traceDegreeMoment (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) : ℝ :=
  ∑ v : V, (G.degree v : ℝ) ^ r

noncomputable def traceOrderedDegreeProduct (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  ∑ v : V, ∑ w ∈ G.neighborFinset v, (G.degree v : ℝ) * (G.degree w : ℝ)

theorem trace_degree_cube_secant
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) (v : V) :
    28 * (G.degree v : ℝ) ^ 3 + 34969 ≤ 597 * (G.degree v : ℝ) ^ 2 := by
  have hl : (11 : ℝ) ≤ G.degree v := by exact_mod_cast hlo v
  have hu : (G.degree v : ℝ) ≤ 17 := by exact_mod_cast hhi v
  have hp : ((G.degree v : ℝ) - 11) * ((G.degree v : ℝ) - 17) *
      (28 * (G.degree v : ℝ) + 187) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by positivity)
  nlinarith [hp]

theorem trace_degree_fourth_secant
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) (v : V) :
    (G.degree v : ℝ) ^ 4 + 34969 ≤ 410 * (G.degree v : ℝ) ^ 2 := by
  have hl : (11 : ℝ) ≤ G.degree v := by exact_mod_cast hlo v
  have hu : (G.degree v : ℝ) ≤ 17 := by exact_mod_cast hhi v
  have hl2 : (121 : ℝ) ≤ (G.degree v : ℝ) ^ 2 := by nlinarith
  have hu2 : (G.degree v : ℝ) ^ 2 ≤ 289 := by nlinarith
  have hp : ((G.degree v : ℝ) ^ 2 - 121) * ((G.degree v : ℝ) ^ 2 - 289) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith [hp]

theorem trace_degree_first_moment_lower
    (hlo : ∀ v : V, 11 ≤ G.degree v) :
    11 * (Fintype.card V : ℝ) ≤ traceDegreeMoment G 1 := by
  calc
    _ = ∑ _v : V, (11 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum (fun v _ => by
      exact_mod_cast hlo v)
    _ = _ := by simp [traceDegreeMoment]

theorem trace_degree_first_moment_upper
    (hhi : ∀ v : V, G.degree v ≤ 17) :
    traceDegreeMoment G 1 ≤ 17 * (Fintype.card V : ℝ) := by
  calc
    _ = ∑ v : V, (G.degree v : ℝ) := by simp [traceDegreeMoment]
    _ ≤ ∑ _v : V, (17 : ℝ) := Finset.sum_le_sum (fun v _ => by
      exact_mod_cast hhi v)
    _ = _ := by simp [mul_comm]

theorem trace_degree_second_moment_lower
    (hlo : ∀ v : V, 11 ≤ G.degree v) :
    121 * (Fintype.card V : ℝ) ≤ traceDegreeMoment G 2 := by
  calc
    _ = ∑ _v : V, (121 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ v : V, (G.degree v : ℝ) ^ 2 := Finset.sum_le_sum (fun v _ => by
      have hl : (11 : ℝ) ≤ G.degree v := by exact_mod_cast hlo v
      nlinarith)
    _ = _ := rfl

theorem trace_degree_cube_moment_bound
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) :
    28 * traceDegreeMoment G 3 + 34969 * (Fintype.card V : ℝ) ≤
      597 * traceDegreeMoment G 2 := by
  calc
    _ = ∑ v : V, (28 * (G.degree v : ℝ) ^ 3 + 34969) := by
      simp [traceDegreeMoment, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
    _ ≤ ∑ v : V, 597 * (G.degree v : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun v _ => trace_degree_cube_secant hlo hhi v)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem trace_degree_fourth_moment_bound
    (hlo : ∀ v : V, 11 ≤ G.degree v) (hhi : ∀ v : V, G.degree v ≤ 17) :
    traceDegreeMoment G 4 + 34969 * (Fintype.card V : ℝ) ≤
      410 * traceDegreeMoment G 2 := by
  calc
    _ = ∑ v : V, ((G.degree v : ℝ) ^ 4 + 34969) := by
      simp [traceDegreeMoment, Finset.sum_add_distrib, mul_comm]
    _ ≤ ∑ v : V, 410 * (G.degree v : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun v _ => trace_degree_fourth_secant hlo hhi v)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem trace_ordered_degree_product_lower
    (hlo : ∀ v : V, 11 ≤ G.degree v) :
    11 * traceDegreeMoment G 2 ≤ traceOrderedDegreeProduct G := by
  have hrow : ∀ v : V, 11 * (G.degree v : ℝ) ^ 2 ≤
      ∑ w ∈ G.neighborFinset v, (G.degree v : ℝ) * (G.degree w : ℝ) := by
    intro v
    calc
      _ = ∑ _w ∈ G.neighborFinset v, (G.degree v : ℝ) * 11 := by
        simp only [Finset.sum_const, G.card_neighborFinset_eq_degree,
          nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun w _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlo w) (by positivity))
  calc
    _ = ∑ v : V, 11 * (G.degree v : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]; rfl
    _ ≤ _ := Finset.sum_le_sum (fun v _ => hrow v)

end TaskH.Six

#print axioms TaskH.Six.trace_degree_cube_secant
#print axioms TaskH.Six.trace_degree_fourth_secant
#print axioms TaskH.Six.trace_degree_first_moment_lower
#print axioms TaskH.Six.trace_degree_first_moment_upper
#print axioms TaskH.Six.trace_degree_second_moment_lower
#print axioms TaskH.Six.trace_degree_cube_moment_bound
#print axioms TaskH.Six.trace_degree_fourth_moment_bound
#print axioms TaskH.Six.trace_ordered_degree_product_lower
