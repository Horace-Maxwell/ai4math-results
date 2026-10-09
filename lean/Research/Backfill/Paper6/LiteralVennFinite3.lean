import Research.Backfill.Paper6.LiteralCounts

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralVennFinite

open Paper6InclusionExclusionVenn

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_nonempty3 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => U.Nonempty)), f U) = f ({0} : Finset (Fin 3)) + f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => U.Nonempty)) = ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_nonempty3

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_1 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({0} : Finset (Fin 3))), f U) = f ({0} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({0} : Finset (Fin 3))) = ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_1

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_2 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({1} : Finset (Fin 3))), f U) = f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({1} : Finset (Fin 3))) = ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_2

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_3 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1} : Finset (Fin 3))), f U) = f ({0} : Finset (Fin 3)) + f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({0, 1} : Finset (Fin 3))) = ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_3

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_4 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({2} : Finset (Fin 3))), f U) = f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({2} : Finset (Fin 3))) = ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_4

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_5 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({0, 2} : Finset (Fin 3))), f U) = f ({0} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({0, 2} : Finset (Fin 3))) = ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_5

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_6 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({1, 2} : Finset (Fin 3))), f U) = f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({1, 2} : Finset (Fin 3))) = ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_6

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting3_7 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 3) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1, 2} : Finset (Fin 3))), f U) = f ({0} : Finset (Fin 3)) + f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : (meetingPatterns ({0, 1, 2} : Finset (Fin 3))) = ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting3_7

set_option maxHeartbeats 400000 in
theorem formula3 (r : Finset (Fin 3) → ℕ) :
    (∑ T ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun T => T.Nonempty),
      (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^
        (12 - ∑ U ∈ meetingPatterns T, r U)) =
      Paper6LiteralLouWang.vennWeight3 (r ({0} : Finset (Fin 3))) (r ({1} : Finset (Fin 3))) (r ({0, 1} : Finset (Fin 3))) (r ({2} : Finset (Fin 3))) (r ({0, 2} : Finset (Fin 3))) (r ({1, 2} : Finset (Fin 3))) (r ({0, 1, 2} : Finset (Fin 3))) := by
  have coeff_1 : (-2 : ℤ) ^ (({0} : Finset (Fin 3)).card - 1) = (1 : ℤ) := by decide
  have coeff_2 : (-2 : ℤ) ^ (({1} : Finset (Fin 3)).card - 1) = (1 : ℤ) := by decide
  have coeff_3 : (-2 : ℤ) ^ (({0, 1} : Finset (Fin 3)).card - 1) = (-2 : ℤ) := by decide
  have coeff_4 : (-2 : ℤ) ^ (({2} : Finset (Fin 3)).card - 1) = (1 : ℤ) := by decide
  have coeff_5 : (-2 : ℤ) ^ (({0, 2} : Finset (Fin 3)).card - 1) = (-2 : ℤ) := by decide
  have coeff_6 : (-2 : ℤ) ^ (({1, 2} : Finset (Fin 3)).card - 1) = (-2 : ℤ) := by decide
  have coeff_7 : (-2 : ℤ) ^ (({0, 1, 2} : Finset (Fin 3)).card - 1) = (4 : ℤ) := by decide
  rw [sum_nonempty3]
  simp only [sum_meeting3_1, sum_meeting3_2, sum_meeting3_3, sum_meeting3_4, sum_meeting3_5, sum_meeting3_6, sum_meeting3_7, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, Paper6LiteralLouWang.vennWeight3]

#print axioms Paper6LiteralVennFinite.formula3

end Paper6LiteralVennFinite
