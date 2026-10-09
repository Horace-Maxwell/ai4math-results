import Research.Backfill.Paper6.LiteralCounts

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralVennFinite

open Paper6InclusionExclusionVenn

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_nonempty4 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 4))).filter (fun U => U.Nonempty)), f U) = f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 4))).filter (fun U => U.Nonempty)) = ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_nonempty4

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_1 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_1

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_2 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({1} : Finset (Fin 4))), f U) = f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({1} : Finset (Fin 4))) = ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_2

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_3 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 1} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_3

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_4 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({2} : Finset (Fin 4))), f U) = f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({2} : Finset (Fin 4))) = ([({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_4

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_5 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 2} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 2} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_5

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_6 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({1, 2} : Finset (Fin 4))), f U) = f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({1, 2} : Finset (Fin 4))) = ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_6

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_7 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1, 2} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 1, 2} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_7

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_8 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({3} : Finset (Fin 4))), f U) = f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({3} : Finset (Fin 4))) = ([({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_8

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_9 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 3} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 3} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_9

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_10 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({1, 3} : Finset (Fin 4))), f U) = f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({1, 3} : Finset (Fin 4))) = ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_10

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_11 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1, 3} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 1, 3} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_11

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_12 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({2, 3} : Finset (Fin 4))), f U) = f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({2, 3} : Finset (Fin 4))) = ([({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_12

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_13 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 2, 3} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 2, 3} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_13

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_14 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({1, 2, 3} : Finset (Fin 4))), f U) = f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({1, 2, 3} : Finset (Fin 4))) = ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_14

/-- Finite index identity; the summand remains an opaque parameter. -/
theorem sum_meeting4_15 {α : Type*} [AddCommMonoid α] (f : Finset (Fin 4) → α) :
    (∑ U ∈ (meetingPatterns ({0, 1, 2, 3} : Finset (Fin 4))), f U) = f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : (meetingPatterns ({0, 1, 2, 3} : Finset (Fin 4))) = ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

#print axioms Paper6LiteralVennFinite.sum_meeting4_15

set_option maxHeartbeats 400000 in
theorem formula4 (r : Finset (Fin 4) → ℕ) :
    (∑ T ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun T => T.Nonempty),
      (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^
        (12 - ∑ U ∈ meetingPatterns T, r U)) =
      Paper6LiteralLouWang.vennWeight4 (r ({0} : Finset (Fin 4))) (r ({1} : Finset (Fin 4))) (r ({0, 1} : Finset (Fin 4))) (r ({2} : Finset (Fin 4))) (r ({0, 2} : Finset (Fin 4))) (r ({1, 2} : Finset (Fin 4))) (r ({0, 1, 2} : Finset (Fin 4))) (r ({3} : Finset (Fin 4))) (r ({0, 3} : Finset (Fin 4))) (r ({1, 3} : Finset (Fin 4))) (r ({0, 1, 3} : Finset (Fin 4))) (r ({2, 3} : Finset (Fin 4))) (r ({0, 2, 3} : Finset (Fin 4))) (r ({1, 2, 3} : Finset (Fin 4))) (r ({0, 1, 2, 3} : Finset (Fin 4))) := by
  have coeff_1 : (-2 : ℤ) ^ (({0} : Finset (Fin 4)).card - 1) = (1 : ℤ) := by decide
  have coeff_2 : (-2 : ℤ) ^ (({1} : Finset (Fin 4)).card - 1) = (1 : ℤ) := by decide
  have coeff_3 : (-2 : ℤ) ^ (({0, 1} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_4 : (-2 : ℤ) ^ (({2} : Finset (Fin 4)).card - 1) = (1 : ℤ) := by decide
  have coeff_5 : (-2 : ℤ) ^ (({0, 2} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_6 : (-2 : ℤ) ^ (({1, 2} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_7 : (-2 : ℤ) ^ (({0, 1, 2} : Finset (Fin 4)).card - 1) = (4 : ℤ) := by decide
  have coeff_8 : (-2 : ℤ) ^ (({3} : Finset (Fin 4)).card - 1) = (1 : ℤ) := by decide
  have coeff_9 : (-2 : ℤ) ^ (({0, 3} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_10 : (-2 : ℤ) ^ (({1, 3} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_11 : (-2 : ℤ) ^ (({0, 1, 3} : Finset (Fin 4)).card - 1) = (4 : ℤ) := by decide
  have coeff_12 : (-2 : ℤ) ^ (({2, 3} : Finset (Fin 4)).card - 1) = (-2 : ℤ) := by decide
  have coeff_13 : (-2 : ℤ) ^ (({0, 2, 3} : Finset (Fin 4)).card - 1) = (4 : ℤ) := by decide
  have coeff_14 : (-2 : ℤ) ^ (({1, 2, 3} : Finset (Fin 4)).card - 1) = (4 : ℤ) := by decide
  have coeff_15 : (-2 : ℤ) ^ (({0, 1, 2, 3} : Finset (Fin 4)).card - 1) = (-8 : ℤ) := by decide
  rw [sum_nonempty4]
  simp only [sum_meeting4_1, sum_meeting4_2, sum_meeting4_3, sum_meeting4_4, sum_meeting4_5, sum_meeting4_6, sum_meeting4_7, sum_meeting4_8, sum_meeting4_9, sum_meeting4_10, sum_meeting4_11, sum_meeting4_12, sum_meeting4_13, sum_meeting4_14, sum_meeting4_15, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6, coeff_7, coeff_8, coeff_9, coeff_10, coeff_11, coeff_12, coeff_13, coeff_14, coeff_15, Paper6LiteralLouWang.vennWeight4]

#print axioms Paper6LiteralVennFinite.formula4

end Paper6LiteralVennFinite
