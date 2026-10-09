import Research.Backfill.Paper6.PairSemantic
import Research.Backfill.Paper6.PairCounts

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem univ_patterns0 : (Finset.univ : Finset (Finset (Fin 0))) =
    {(∅ : Finset (Fin 0))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns0

theorem univ_indices0 : (Finset.univ : Finset (Fin 0)) = ∅ := by decide

#print axioms Paper6FiveExclusion.univ_indices0

theorem univ_patterns1 : (Finset.univ : Finset (Finset (Fin 1))) =
    {(∅ : Finset (Fin 1)), ({0} : Finset (Fin 1))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns1

theorem univ_indices1 : (Finset.univ : Finset (Fin 1)) = {0} := by decide

#print axioms Paper6FiveExclusion.univ_indices1

theorem univ_patterns2 : (Finset.univ : Finset (Finset (Fin 2))) =
    {(∅ : Finset (Fin 2)), ({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns2

theorem univ_indices2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide

#print axioms Paper6FiveExclusion.univ_indices2

theorem univ_patterns3 : (Finset.univ : Finset (Finset (Fin 3))) =
    {(∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns3

theorem univ_indices3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

#print axioms Paper6FiveExclusion.univ_indices3

theorem univ_patterns4 : (Finset.univ : Finset (Finset (Fin 4))) =
    {(∅ : Finset (Fin 4)), ({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns4

theorem univ_indices4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

#print axioms Paper6FiveExclusion.univ_indices4

theorem univ_patterns5 : (Finset.univ : Finset (Finset (Fin 5))) =
    {(∅ : Finset (Fin 5)), ({0} : Finset (Fin 5)), ({1} : Finset (Fin 5)), ({0, 1} : Finset (Fin 5)), ({2} : Finset (Fin 5)), ({0, 2} : Finset (Fin 5)), ({1, 2} : Finset (Fin 5)), ({0, 1, 2} : Finset (Fin 5)), ({3} : Finset (Fin 5)), ({0, 3} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)), ({0, 1, 3} : Finset (Fin 5)), ({2, 3} : Finset (Fin 5)), ({0, 2, 3} : Finset (Fin 5)), ({1, 2, 3} : Finset (Fin 5)), ({0, 1, 2, 3} : Finset (Fin 5)), ({4} : Finset (Fin 5)), ({0, 4} : Finset (Fin 5)), ({1, 4} : Finset (Fin 5)), ({0, 1, 4} : Finset (Fin 5)), ({2, 4} : Finset (Fin 5)), ({0, 2, 4} : Finset (Fin 5)), ({1, 2, 4} : Finset (Fin 5)), ({0, 1, 2, 4} : Finset (Fin 5)), ({3, 4} : Finset (Fin 5)), ({0, 3, 4} : Finset (Fin 5)), ({1, 3, 4} : Finset (Fin 5)), ({0, 1, 3, 4} : Finset (Fin 5)), ({2, 3, 4} : Finset (Fin 5)), ({0, 2, 3, 4} : Finset (Fin 5)), ({1, 2, 3, 4} : Finset (Fin 5)), ({0, 1, 2, 3, 4} : Finset (Fin 5))} := by decide

#print axioms Paper6FiveExclusion.univ_patterns5

theorem univ_indices5 : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide

/-! Small inner sums are expanded separately, before any outer weight expansion.
The generic blockCount values remain opaque in these proofs. -/

#print axioms Paper6FiveExclusion.univ_indices5

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_nonempty_patterns1 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 1) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 1))).filter (fun U => U.Nonempty)), f U) =
      f ({0} : Finset (Fin 1)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 1))).filter (fun U => U.Nonempty)) =
      ([({0} : Finset (Fin 1))] : List (Finset (Fin 1))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 1))] : List (Finset (Fin 1))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

#print axioms Paper6FiveExclusion.sum_nonempty_patterns1

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_nonempty_patterns2 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 2) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => U.Nonempty)), f U) =
      f ({0} : Finset (Fin 2)) + f ({1} : Finset (Fin 2)) + f ({0, 1} : Finset (Fin 2)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => U.Nonempty)) =
      ([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_nonempty_patterns2

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_nonempty_patterns3 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 3) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => U.Nonempty)), f U) =
      f ({0} : Finset (Fin 3)) + f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => U.Nonempty)) =
      ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_nonempty_patterns3

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_nonempty_patterns4 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 4) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 4))).filter (fun U => U.Nonempty)), f U) =
      f ({0} : Finset (Fin 4)) + f ({1} : Finset (Fin 4)) + f ({0, 1} : Finset (Fin 4)) + f ({2} : Finset (Fin 4)) + f ({0, 2} : Finset (Fin 4)) + f ({1, 2} : Finset (Fin 4)) + f ({0, 1, 2} : Finset (Fin 4)) + f ({3} : Finset (Fin 4)) + f ({0, 3} : Finset (Fin 4)) + f ({1, 3} : Finset (Fin 4)) + f ({0, 1, 3} : Finset (Fin 4)) + f ({2, 3} : Finset (Fin 4)) + f ({0, 2, 3} : Finset (Fin 4)) + f ({1, 2, 3} : Finset (Fin 4)) + f ({0, 1, 2, 3} : Finset (Fin 4)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 4))).filter (fun U => U.Nonempty)) =
      ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))] : List (Finset (Fin 4))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_nonempty_patterns4

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_nonempty_patterns5 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 5) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 5))).filter (fun U => U.Nonempty)), f U) =
      f ({0} : Finset (Fin 5)) + f ({1} : Finset (Fin 5)) + f ({0, 1} : Finset (Fin 5)) + f ({2} : Finset (Fin 5)) + f ({0, 2} : Finset (Fin 5)) + f ({1, 2} : Finset (Fin 5)) + f ({0, 1, 2} : Finset (Fin 5)) + f ({3} : Finset (Fin 5)) + f ({0, 3} : Finset (Fin 5)) + f ({1, 3} : Finset (Fin 5)) + f ({0, 1, 3} : Finset (Fin 5)) + f ({2, 3} : Finset (Fin 5)) + f ({0, 2, 3} : Finset (Fin 5)) + f ({1, 2, 3} : Finset (Fin 5)) + f ({0, 1, 2, 3} : Finset (Fin 5)) + f ({4} : Finset (Fin 5)) + f ({0, 4} : Finset (Fin 5)) + f ({1, 4} : Finset (Fin 5)) + f ({0, 1, 4} : Finset (Fin 5)) + f ({2, 4} : Finset (Fin 5)) + f ({0, 2, 4} : Finset (Fin 5)) + f ({1, 2, 4} : Finset (Fin 5)) + f ({0, 1, 2, 4} : Finset (Fin 5)) + f ({3, 4} : Finset (Fin 5)) + f ({0, 3, 4} : Finset (Fin 5)) + f ({1, 3, 4} : Finset (Fin 5)) + f ({0, 1, 3, 4} : Finset (Fin 5)) + f ({2, 3, 4} : Finset (Fin 5)) + f ({0, 2, 3, 4} : Finset (Fin 5)) + f ({1, 2, 3, 4} : Finset (Fin 5)) + f ({0, 1, 2, 3, 4} : Finset (Fin 5)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 5))).filter (fun U => U.Nonempty)) =
      ([({0} : Finset (Fin 5)), ({1} : Finset (Fin 5)), ({0, 1} : Finset (Fin 5)), ({2} : Finset (Fin 5)), ({0, 2} : Finset (Fin 5)), ({1, 2} : Finset (Fin 5)), ({0, 1, 2} : Finset (Fin 5)), ({3} : Finset (Fin 5)), ({0, 3} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)), ({0, 1, 3} : Finset (Fin 5)), ({2, 3} : Finset (Fin 5)), ({0, 2, 3} : Finset (Fin 5)), ({1, 2, 3} : Finset (Fin 5)), ({0, 1, 2, 3} : Finset (Fin 5)), ({4} : Finset (Fin 5)), ({0, 4} : Finset (Fin 5)), ({1, 4} : Finset (Fin 5)), ({0, 1, 4} : Finset (Fin 5)), ({2, 4} : Finset (Fin 5)), ({0, 2, 4} : Finset (Fin 5)), ({1, 2, 4} : Finset (Fin 5)), ({0, 1, 2, 4} : Finset (Fin 5)), ({3, 4} : Finset (Fin 5)), ({0, 3, 4} : Finset (Fin 5)), ({1, 3, 4} : Finset (Fin 5)), ({0, 1, 3, 4} : Finset (Fin 5)), ({2, 3, 4} : Finset (Fin 5)), ({0, 2, 3, 4} : Finset (Fin 5)), ({1, 2, 3, 4} : Finset (Fin 5)), ({0, 1, 2, 3, 4} : Finset (Fin 5))] : List (Finset (Fin 5))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 5)), ({1} : Finset (Fin 5)), ({0, 1} : Finset (Fin 5)), ({2} : Finset (Fin 5)), ({0, 2} : Finset (Fin 5)), ({1, 2} : Finset (Fin 5)), ({0, 1, 2} : Finset (Fin 5)), ({3} : Finset (Fin 5)), ({0, 3} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)), ({0, 1, 3} : Finset (Fin 5)), ({2, 3} : Finset (Fin 5)), ({0, 2, 3} : Finset (Fin 5)), ({1, 2, 3} : Finset (Fin 5)), ({0, 1, 2, 3} : Finset (Fin 5)), ({4} : Finset (Fin 5)), ({0, 4} : Finset (Fin 5)), ({1, 4} : Finset (Fin 5)), ({0, 1, 4} : Finset (Fin 5)), ({2, 4} : Finset (Fin 5)), ({0, 2, 4} : Finset (Fin 5)), ({1, 2, 4} : Finset (Fin 5)), ({0, 1, 2, 4} : Finset (Fin 5)), ({3, 4} : Finset (Fin 5)), ({0, 3, 4} : Finset (Fin 5)), ({1, 3, 4} : Finset (Fin 5)), ({0, 1, 3, 4} : Finset (Fin 5)), ({2, 3, 4} : Finset (Fin 5)), ({0, 2, 3, 4} : Finset (Fin 5)), ({1, 2, 3, 4} : Finset (Fin 5)), ({0, 1, 2, 3, 4} : Finset (Fin 5))] : List (Finset (Fin 5))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_nonempty_patterns5

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns1_0 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 1) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 1))).filter (fun U => (0 : Fin 1) ∈ U)), f U) =
      f ({0} : Finset (Fin 1)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 1))).filter (fun U => (0 : Fin 1) ∈ U)) =
      ([({0} : Finset (Fin 1))] : List (Finset (Fin 1))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 1))] : List (Finset (Fin 1))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

#print axioms Paper6FiveExclusion.sum_column_patterns1_0

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns2_0 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 2) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => (0 : Fin 2) ∈ U)), f U) =
      f ({0} : Finset (Fin 2)) + f ({0, 1} : Finset (Fin 2)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => (0 : Fin 2) ∈ U)) =
      ([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

#print axioms Paper6FiveExclusion.sum_column_patterns2_0

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns2_1 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 2) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => (1 : Fin 2) ∈ U)), f U) =
      f ({1} : Finset (Fin 2)) + f ({0, 1} : Finset (Fin 2)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 2))).filter (fun U => (1 : Fin 2) ∈ U)) =
      ([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

#print axioms Paper6FiveExclusion.sum_column_patterns2_1

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns3_0 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 3) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (0 : Fin 3) ∈ U)), f U) =
      f ({0} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (0 : Fin 3) ∈ U)) =
      ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_column_patterns3_0

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns3_1 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 3) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (1 : Fin 3) ∈ U)), f U) =
      f ({1} : Finset (Fin 3)) + f ({0, 1} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (1 : Fin 3) ∈ U)) =
      ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_column_patterns3_1

/-- A finite index identity with an opaque summand and explicit list Nodup proof. -/
theorem sum_column_patterns3_2 {α : Type*} [AddCommMonoid α]
    (f : Finset (Fin 3) → α) :
    (∑ U ∈ ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (2 : Fin 3) ∈ U)), f U) =
      f ({2} : Finset (Fin 3)) + f ({0, 2} : Finset (Fin 3)) + f ({1, 2} : Finset (Fin 3)) + f ({0, 1, 2} : Finset (Fin 3)) := by
  have hdomain : ((Finset.univ : Finset (Finset (Fin 3))).filter (fun U => (2 : Fin 3) ∈ U)) =
      ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  rw [hdomain, List.sum_toFinset f (by decide : ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

#print axioms Paper6FiveExclusion.sum_column_patterns3_2

theorem blockUnion_expand_0_0 (H : Finset (Fin 14))
    (R : Fin 0 → Finset (Fin 14)) :
    blockUnion H R (∅ : Finset (Fin 0)) =
      0 := by
  have hp : meetingPatterns (∅ : Finset (Fin 0)) =
      (∅ : Finset (Finset (Fin 0))) := by decide
  rw [blockUnion, hp]; norm_num

#print axioms Paper6FiveExclusion.blockUnion_expand_0_0

theorem blockUnion_expand_1_0 (H : Finset (Fin 14))
    (R : Fin 1 → Finset (Fin 14)) :
    blockUnion H R (∅ : Finset (Fin 1)) =
      0 := by
  have hp : meetingPatterns (∅ : Finset (Fin 1)) =
      (∅ : Finset (Finset (Fin 1))) := by decide
  rw [blockUnion, hp]; norm_num

#print axioms Paper6FiveExclusion.blockUnion_expand_1_0

theorem blockUnion_expand_1_1 (H : Finset (Fin 14))
    (R : Fin 1 → Finset (Fin 14)) :
    blockUnion H R ({0} : Finset (Fin 1)) =
      blockCount H R ({0} : Finset (Fin 1)) := by
  have hp : meetingPatterns ({0} : Finset (Fin 1)) =
      ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))) := by decide
  rw [blockUnion, hp]; norm_num

#print axioms Paper6FiveExclusion.blockUnion_expand_1_1

theorem blockUnion_expand_2_0 (H : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) :
    blockUnion H R (∅ : Finset (Fin 2)) =
      0 := by
  have hp : meetingPatterns (∅ : Finset (Fin 2)) =
      (∅ : Finset (Finset (Fin 2))) := by decide
  rw [blockUnion, hp]; norm_num

#print axioms Paper6FiveExclusion.blockUnion_expand_2_0

theorem blockUnion_expand_2_1 (H : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) :
    blockUnion H R ({0} : Finset (Fin 2)) =
      blockCount H R ({0} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
  have hp : meetingPatterns ({0} : Finset (Fin 2)) =
      ({({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) := by decide
  have hl : ({({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) =
      ([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  calc
    blockUnion H R ({0} : Finset (Fin 2)) =
        ([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]

#print axioms Paper6FiveExclusion.blockUnion_expand_2_1

theorem blockUnion_expand_2_2 (H : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) :
    blockUnion H R ({1} : Finset (Fin 2)) =
      blockCount H R ({1} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
  have hp : meetingPatterns ({1} : Finset (Fin 2)) =
      ({({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) := by decide
  have hl : ({({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) =
      ([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  calc
    blockUnion H R ({1} : Finset (Fin 2)) =
        ([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)
    _ = blockCount H R ({1} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]

#print axioms Paper6FiveExclusion.blockUnion_expand_2_2

theorem blockUnion_expand_2_3 (H : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) :
    blockUnion H R ({0, 1} : Finset (Fin 2)) =
      blockCount H R ({0} : Finset (Fin 2)) + blockCount H R ({1} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
  have hp : meetingPatterns ({0, 1} : Finset (Fin 2)) =
      ({({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) := by decide
  have hl : ({({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))} : Finset (Finset (Fin 2))) =
      ([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset := by decide
  calc
    blockUnion H R ({0, 1} : Finset (Fin 2)) =
        ([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))] : List (Finset (Fin 2))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 2)) + blockCount H R ({1} : Finset (Fin 2)) + blockCount H R ({0, 1} : Finset (Fin 2)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_2_3

theorem blockUnion_expand_3_0 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R (∅ : Finset (Fin 3)) =
      0 := by
  have hp : meetingPatterns (∅ : Finset (Fin 3)) =
      (∅ : Finset (Finset (Fin 3))) := by decide
  rw [blockUnion, hp]; norm_num

#print axioms Paper6FiveExclusion.blockUnion_expand_3_0

theorem blockUnion_expand_3_1 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({0} : Finset (Fin 3)) =
      blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({0} : Finset (Fin 3)) =
      ({({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({0} : Finset (Fin 3)) =
        ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_1

theorem blockUnion_expand_3_2 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({1} : Finset (Fin 3)) =
      blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({1} : Finset (Fin 3)) =
      ({({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({1} : Finset (Fin 3)) =
        ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_2

theorem blockUnion_expand_3_3 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({0, 1} : Finset (Fin 3)) =
      blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({0, 1} : Finset (Fin 3)) =
      ({({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({0, 1} : Finset (Fin 3)) =
        ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_3

theorem blockUnion_expand_3_4 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({2} : Finset (Fin 3)) =
      blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({2} : Finset (Fin 3)) =
      ({({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({2} : Finset (Fin 3)) =
        ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_4

theorem blockUnion_expand_3_5 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({0, 2} : Finset (Fin 3)) =
      blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({0, 2} : Finset (Fin 3)) =
      ({({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({0, 2} : Finset (Fin 3)) =
        ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_5

theorem blockUnion_expand_3_6 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({1, 2} : Finset (Fin 3)) =
      blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({1, 2} : Finset (Fin 3)) =
      ({({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({1, 2} : Finset (Fin 3)) =
        ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_6

theorem blockUnion_expand_3_7 (H : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) :
    blockUnion H R ({0, 1, 2} : Finset (Fin 3)) =
      blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
  have hp : meetingPatterns ({0, 1, 2} : Finset (Fin 3)) =
      ({({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by decide
  have hl : ({({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) =
      ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset := by decide
  calc
    blockUnion H R ({0, 1, 2} : Finset (Fin 3)) =
        ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).toFinset.sum (fun U => blockCount H R U) := by
      rw [blockUnion, hp, hl]
    _ = (([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).map (fun U => blockCount H R U)).sum :=
      List.sum_toFinset (fun U => blockCount H R U) (by decide : ([({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))] : List (Finset (Fin 3))).Nodup)
    _ = blockCount H R ({0} : Finset (Fin 3)) + blockCount H R ({1} : Finset (Fin 3)) + blockCount H R ({0, 1} : Finset (Fin 3)) + blockCount H R ({2} : Finset (Fin 3)) + blockCount H R ({0, 2} : Finset (Fin 3)) + blockCount H R ({1, 2} : Finset (Fin 3)) + blockCount H R ({0, 1, 2} : Finset (Fin 3)) := by
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, add_assoc]

#print axioms Paper6FiveExclusion.blockUnion_expand_3_7

set_option maxHeartbeats 1000000 in
theorem actual_pair_weight0 (A B : Finset (Fin 14))
    (R : Fin 0 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (hammingNorm (pairFunction A B R) : ℤ) = pairWeight0  := by
  have h := pair_weight_formula A B R hA hB hd hu
  rw [sum_nonempty_patterns2] at h
  norm_num [selectedCard, tailSelection, univ_indices0,
    Finset.filter_insert, Finset.filter_singleton, blockUnion_expand_0_0] at h
  unfold pairWeight0
  simp only [add_assoc] at h ⊢
  convert h using 1; ring

#print axioms Paper6FiveExclusion.actual_pair_weight0

theorem actual_pair_bounds1 (A B : Finset (Fin 14))
    (R : Fin 1 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ)
    (hR : ∀ i, (R i).card ≤ 7) :
    pairBounds1 (blockCount A R ({0} : Finset (Fin 1))) (blockCount B R ({0} : Finset (Fin 1))) := by
  have htotalA := block_total_le A R
  have htotalB := block_total_le B R
  rw [hA] at htotalA
  rw [hB] at htotalB
  rw [sum_nonempty_patterns1] at htotalA htotalB
  have ha0 := block_column_card A R (0 : Fin 1)
  have hb0 := block_column_card B R (0 : Fin 1)
  rw [sum_column_patterns1_0] at ha0 hb0
  have hs0 := split_card A B (R 0) hd hu
  have hr0 := hR (0 : Fin 1)
  unfold pairBounds1
  omega

#print axioms Paper6FiveExclusion.actual_pair_bounds1

set_option maxHeartbeats 1000000 in
theorem actual_pair_weight1 (A B : Finset (Fin 14))
    (R : Fin 1 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (hammingNorm (pairFunction A B R) : ℤ) = pairWeight1 (blockCount A R ({0} : Finset (Fin 1))) (blockCount B R ({0} : Finset (Fin 1))) := by
  have h := pair_weight_formula A B R hA hB hd hu
  rw [sum_nonempty_patterns3] at h
  norm_num [selectedCard, tailSelection, univ_indices1,
    Finset.filter_insert, Finset.filter_singleton, blockUnion_expand_1_0, blockUnion_expand_1_1] at h
  unfold pairWeight1
  simp only [add_assoc] at h ⊢
  convert h using 1; ring

#print axioms Paper6FiveExclusion.actual_pair_weight1

theorem actual_pair_bounds2 (A B : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ)
    (hR : ∀ i, (R i).card ≤ 7) :
    pairBounds2 (blockCount A R ({0} : Finset (Fin 2))) (blockCount A R ({1} : Finset (Fin 2))) (blockCount A R ({0, 1} : Finset (Fin 2))) (blockCount B R ({0} : Finset (Fin 2))) (blockCount B R ({1} : Finset (Fin 2))) (blockCount B R ({0, 1} : Finset (Fin 2))) := by
  have htotalA := block_total_le A R
  have htotalB := block_total_le B R
  rw [hA] at htotalA
  rw [hB] at htotalB
  rw [sum_nonempty_patterns2] at htotalA htotalB
  have ha0 := block_column_card A R (0 : Fin 2)
  have hb0 := block_column_card B R (0 : Fin 2)
  rw [sum_column_patterns2_0] at ha0 hb0
  have hs0 := split_card A B (R 0) hd hu
  have hr0 := hR (0 : Fin 2)
  have ha1 := block_column_card A R (1 : Fin 2)
  have hb1 := block_column_card B R (1 : Fin 2)
  rw [sum_column_patterns2_1] at ha1 hb1
  have hs1 := split_card A B (R 1) hd hu
  have hr1 := hR (1 : Fin 2)
  unfold pairBounds2
  omega

#print axioms Paper6FiveExclusion.actual_pair_bounds2

set_option maxHeartbeats 1000000 in
theorem actual_pair_weight2 (A B : Finset (Fin 14))
    (R : Fin 2 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (hammingNorm (pairFunction A B R) : ℤ) = pairWeight2 (blockCount A R ({0} : Finset (Fin 2))) (blockCount A R ({1} : Finset (Fin 2))) (blockCount A R ({0, 1} : Finset (Fin 2))) (blockCount B R ({0} : Finset (Fin 2))) (blockCount B R ({1} : Finset (Fin 2))) (blockCount B R ({0, 1} : Finset (Fin 2))) := by
  have h := pair_weight_formula A B R hA hB hd hu
  rw [sum_nonempty_patterns4] at h
  norm_num [selectedCard, tailSelection, univ_indices2,
    Finset.filter_insert, Finset.filter_singleton, blockUnion_expand_2_0, blockUnion_expand_2_1, blockUnion_expand_2_2, blockUnion_expand_2_3] at h
  unfold pairWeight2
  simp only [add_assoc] at h ⊢
  convert h using 1; ring

#print axioms Paper6FiveExclusion.actual_pair_weight2

theorem actual_pair_bounds3 (A B : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ)
    (hR : ∀ i, (R i).card ≤ 7) :
    pairBounds3 (blockCount A R ({0} : Finset (Fin 3))) (blockCount A R ({1} : Finset (Fin 3))) (blockCount A R ({0, 1} : Finset (Fin 3))) (blockCount A R ({2} : Finset (Fin 3))) (blockCount A R ({0, 2} : Finset (Fin 3))) (blockCount A R ({1, 2} : Finset (Fin 3))) (blockCount A R ({0, 1, 2} : Finset (Fin 3))) (blockCount B R ({0} : Finset (Fin 3))) (blockCount B R ({1} : Finset (Fin 3))) (blockCount B R ({0, 1} : Finset (Fin 3))) (blockCount B R ({2} : Finset (Fin 3))) (blockCount B R ({0, 2} : Finset (Fin 3))) (blockCount B R ({1, 2} : Finset (Fin 3))) (blockCount B R ({0, 1, 2} : Finset (Fin 3))) := by
  have htotalA := block_total_le A R
  have htotalB := block_total_le B R
  rw [hA] at htotalA
  rw [hB] at htotalB
  rw [sum_nonempty_patterns3] at htotalA htotalB
  have ha0 := block_column_card A R (0 : Fin 3)
  have hb0 := block_column_card B R (0 : Fin 3)
  rw [sum_column_patterns3_0] at ha0 hb0
  have hs0 := split_card A B (R 0) hd hu
  have hr0 := hR (0 : Fin 3)
  have ha1 := block_column_card A R (1 : Fin 3)
  have hb1 := block_column_card B R (1 : Fin 3)
  rw [sum_column_patterns3_1] at ha1 hb1
  have hs1 := split_card A B (R 1) hd hu
  have hr1 := hR (1 : Fin 3)
  have ha2 := block_column_card A R (2 : Fin 3)
  have hb2 := block_column_card B R (2 : Fin 3)
  rw [sum_column_patterns3_2] at ha2 hb2
  have hs2 := split_card A B (R 2) hd hu
  have hr2 := hR (2 : Fin 3)
  unfold pairBounds3
  omega

#print axioms Paper6FiveExclusion.actual_pair_bounds3

set_option maxHeartbeats 1000000 in
theorem actual_pair_weight3 (A B : Finset (Fin 14))
    (R : Fin 3 → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (hammingNorm (pairFunction A B R) : ℤ) = pairWeight3 (blockCount A R ({0} : Finset (Fin 3))) (blockCount A R ({1} : Finset (Fin 3))) (blockCount A R ({0, 1} : Finset (Fin 3))) (blockCount A R ({2} : Finset (Fin 3))) (blockCount A R ({0, 2} : Finset (Fin 3))) (blockCount A R ({1, 2} : Finset (Fin 3))) (blockCount A R ({0, 1, 2} : Finset (Fin 3))) (blockCount B R ({0} : Finset (Fin 3))) (blockCount B R ({1} : Finset (Fin 3))) (blockCount B R ({0, 1} : Finset (Fin 3))) (blockCount B R ({2} : Finset (Fin 3))) (blockCount B R ({0, 2} : Finset (Fin 3))) (blockCount B R ({1, 2} : Finset (Fin 3))) (blockCount B R ({0, 1, 2} : Finset (Fin 3))) := by
  have h := pair_weight_formula A B R hA hB hd hu
  rw [sum_nonempty_patterns5] at h
  norm_num [selectedCard, tailSelection, univ_indices3,
    Finset.filter_insert, Finset.filter_singleton, blockUnion_expand_3_0, blockUnion_expand_3_1, blockUnion_expand_3_2, blockUnion_expand_3_3, blockUnion_expand_3_4, blockUnion_expand_3_5, blockUnion_expand_3_6, blockUnion_expand_3_7] at h
  unfold pairWeight3
  simp only [add_assoc] at h ⊢
  convert h using 1; ring

#print axioms Paper6FiveExclusion.actual_pair_weight3

end Paper6FiveExclusion
