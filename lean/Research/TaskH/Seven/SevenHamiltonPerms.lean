import Research.TaskH.FiniteBudget

/-!
Analytic finite-permutation counts for rooted Hamilton traversals.
No permutation table or native enumeration is supplied or trusted.
The graph-to-traversal transport is a separate obligation.
-/

set_option autoImplicit false

namespace TaskH.Seven

open scoped Classical

noncomputable def hamiltonEvaluationFiber (i a : Fin 6) :
    Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.filter (fun π => π i = a)

theorem hamiltonEvaluationFiber_card_eq (i a b : Fin 6) :
    (hamiltonEvaluationFiber i a).card = (hamiltonEvaluationFiber i b).card := by
  classical
  refine Finset.card_bij (fun π _ => Equiv.swap a b * π) ?_ ?_ ?_
  · intro π hπ
    have hv : π i = a := (Finset.mem_filter.mp hπ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Equiv.Perm.mul_apply, hv, Equiv.swap_apply_left]
  · intro π _ ρ _ he
    exact mul_left_cancel he
  · intro ρ hρ
    have hv : ρ i = b := (Finset.mem_filter.mp hρ).2
    refine ⟨Equiv.swap a b * ρ, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Equiv.Perm.mul_apply, hv, Equiv.swap_apply_right]
    · apply Equiv.ext
      intro z
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_self]

theorem hamiltonEvaluationFiber_card (i a : Fin 6) :
    (hamiltonEvaluationFiber i a).card = 120 := by
  classical
  have hsum : (∑ b : Fin 6, (hamiltonEvaluationFiber i b).card) = 720 := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Equiv.Perm (Fin 6)))
      (Finset.univ : Finset (Fin 6)) (fun π => π i)
    simpa [hamiltonEvaluationFiber, Fintype.card_perm, Nat.factorial] using h
  have heq : (∑ b : Fin 6, (hamiltonEvaluationFiber i b).card) =
      6 * (hamiltonEvaluationFiber i a).card := by
    calc
      _ = ∑ _b : Fin 6, (hamiltonEvaluationFiber i a).card := by
        apply Finset.sum_congr rfl
        intro b _
        exact hamiltonEvaluationFiber_card_eq i b a
      _ = _ := by simp
  omega

noncomputable def hamiltonAvoidingEnds (i j a : Fin 6) :
    Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.filter (fun π => π i ≠ a ∧ π j ≠ a)

/-- Missing adjacency to the root forbids a fixed remaining point in
either of two distinct endpoint positions: exactly480 orders remain. -/
theorem hamiltonAvoidingEnds_card (i j a : Fin 6) (hij : i ≠ j) :
    (hamiltonAvoidingEnds i j a).card = 480 := by
  classical
  have hdis : Disjoint (hamiltonEvaluationFiber i a) (hamiltonEvaluationFiber j a) := by
    apply Finset.disjoint_left.mpr
    intro π hi hj
    have hi' : π i = a := (Finset.mem_filter.mp hi).2
    have hj' : π j = a := (Finset.mem_filter.mp hj).2
    exact hij (π.injective (hi'.trans hj'.symm))
  have hbad : (hamiltonEvaluationFiber i a ∪ hamiltonEvaluationFiber j a).card = 240 := by
    rw [Finset.card_union_of_disjoint hdis, hamiltonEvaluationFiber_card,
      hamiltonEvaluationFiber_card]
  have he : hamiltonAvoidingEnds i j a = Finset.univ \
      (hamiltonEvaluationFiber i a ∪ hamiltonEvaluationFiber j a) := by
    ext π
    simp [hamiltonAvoidingEnds, hamiltonEvaluationFiber]
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), hbad]
  norm_num [Fintype.card_perm]

/-- A finite relation with at least two genuine oriented parameters per
circle and at most one actual circle per parameter has at most240 rows.
Actual graph transport must establish these two fiber statements. -/
theorem hamilton_two_directions_bound {A : Type*} (C : Finset A)
    (P : Finset (Equiv.Perm (Fin 6))) (R : A → Equiv.Perm (Fin 6) → Prop)
    (hP : P.card ≤ 480)
    (hrow : ∀ s ∈ C, 2 ≤ (P.filter (R s)).card)
    (hcol : ∀ π ∈ P, (C.filter (fun s => R s π)).card ≤ 1) : C.card ≤ 240 := by
  classical
  have hdouble := FiniteBudget.relation_double_count C P R
  have hlo : C.card * 2 ≤ ∑ s ∈ C, (P.filter (R s)).card := by
    calc
      C.card * 2 = ∑ _s ∈ C, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ π ∈ P, (C.filter (fun s => R s π)).card) ≤ P.card := by
    calc
      _ ≤ ∑ _π ∈ P, 1 := Finset.sum_le_sum hcol
      _ = _ := by simp
  omega

end TaskH.Seven

#print axioms TaskH.Seven.hamiltonEvaluationFiber
#print axioms TaskH.Seven.hamiltonEvaluationFiber_card_eq
#print axioms TaskH.Seven.hamiltonEvaluationFiber_card
#print axioms TaskH.Seven.hamiltonAvoidingEnds
#print axioms TaskH.Seven.hamiltonAvoidingEnds_card
#print axioms TaskH.Seven.hamilton_two_directions_bound
