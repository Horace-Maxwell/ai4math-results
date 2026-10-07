import Research.Backfill.Paper5.Supplement.AlgebraStatementV2

set_option autoImplicit false

universe u v w

namespace CodexPaper5.GenericAlgebra

open BackfillPaper5

/-- The two sandwich entries are the only zero cases; otherwise base associativity applies. -/
theorem rees0Mul_assoc {G : Type u} {I : Type v} {L : Type w} [Semigroup G]
    (P : L → I → Option G) (x y z : Challenge.Rees0 G I L) :
    Challenge.rees0Mul P (Challenge.rees0Mul P x y) z =
      Challenge.rees0Mul P x (Challenge.rees0Mul P y z) := by
  rcases x with _ | ⟨i, a, l⟩
  · rfl
  rcases y with _ | ⟨j, b, m⟩
  · rfl
  rcases z with _ | ⟨k, c, t⟩
  · cases hP : P l j <;>
      simp only [Challenge.rees0Mul, hP, Option.map_none, Option.map_some]
  cases hP : P l j <;> cases hQ : P m k <;>
    simp only [Challenge.rees0Mul, hP, hQ, Option.map_none, Option.map_some, mul_assoc]

/-- Graph cells of a complete mapping give all three bijections. Conversely the bijective
row projection supplies the unique cell from which the mapping is recovered. -/
theorem cayley_transversal_iff (S : Type u) (op : S → S → S) :
    (∃ a : S → S, Challenge.IsCompleteMapping op a) ↔
      ∃ T : Set (S × S),
        Function.Bijective (fun x : T => x.val.1) ∧
        Function.Bijective (fun x : T => x.val.2) ∧
        Function.Bijective (fun x : T => op x.val.1 x.val.2) := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    let T : Set (S × S) := {p | p.2 = a p.1}
    let e : S ≃ T :=
      { toFun := fun x => ⟨(x, a x), rfl⟩
        invFun := fun x => x.val.1
        left_inv := fun _ => rfl
        right_inv := by
          intro x
          apply Subtype.ext
          exact Prod.ext rfl x.property.symm }
    refine ⟨T, ?_, ?_, ?_⟩
    · exact e.symm.bijective
    · have hc : (fun x : T => x.val.2) = a ∘ e.symm := by
        funext x
        exact x.property
      rw [hc]
      exact ha.1.comp e.symm.bijective
    · have hv : (fun x : T => op x.val.1 x.val.2) =
          (fun x : S => op x (a x)) ∘ e.symm := by
        funext x
        change op x.val.1 x.val.2 = op x.val.1 (a x.val.1)
        rw [x.property]
      rw [hv]
      exact ha.2.comp e.symm.bijective
  · rintro ⟨T, hrow, hcol, hvalue⟩
    let e : T ≃ S := Equiv.ofBijective (fun x : T => x.val.1) hrow
    let a : S → S := fun x => (e.symm x).val.2
    refine ⟨a, ?_, ?_⟩
    · exact hcol.comp e.symm.bijective
    · have hr : ∀ x : S, (e.symm x).val.1 = x := by
        intro x
        exact e.apply_symm_apply x
      have hv : (fun x : S => op x (a x)) =
          (fun t : T => op t.val.1 t.val.2) ∘ e.symm := by
        funext x
        change op x ((e.symm x).val.2) =
          op ((e.symm x).val.1) ((e.symm x).val.2)
        rw [hr x]
      rw [hv]
      exact hvalue.comp e.symm.bijective

theorem check_ReesAssociativity : CodexPaper5.AlgebraStatement.ReesAssociativity := by
  intro G I L M P
  let _ : Semigroup G := M
  exact rees0Mul_assoc P

theorem check_CayleyTransversalIff : CodexPaper5.AlgebraStatement.CayleyTransversalIff := by
  intro S op
  exact cayley_transversal_iff S op

end CodexPaper5.GenericAlgebra

#print axioms CodexPaper5.GenericAlgebra.rees0Mul_assoc
#print axioms CodexPaper5.GenericAlgebra.cayley_transversal_iff
#print axioms CodexPaper5.GenericAlgebra.check_ReesAssociativity
#print axioms CodexPaper5.GenericAlgebra.check_CayleyTransversalIff
