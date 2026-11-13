import Research.TaskG.Automorphism
import Research.TaskG.Forms
import Research.TaskG.Simplicity
import Research.TaskG.Axes

set_option autoImplicit false
namespace TaskG.Proof
open AxialMSZ.Challenge TaskG.Challenge

theorem beta_nondegenerate (u : V) (hu : ∀ v : V, β u v = 0) : u = 0 := by
  have h0 := hu (e 0)
  have h1 := hu (e 1)
  have h2 := hu (e 2)
  have h3 := hu (e 3)
  norm_num [e, Pi.single_apply] at h0 h1 h2 h3
  ext i; fin_cases i <;> simp_all

/-- Multiplying the form by -1 really changes it. -/
theorem form_not_preserved : ∃ u v : V, β (g u) (g v) ≠ β u v := by
  refine ⟨e 0, e 0, ?_⟩
  rw [g_scales]
  have hb : β (e 0) (e 0) = 1 := by norm_num [e, Pi.single_apply]
  rw [hb, mul_one]
  exact scale_nontrivial

/-- The actual tight fusion table is graded by the even and odd parts of C2. -/
theorem fusion_grading :
    (∀ l m x : K, l ∈ ({1,5,7} : Set K) → m ∈ ({1,5,7} : Set K) →
      x ∈ F.star l m → x ∈ ({1,5,7} : Set K)) ∧
    (∀ l m x : K, l ∈ ({1,5,7} : Set K) → m = 10 → x ∈ F.star l m → x = 10) ∧
    (∀ x : K, x ∈ F.star 10 10 → x ∈ ({1,5,7} : Set K)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l m x hl hm hx
    rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
    all_goals norm_num [F] at hx ⊢
    all_goals aesop
  · intro l m x hl hm hx
    subst m
    rcases hl with rfl | rfl | rfl
    all_goals norm_num [F] at hx ⊢
    all_goals aesop
  · intro x hx
    have h10 : (10 : K) ≠ 1 := by decide +kernel
    simpa [F, h10] using hx

theorem witness_conditions : WitnessConditions F μ X β g (-1 : K) := by
  exact ⟨fusion_finite_symmetric, X_finite, X_nonempty, primitive_axial,
    directlyIndecomposable, beta_nonzero, beta_symmetric, beta_frobenius,
    g_mul, scale_nonzero, scale_nontrivial, g_scales, Or.inl g_involutive⟩

theorem example_over_eleven : ExampleOver K := by
  exact ⟨4,T,F,X,β,g,-1,by decide,by decide,witness_conditions⟩

theorem strong_example_over_eleven : StrongExampleOver K := by
  exact ⟨4,T,F,X,β,g,-1,by decide,by decide,witness_conditions,beta_form_space,hasNoIdentity⟩

theorem answer : ShpectorovAnswer :=
  Or.inr (Or.inr (Or.inr example_over_eleven))

theorem strong_answer : StrongShpectorovAnswer :=
  Or.inr (Or.inr (Or.inr strong_example_over_eleven))

#print axioms TaskG.Proof.beta_nondegenerate
#print axioms TaskG.Proof.form_not_preserved
#print axioms TaskG.Proof.fusion_grading
#print axioms TaskG.Proof.witness_conditions
#print axioms TaskG.Proof.answer
#print axioms TaskG.Proof.strong_answer
end TaskG.Proof
