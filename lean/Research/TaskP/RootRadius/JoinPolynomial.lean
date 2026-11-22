import Research.TaskP.RootRadius.JoinDecomposition
import Research.TaskP.RootRadius.PetalEvaluation

open Polynomial
namespace TaskP.GraphRootRadius.Proof
open Challenge

variable {V : Type*} [Fintype V]

noncomputable def dWeight {W : Type*} (G : SimpleGraph W) (z : ℂ) (S : Finset W) : ℂ := by
  classical
  exact if Dominates G S then z^S.card else 0

theorem eval_eq_weights (B : SimpleGraph V) (z : ℂ) :
    (dominationPolynomial B).eval z = ∑ S, dWeight B z S := by
  classical
  rw [dominationPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : Dominates B S <;> simp [dWeight, h]

theorem sum_all_weights (V : Type*) [Fintype V] (z : ℂ) :
    ∑ S : Finset V, z^S.card = (z+1)^(Fintype.card V) := by
  simpa using Fintype.sum_pow_mul_eq_add_pow V z 1

theorem eval_join {a m : ℕ} [Nonempty V] (hm : 0 < m) (B : SimpleGraph V) (z : ℂ) :
    (dominationPolynomial (petalJoin a m B)).eval z =
      ((z+1)^a-1) * (z+1)^(Fintype.card V*m) + ((dominationPolynomial B).eval z)^m := by
  classical
  let A := (z+1)^(Fintype.card V*m)
  let D := ((dominationPolynomial B).eval z)^m
  have hA : ∑ F : Fin m → Finset V, z^(bundle F).card = A := by
    change _ = (z+1)^(Fintype.card V*m)
    rw [pow_mul, ← sum_all_weights, Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro F _
    rw [card_bundle, Finset.prod_pow_eq_pow_sum]
  have hD : (∑ F : Fin m → Finset V, if ∀ i, Dominates B (F i) then z^(bundle F).card else 0) = D := by
    change _ = ((dominationPolynomial B).eval z)^m
    rw [eval_eq_weights, Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro F _
    simp only [dWeight, Fintype.prod_ite_zero, Finset.prod_pow_eq_pow_sum, card_bundle]
  let J := petalJoin a m B
  have inner (S : Finset (Fin a)) :
      ∑ F : Fin m → Finset V, dWeight J z (S.disjSum (bundle F)) =
        z^S.card * A + (if S = ∅ then D-A else 0) := by
    by_cases he : S = ∅
    · subst S
      simp only [Finset.card_empty, pow_zero, one_mul, ite_true]
      rw [add_sub_cancel]
      convert hD using 1
      apply Finset.sum_congr rfl
      intro F _
      simp only [dWeight, J, dominates_join_iff hm, Finset.card_disjSum]
      simp
    · have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      simp only [he, ite_false, add_zero, ← hA, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      simp [dWeight, J, dominates_join_iff hm, hS, Finset.card_disjSum, pow_add]
  rw [eval_eq_weights]
  change (∑ S, dWeight J z S) = _
  rw [← Finset.sumEquiv.toEquiv.symm.sum_comp (dWeight J z), Fintype.sum_prod_type]
  change (∑ S : Finset (Fin a), ∑ T : Finset (Fin m × V), dWeight J z (S.disjSum T)) = _
  have hr (S : Finset (Fin a)) : (∑ T : Finset (Fin m × V), dWeight J z (S.disjSum T)) =
      z ^ S.card * A + (if S = ∅ then D-A else 0) := by
    rw [← familyEquiv.sum_comp (fun T : Finset (Fin m × V) => dWeight J z (S.disjSum T))]
    exact inner S
  simp_rw [hr]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_all_weights]
  simp only [Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (z+1)^a*A + (D-A) = ((z+1)^a-1)*A + D
  ring

theorem root_equation {a m : ℕ} [Nonempty V] (hm : 0 < m) (B : SimpleGraph V)
    {y : ℂ} (hy : y ≠ 0) :
    (dominationPolynomial (petalJoin a m B)).eval (y-1) = 0 ↔
      ((normalized B).eval y⁻¹)^m = 1-y^a := by
  rw [eval_join hm, sub_add_cancel, ← normalized_at_inverse B hy, mul_pow, ← pow_mul]
  have hn := pow_ne_zero (Fintype.card V*m) hy
  constructor
  · intro h
    apply (mul_left_inj' hn).mp
    linear_combination h
  · intro h
    rw [h]
    ring

end TaskP.GraphRootRadius.Proof
