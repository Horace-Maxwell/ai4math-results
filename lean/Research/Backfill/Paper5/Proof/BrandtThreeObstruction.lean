import Research.Backfill.Paper5.Proof.ReesBasic
import Research.Backfill.Paper5.Proof.SignSmall

set_option autoImplicit false

namespace CodexPaper5.BrandtThreeObstruction

open BackfillPaper5 Function

/-- The actual Brandt semigroup appearing in the frozen Proposition 6.2. -/
abbrev S := Challenge.Rees0 (Challenge.Sym 2) (Fin 3) (Fin 3)

/-- The sign of the group coordinate; the absorbing zero contributes zero. -/
def epsilon : S → ZMod 2
  | none => 0
  | some (_, g, _) => Challenge.sgn g

/-- An explicit finite enumeration obtained from the actual permutation type. -/
@[instance_reducible]
def symTwoFintype : Fintype (Challenge.Sym 2) :=
  Fintype.ofEquiv (Equiv.Perm (Fin 2)) MulOpposite.opEquiv

section FiniteSums

attribute [local instance] symTwoFintype

theorem card_sym_two : Fintype.card (Challenge.Sym 2) = 2 := by
  calc
    Fintype.card (Challenge.Sym 2) = Fintype.card (Equiv.Perm (Fin 2)) :=
      Fintype.card_congr MulOpposite.opEquiv.symm
    _ = 2 := by norm_num [Fintype.card_perm]

/-- The already verified sign section enumerates precisely the two actual permutations. -/
theorem rep_two_bijective : Bijective (SignSmall.rep 2) := by
  apply (Fintype.bijective_iff_injective_and_card (SignSmall.rep 2)).2
  constructor
  · intro u v huv
    calc
      u = Challenge.sgn (SignSmall.rep 2 u) :=
        (SignSmall.sgn_rep (r := 2) (by omega) u).symm
      _ = Challenge.sgn (SignSmall.rep 2 v) := congrArg Challenge.sgn huv
      _ = v := SignSmall.sgn_rep (r := 2) (by omega) v
  · rw [ZMod.card, card_sym_two]

/-- Reindex the true sign sum by its two parity representatives. -/
theorem sum_sgn : (∑ g : Challenge.Sym 2, Challenge.sgn g) = 1 := by
  calc
    (∑ g : Challenge.Sym 2, Challenge.sgn g) = ∑ u : ZMod 2, u :=
      (Fintype.sum_bijective (SignSmall.rep 2) rep_two_bijective
        (fun u : ZMod 2 => u) (fun g : Challenge.Sym 2 => Challenge.sgn g)
        (fun u => (SignSmall.sgn_rep (r := 2) (by omega) u).symm)).symm
    _ = 1 := by decide +kernel

/-- Each of the nine index pairs contributes the true two-element sign sum. -/
theorem sum_epsilon : (∑ x : S, epsilon x) = 1 := by
  have hthree (a : ZMod 2) : (∑ _ : Fin 3, a) = a := by
    simp only [Fin.sum_univ_three, CharTwo.add_self_eq_zero, zero_add]
  calc
    (∑ x : S, epsilon x) =
        ∑ _ : Fin 3, ∑ g : Challenge.Sym 2, ∑ _ : Fin 3, Challenge.sgn g := by
      simp only [Fintype.sum_option, epsilon, zero_add, Fintype.sum_prod_type]
    _ = ∑ _ : Fin 3, ∑ g : Challenge.Sym 2, Challenge.sgn g := by
      simp_rw [hthree]
    _ = 1 := by
      rw [sum_sgn, hthree]

end FiniteSums

/-- Both bijections in a complete mapping force the absorbing zero to be fixed. -/
theorem alpha_zero (α : S → S)
    (hα : Challenge.IsCompleteMapping (Challenge.rees0Mul Challenge.delta3) α) :
    α none = none := by
  apply CodexPaper5.check_ZeroFixed S (Challenge.rees0Mul Challenge.delta3) none
    (fun x => ?_) α hα
  constructor
  · rfl
  · cases x <;> rfl

theorem alpha_ne_zero (α : S → S)
    (hα : Challenge.IsCompleteMapping (Challenge.rees0Mul Challenge.delta3) α)
    {x : S} (hx : x ≠ none) : α x ≠ none := by
  intro h
  apply hx
  apply hα.1.1
  exact h.trans (alpha_zero α hα).symm

/-- The product bijection cannot send any nonzero element to the zero product. -/
theorem selected_ne_zero (α : S → S)
    (hα : Challenge.IsCompleteMapping (Challenge.rees0Mul Challenge.delta3) α)
    {x : S} (hx : x ≠ none) :
    Challenge.rees0Mul Challenge.delta3 x (α x) ≠ none := by
  intro h
  apply hx
  apply hα.2.1
  simpa only [Challenge.rees0Mul] using h

/-- Additivity is required only for the nonzero products selected by a complete mapping. -/
theorem epsilon_selected_add (α : S → S)
    (hα : Challenge.IsCompleteMapping (Challenge.rees0Mul Challenge.delta3) α)
    (x : S) :
    epsilon (Challenge.rees0Mul Challenge.delta3 x (α x)) =
      epsilon x + epsilon (α x) := by
  cases x with
  | none =>
      rw [alpha_zero α hα]
      simp only [Challenge.rees0Mul, epsilon, zero_add]
  | some p =>
      rcases p with ⟨i, g, l⟩
      obtain ⟨⟨j, h, m⟩, hαx⟩ :=
        Option.ne_none_iff_exists'.mp (alpha_ne_zero α hα (x := some (i, g, l)) (by simp))
      have hlj : l = j := by
        by_contra hne
        apply selected_ne_zero α hα (x := some (i, g, l)) (by simp)
        rw [hαx]
        simp only [Challenge.rees0Mul, Challenge.delta3, ite_eq_right hne, Option.map_none]
      rw [hαx]
      simp only [Challenge.rees0Mul, Challenge.delta3, ite_eq_left hlj,
        Option.map_some, mul_one, epsilon]
      exact CycleRemarks.sgn_mul g h

section FiniteObstruction

attribute [local instance] symTwoFintype

/-- No function can be a complete mapping of the frozen Brandt semigroup. -/
theorem no_complete_mapping :
    ¬ ∃ α : S → S, Challenge.IsCompleteMapping (Challenge.rees0Mul Challenge.delta3) α := by
  rintro ⟨α, hα⟩
  have hsum : (∑ x : S, epsilon x) = (∑ x : S, epsilon x) + ∑ x : S, epsilon x := by
    calc
      (∑ x : S, epsilon x) =
          ∑ x : S, epsilon (Challenge.rees0Mul Challenge.delta3 x (α x)) :=
        (hα.2.sum_comp epsilon).symm
      _ = ∑ x : S, (epsilon x + epsilon (α x)) :=
        Finset.sum_congr rfl (fun x _ => epsilon_selected_add α hα x)
      _ = (∑ x : S, epsilon x) + ∑ x : S, epsilon x := by
        rw [Finset.sum_add_distrib, hα.1.sum_comp epsilon]
  rw [sum_epsilon] at hsum
  have hzero : (1 : ZMod 2) = 0 := by
    simpa only [CharTwo.add_self_eq_zero] using hsum
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hzero

end FiniteObstruction

/-- Complete mappings transport across an equivalence preserving arbitrary binary operations. -/
theorem transport_complete_mapping {A B : Type*} (opA : A → A → A) (opB : B → B → B)
    (e : A ≃ B) (hm : ∀ x y, e (opA x y) = opB (e x) (e y))
    (α : A → A) (hα : Challenge.IsCompleteMapping opA α) :
    Challenge.IsCompleteMapping opB (fun b => e (α (e.symm b))) := by
  constructor
  · exact e.bijective.comp (hα.1.comp e.symm.bijective)
  · have heq : (fun b : B => opB b (e (α (e.symm b)))) =
        (fun b : B => e (opA (e.symm b) (α (e.symm b)))) := by
      funext b
      rw [hm, e.apply_symm_apply]
    change Bijective (fun b : B => opB b (e (α (e.symm b))))
    rw [heq]
    exact e.bijective.comp (hα.2.comp e.symm.bijective)

end CodexPaper5.BrandtThreeObstruction

#print axioms CodexPaper5.BrandtThreeObstruction.S
#print axioms CodexPaper5.BrandtThreeObstruction.epsilon
#print axioms CodexPaper5.BrandtThreeObstruction.symTwoFintype
#print axioms CodexPaper5.BrandtThreeObstruction.card_sym_two
#print axioms CodexPaper5.BrandtThreeObstruction.rep_two_bijective
#print axioms CodexPaper5.BrandtThreeObstruction.sum_sgn
#print axioms CodexPaper5.BrandtThreeObstruction.sum_epsilon
#print axioms CodexPaper5.BrandtThreeObstruction.alpha_zero
#print axioms CodexPaper5.BrandtThreeObstruction.alpha_ne_zero
#print axioms CodexPaper5.BrandtThreeObstruction.selected_ne_zero
#print axioms CodexPaper5.BrandtThreeObstruction.epsilon_selected_add
#print axioms CodexPaper5.BrandtThreeObstruction.no_complete_mapping
#print axioms CodexPaper5.BrandtThreeObstruction.transport_complete_mapping
