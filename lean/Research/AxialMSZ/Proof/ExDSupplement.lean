import Research.AxialMSZ.Proof.ExDBlock
import Research.AxialMSZ.SupplementDChallenge

/-! The two frozen supplemental statements about the generating axes in D's a-block. -/
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

namespace DecomposableExample

theorem gen_ab : gen ExD.μ {a,b} = J := by
  apply le_antisymm
  · apply gen_le_of_closed
    · rintro u (rfl | rfl) <;> norm_num [a,b,J,e,Pi.single_apply]
    · intro u hu v hv
      exact (J_idealIn.2 u (J_le_I hu) v hv).1
  · have ma : a ∈ gen ExD.μ {a,b} := mem_gen_of_mem (by simp)
    have mb : b ∈ gen ExD.μ {a,b} := mem_gen_of_mem (by simp)
    have mx : x ∈ gen ExD.μ {a,b} := by
      rw [x_from_ab]
      exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb)
        (Submodule.smul_mem _ _ (gen_isSubalgebra _ _ _ ma _ mb))
    rw [J_eq_span]
    apply Submodule.span_le.mpr
    rintro u (rfl | rfl | rfl)
    · exact ma
    · exact mb
    · exact mx

end DecomposableExample
open DecomposableExample

theorem check_ExD_axes_in_block : SupplementChallenge.ExD_axes_in_block := by
  change ExD.X ∩ (block ExD.μ a : Set A) = {a,b}
  rw [block_a]
  ext u
  constructor
  · rintro ⟨hu,hi⟩
    rcases hu with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num [I,e,Pi.single_apply] at hi
  · rintro (rfl | rfl) <;> norm_num [ExD.X,a,b,I,e,Pi.single_apply]

theorem check_ExD_block_not_axial_on_contained_axes :
    SupplementChallenge.ExD_block_not_axial_on_contained_axes := by
  unfold SupplementChallenge.ExD_block_not_axial_on_contained_axes
  rw [check_ExD_axes_in_block]
  change gen ExD.μ {a,b} = Submodule.span ℚ {a,b,x} ∧
    gen ExD.μ {a,b} < block ExD.μ a
  constructor
  · exact gen_ab.trans J_eq_span
  · rw [gen_ab,block_a]
    exact lt_iff_le_and_ne.mpr ⟨J_le_I,J_ne_I⟩

#print axioms check_ExD_axes_in_block
#print axioms check_ExD_block_not_axial_on_contained_axes
end CodexAxial
