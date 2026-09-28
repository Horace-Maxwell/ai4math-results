import Research.AxialMSZ.Challenge

set_option autoImplicit false

namespace CodexAxial.SupplementChallenge
open AxialMSZ.Challenge

/-- The generating axes contained in D's a-block are precisely a and b. -/
def ExD_axes_in_block : Prop :=
  ExD.X ∩ (block ExD.μ (e 0) : Set (Fin 5 → ℚ)) = {e 0, e 1}

/-- Those contained axes generate only the 3C summand, a proper part of the block. -/
def ExD_block_not_axial_on_contained_axes : Prop :=
  gen ExD.μ (ExD.X ∩ (block ExD.μ (e 0) : Set (Fin 5 → ℚ))) =
      Submodule.span ℚ {e 0, e 1, e 2} ∧
    gen ExD.μ (ExD.X ∩ (block ExD.μ (e 0) : Set (Fin 5 → ℚ))) < block ExD.μ (e 0)

#print axioms ExD_axes_in_block
#print axioms ExD_block_not_axial_on_contained_axes

end CodexAxial.SupplementChallenge
