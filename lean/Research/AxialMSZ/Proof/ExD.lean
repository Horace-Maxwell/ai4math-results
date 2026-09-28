import Research.AxialMSZ.Proof.ExDBlock
import Research.AxialMSZ.Proof.ExDFrobenius

/-!
The complete frozen ExD.Statement / TheoremC, with no additional hypotheses.
The coordinate, block and Frobenius proofs are imported from the three
preceding modules. The general Corollary is assembled separately.
-/
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

theorem check_ExD_Statement : AxialMSZ.Challenge.ExD.Statement := by
  exact ⟨DecomposableExample.axial,
    DecomposableExample.decomposable_block,
    DecomposableExample.frobenius_exists,
    DecomposableExample.block_a_exact,
    DecomposableExample.first_internal_ideal,
    DecomposableExample.second_internal_ideal,
    DecomposableExample.notWholeIdeal⟩

theorem check_TheoremC : AxialMSZ.Challenge.TheoremC := check_ExD_Statement

#print axioms check_ExD_Statement
#print axioms check_TheoremC
end CodexAxial
