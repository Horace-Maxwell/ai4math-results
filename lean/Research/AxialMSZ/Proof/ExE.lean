import Research.AxialMSZ.Proof.ExEGraph
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

theorem check_TheoremB : AxialMSZ.Challenge.TheoremB :=
  ⟨DominanceExample.axial, DominanceExample.blocks_strict, DominanceExample.blocks_equal,
    DominanceExample.block_c, DominanceExample.indecomposable, DominanceExample.disconnected,
    DominanceExample.components_do_not_annihilate⟩

theorem check_ExE_Statement : AxialMSZ.Challenge.ExE.Statement := check_TheoremB

#print axioms check_TheoremB
#print axioms check_ExE_Statement
end CodexAxial
