import Research.ICGEqualParityBGraph

set_option autoImplicit false

/-! Statement and axiom audit for Theorem B (round 6, `work/round6/equal-parity-a2/PROOF.md`). -/

-- definitions used in the statements
#print ICGEqualParityB.Theta
#print ICGEqualParityB.Gfun
#print ICGEqualParityB.Ym
#print ICGEqualParityB.Yp
#print ICGEqualParityB.ParamB
#print ICGEqualParityB.SignMat
#print ICGEqualParityB.DtruncB
#print ICGEqualParity.DantiPQ
#print ICGGeneral.DstarPQ
-- main statements
#check @ICGEqualParityB.theoremB
#check @ICGEqualParityB.corollaryB
#check @ICGEqualParityB.theoremB_swap
#check @ICGEqualParityB.thmB'
-- key lemmas
#check @ICGEqualParityB.prop1
#check @ICGEqualParityB.lemS
#check @ICGEqualParityB.fd1
#check @ICGEqualParityB.fd2a
#check @ICGEqualParityB.fd2dom
#check @ICGEqualParityB.eq_all
#check @ICGEqualParityB.G_Ym
#check @ICGEqualParityB.G_Yp
#check @ICGEqualParityB.two_L1mat_rows2
-- axioms
#print axioms ICGEqualParityB.theoremB
#print axioms ICGEqualParityB.corollaryB
#print axioms ICGEqualParityB.theoremB_swap
#print axioms ICGEqualParityB.thmB'
#print axioms ICGEqualParityB.prop1
#print axioms ICGEqualParityB.lemS
#print axioms ICGEqualParityB.fd1
#print axioms ICGEqualParityB.fd2a
#print axioms ICGEqualParityB.fd2dom
#print axioms ICGEqualParityB.G_Yp
