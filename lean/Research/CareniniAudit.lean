import Research.Carenini

set_option autoImplicit false

/-!
# Audit printout for `Research.Carenini`

Prints the key definitions, the final statements and their axioms, for comparison with
Section 9 (Table 4) of the paper "A negative answer to a question of Carenini on almost
independent sets in regular graphs" and with Question 1.3 of Carenini, arXiv:2609.28527v1.
This file is not imported by `Research.lean`.
-/

-- Key definitions
#print Carenini.edgesIn
#print Carenini.iCount
#print Carenini.iGamma
#print Carenini.KddUnion
#print Carenini.CareniniQuestion

-- Competitor and reference graphs
#print Carenini.K33
#print Carenini.prism
#print Carenini.swAdj
#print Carenini.switchedKdd
#print Carenini.C8
#print Carenini.h3Adj
#print Carenini.H3
#print Carenini.threeK4

-- The five negative results (Table 4 of the paper)
#check @Carenini.not_careniniQuestion_six
#check @Carenini.not_careniniQuestion_two_d
#check @Carenini.not_careniniQuestion_eight_two
#check @Carenini.not_careniniQuestion_twelve_bip
#check @Carenini.not_careniniQuestion_twelve_top

-- Supporting statements named in Section 9
#check @Carenini.iGamma_eq_iCount_floor
#check @Carenini.iGamma_eq_iCount
#check @Carenini.iGamma_iso
#check @Carenini.iCount_iso
#check @Carenini.prism_regular
#check @Carenini.K33_regular
#check @Carenini.iCount_prism_one
#check @Carenini.iCount_K33_one
#check @Carenini.iCount_KddUnion_one
#check @Carenini.prismIso
#check @Carenini.K33Iso
#check @Carenini.K33IsoKddUnion
#check @Carenini.prism_beats_K33
#check @Carenini.switchedKdd_regular
#check @Carenini.edgesIn_switched_le_one
#check @Carenini.switched_extra_set
#check @Carenini.iCount_one_lt
#check @Carenini.kddUnionOneIso
#check @Carenini.C8_regular
#check @Carenini.iCount_C8_one
#check @Carenini.iCount_2C4_one
#check @Carenini.H3_regular
#check @Carenini.H3_bipartite
#check @Carenini.H3_connected
#check @Carenini.iCount_H3_one
#check @Carenini.iCount_2K33_one
#check @Carenini.threeK4_regular
#check @Carenini.iCount_threeK4_ten
#check @Carenini.iCount_2K33_ten
#check @Carenini.KddUnion_two_three_regular

-- Small semantic checks of the definitions (kernel evaluation):
-- `KddUnion 1 3` is `K_{3,3}`, with 9 edges and 2^4 - 1 = 15 independent sets;
-- in `KddUnion 2 3` two vertices are adjacent only inside one copy, across the two sides.
example : Carenini.edgesIn (Carenini.KddUnion 1 3) Finset.univ = 9 := by decide
example : Carenini.iCount (Carenini.KddUnion 1 3) 0 = 15 := by decide
example : ¬ (Carenini.KddUnion 2 3).Adj (0, .inl 0) (1, .inr 0) := by decide
example : ¬ (Carenini.KddUnion 2 3).Adj (1, .inl 0) (1, .inl 2) := by decide
example : (Carenini.KddUnion 2 3).Adj (1, .inl 0) (1, .inr 2) := by decide

-- Axioms of the five negative results and of the key definitions
#print axioms Carenini.not_careniniQuestion_six
#print axioms Carenini.not_careniniQuestion_two_d
#print axioms Carenini.not_careniniQuestion_eight_two
#print axioms Carenini.not_careniniQuestion_twelve_bip
#print axioms Carenini.not_careniniQuestion_twelve_top
#print axioms Carenini.CareniniQuestion
#print axioms Carenini.iGamma
#print axioms Carenini.iCount
#print axioms Carenini.edgesIn
#print axioms Carenini.KddUnion
