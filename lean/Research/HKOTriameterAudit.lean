import Research.HKOTriameterDH

set_option autoImplicit false

/-!
# Audit printout for `Research.HKOTriameter` and `Research.HKOTriameterDH`

Prints the key definitions and the final statements, for comparison with
Hak–Kozerenko–Oliynyk, arXiv:2103.10806v1, Sections 2 and 4.
-/

open HKOTriameter

-- Key definitions
#print HKOTriameter.triDist
#print HKOTriameter.triameter
#print HKOTriameter.IsTriametral
#print HKOTriameter.IsDiametral
#print HKOTriameter.IsPeripheral
#print HKOTriameter.IsPeripheralPair
#print HKOTriameter.InInterval
#print HKOTriameter.IsMedian
#print HKOTriameter.Question3'
#print HKOTriameter.Question3'Pair
#print HKOTriameter.Question3
#print HKOTriameter.Question4
#print HKOTriameter.Question4'
#print HKOTriameter.Problem2ClaimWeak
#print HKOTriameter.Problem1Claim
#print HKOTriameter.Problem1ClaimPair
#print HKOTriameter.Problem2Claim
#print HKOTriameter.g1Edges
#print HKOTriameter.G1
#print HKOTriameter.g2Edges
#print HKOTriameter.G2
#print HKOTriameter.FP
#print HKOTriameter.FourPointBM
#print HKOTriameter.Problem3ClaimFP
#print HKOTriameter.f1gEdges
#print HKOTriameter.f1hEdges
-- Mathlib definitions used
#print SimpleGraph.dist
#print SimpleGraph.edist
#print SimpleGraph.diam
#print SimpleGraph.ediam
#print SimpleGraph.eccent

-- Final statements
#check @HKOTriameter.not_problem1Claim
#check @HKOTriameter.not_problem1ClaimPair
#check @HKOTriameter.not_problem2Claim
#check @HKOTriameter.not_problem2ClaimWeak
#check @HKOTriameter.G1_counterexample
#check @HKOTriameter.G2_counterexample
#check @HKOTriameter.not_question3_G1
#check @HKOTriameter.isPeripheral_iff_isPeripheralPair
#check @HKOTriameter.dist_eq_of_certificate
#check @HKOTriameter.G1_diam
#check @HKOTriameter.G1_triameter
#check @HKOTriameter.G2_diam
#check @HKOTriameter.G2_triameter
#check @HKOTriameter.C6_not_median
#check @HKOTriameter.core
#check @HKOTriameter.extends_of_no_diametral
#check @HKOTriameter.question3_or_question4
#check @HKOTriameter.question3'_of_question3
#check @HKOTriameter.problem3_fourPoint
#check @HKOTriameter.problem3ClaimFP
#check @HKOTriameter.F1G_fourPoint
#check @HKOTriameter.F1G_not_question3'
#check @HKOTriameter.F1H_fourPoint
#check @HKOTriameter.F1H_not_question4
#check @HKOTriameter.G1_not_fourPoint
#check @HKOTriameter.G2_fourPoint
#check @HKOTriameter.F1G_not_median

#print axioms HKOTriameter.not_problem1Claim
#print axioms HKOTriameter.not_problem1ClaimPair
#print axioms HKOTriameter.not_problem2Claim
#print axioms HKOTriameter.not_problem2ClaimWeak
#print axioms HKOTriameter.G1_counterexample
#print axioms HKOTriameter.G2_counterexample
#print axioms HKOTriameter.not_question3_G1
#print axioms HKOTriameter.isPeripheral_iff_isPeripheralPair
#print axioms HKOTriameter.C6_not_median
#print axioms HKOTriameter.core
#print axioms HKOTriameter.extends_of_no_diametral
#print axioms HKOTriameter.question3_or_question4
#print axioms HKOTriameter.problem3_fourPoint
#print axioms HKOTriameter.problem3ClaimFP
#print axioms HKOTriameter.F1G_fourPoint
#print axioms HKOTriameter.F1G_not_question3'
#print axioms HKOTriameter.F1H_fourPoint
#print axioms HKOTriameter.F1H_not_question4
#print axioms HKOTriameter.G1_not_fourPoint
#print axioms HKOTriameter.G2_fourPoint
#print axioms HKOTriameter.F1G_not_median
