import Research.RM714Weights

/-! Audit file for `Research.RM714Weights`: prints the final statement and the key definitions,
plus small semantic checks of the definitions. -/

set_option autoImplicit false

#print RM714.evalPoly
#print RM714.weight
#print RM714.IsRM714Weight
#check @RM714.rm714_new_weights
#check @RM714.weight_map_maskSet
#check @RM714.isRM714Weight_of

-- Semantic sanity checks (via the bridge + kernel computation):
-- a single monomial x1⋯x7 has weight 2^7 = 128; x1⋯x7 + x8⋯x14 has weight 254 = 2·127;
-- the constant 1 (empty monomial) has weight 2^14; x1 has weight 2^13.
example : RM714.weight ([127].map RM714.maskSet) = 128 := by
  rw [RM714.weight_map_maskSet _ (by decide)]; decide +kernel
example : RM714.weight ([127, 16256].map RM714.maskSet) = 254 := by
  rw [RM714.weight_map_maskSet _ (by decide)]; decide +kernel
example : RM714.weight ([0].map RM714.maskSet) = 16384 := by
  rw [RM714.weight_map_maskSet _ (by decide)]; decide +kernel
example : RM714.weight ([1].map RM714.maskSet) = 8192 := by
  rw [RM714.weight_map_maskSet _ (by decide)]; decide +kernel
-- the mask 127 is the variable set {x1,…,x7} = {0,…,6} : Finset (Fin 14), of degree 7
example : RM714.degNat 127 = 7 := by decide +kernel
example : RM714.degNat 16256 = 7 := by decide +kernel

#print axioms RM714.rm714_new_weights
#print axioms RM714.weight_map_maskSet
#print axioms RM714.isRM714Weight_of
