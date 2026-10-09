import Research.Backfill.Paper6.ChallengeV3

/-!
# Paper 6 V3: dimensions of two transversal flats

A one-point intersection is nonempty and has zero direction. Choosing its
unique point identifies the intersection of the two direction submodules with
that zero direction. The submodule dimension formula then bounds the sum of
the two dimensions by the dimension of the ambient vector space. In dimension
14, two dimensions each at least 7 must therefore both be 7.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
This source is a candidate for root-controlled compilation and acceptance.
-/

set_option autoImplicit false

namespace Paper6Geometry

open BackfillPaper6.V3

/-- A singleton intersection forces the direction submodules to have zero intersection.
Nonemptiness is deduced from cardinality one, not imposed as an extra hypothesis. -/
theorem direction_inf_eq_bot_of_inter_ncard_one {m : ℕ}
    (F1 F2 : AffineSubspace (ZMod 2) (Pt m))
    (hcard : ((F1 : Set (Pt m)) ∩ F2).ncard = 1) :
    F1.direction ⊓ F2.direction = ⊥ := by
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard
  have hmem : x ∈ (F1 : Set (Pt m)) ∩ F2 := by
    rw [hx]
    simp
  have hsub : ((F1 ⊓ F2 : AffineSubspace (ZMod 2) (Pt m)) : Set (Pt m)).Subsingleton := by
    change ((F1 : Set (Pt m)) ∩ F2).Subsingleton
    rw [hx]
    exact Set.subsingleton_singleton
  have hdir : (F1 ⊓ F2).direction = ⊥ :=
    AffineSubspace.direction_eq_bot_iff.mpr hsub
  rw [AffineSubspace.direction_inf_of_mem hmem.1 hmem.2] at hdir
  exact hdir

/-- The actual ambient binary function space has its expected dimension. -/
theorem ambient_finrank (m : ℕ) : Module.finrank (ZMod 2) (Pt m) = m := by
  change Module.finrank (ZMod 2) (Fin m → ZMod 2) = m
  rw [Module.finrank_pi, Fintype.card_fin]

/-- Transversality bounds the sum of the two direction dimensions by the ambient dimension. -/
theorem finrank_sum_le_of_inter_ncard_one {m : ℕ}
    (F1 F2 : AffineSubspace (ZMod 2) (Pt m))
    (hcard : ((F1 : Set (Pt m)) ∩ F2).ncard = 1) :
    Module.finrank (ZMod 2) F1.direction +
      Module.finrank (ZMod 2) F2.direction ≤ m := by
  have hinf := direction_inf_eq_bot_of_inter_ncard_one F1 F2 hcard
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq F1.direction F2.direction
  rw [hinf, finrank_bot, add_zero] at hdim
  calc
    Module.finrank (ZMod 2) F1.direction +
        Module.finrank (ZMod 2) F2.direction =
        Module.finrank (ZMod 2) (F1.direction ⊔ F2.direction : Submodule (ZMod 2) (Pt m)) := hdim.symm
    _ ≤ Module.finrank (ZMod 2) (Pt m) := Submodule.finrank_le _
    _ = m := ambient_finrank m

/-- The exact frozen V3 statement for two flats in binary dimension fourteen. -/
theorem transversalDim : BackfillPaper6.V3.TransversalDim := by
  intro F1 F2 h1 h2 hcard
  have hsum := finrank_sum_le_of_inter_ncard_one F1 F2 hcard
  omega

/-- Exact contract check; this alias does not count as another mathematical result. -/
theorem check_TransversalDim : BackfillPaper6.V3.TransversalDim := transversalDim

end Paper6Geometry

#print axioms Paper6Geometry.direction_inf_eq_bot_of_inter_ncard_one
#print axioms Paper6Geometry.ambient_finrank
#print axioms Paper6Geometry.finrank_sum_le_of_inter_ncard_one
#print axioms Paper6Geometry.transversalDim
#print axioms Paper6Geometry.check_TransversalDim
#print Paper6Geometry.check_TransversalDim
