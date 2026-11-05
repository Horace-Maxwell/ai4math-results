import Research.Backfill.Paper7.IntroGraphRealRootObstruction
import Research.Backfill.Paper7.IntroOddSchwenkParity

/-! A root constraint on the actual antisymmetric part of every odd-cycle
unicyclic graph. Arbitrary off-cycle branching remains in the scope. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddForest
open SimpleGraph Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra

theorem unicyclic_odd_antipart_root_real
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b) (z : ℂ)
    (hz : ((graphPhi G - C ((-1 : ℤ) ^ Fintype.card V) *
      (graphPhi G).comp (-X)).map (Int.castRingHom ℂ)).IsRoot z) : z.im = 0 := by
  obtain ⟨r, w, _hw, _hlen, _hforest, _hcard, hid⟩ :=
    unicyclic_odd_exists_forest_identity G b hG hb
  have hz0 := hz.eq_zero
  rw [hid, Polynomial.map_mul, Polynomial.eval_mul,
    Polynomial.map_C, Polynomial.eval_C] at hz0
  have hforest : ((graphPhi (deleteVertices G {v | v ∈ w.support})).map
      (Int.castRingHom ℂ)).IsRoot z :=
    (mul_eq_zero.mp hz0).resolve_left (by norm_num)
  exact graphPhi_complex_root_real (deleteVertices G {v | v ∈ w.support}) z hforest
#print axioms Paper7IntroOddForest.unicyclic_odd_antipart_root_real

theorem unicyclic_odd_antipart_not_dvd_radiusThreeForestFactor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b) :
    ¬ radiusThreeForestFactor ∣
      graphPhi G - C ((-1 : ℤ) ^ Fintype.card V) * (graphPhi G).comp (-X) :=
  radiusThreeForestFactor_not_dvd_of_real_roots _
    (unicyclic_odd_antipart_root_real G b hG hb)
#print axioms Paper7IntroOddForest.unicyclic_odd_antipart_not_dvd_radiusThreeForestFactor

end Paper7IntroOddForest
