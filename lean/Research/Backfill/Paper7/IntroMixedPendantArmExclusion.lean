import Research.Backfill.Paper7.IntroMixedPendantArmDegree
import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion

/-! Actual mixed one-edge and two-edge pendant arms are impossible under
the original even integral unicyclic order bound. No component shape,
degree-four center or Sun hypothesis is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroMixedArms
open SimpleGraph BackfillPaper7.Challenge Paper7IntroFour

theorem intro21_even_no_mixed_pendant_arms
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v y k l : V) (hvk : G.Adj v k) (hvy : G.Adj v y) (hyl : G.Adj y l)
    (hvl : v ≠ l) (hk : G.degree k = 1) (hy : G.degree y = 2)
    (hl : G.degree l = 1) : False := by
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  have hd := integral_radius_three_mixed_pendant_arms_degree_twelve
    G hI hbound v y k l hvk hvy hyl hvl hk hy hl
  have hcap : ∀ t ∈ spec G, t ≤ (3 : ℝ) := by
    intro t ht
    exact (le_abs_self t).trans (hbound t ht)
  have hlt := unicyclic_degree_lt_spectral_bound_sq G b hG 3 (by norm_num) hcap v
  norm_num [hd] at hlt
#print axioms Paper7IntroMixedArms.intro21_even_no_mixed_pendant_arms

end Paper7IntroMixedArms
