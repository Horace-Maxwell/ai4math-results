import Research.Backfill.Paper7.MomentB4Type112MiddleSixBounds

/-! SOURCE ONLY. Actual573 supplies both generic quadratic lemmas.
The original t=3 budget is used; no t4 or t5 source is imported. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_three_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,3,u,Q)) Q.val) :
    z.val ≤ 18 ∧ u.val ≤ 26 := by
  have hb := type112_accept_budget z 3 u Q ha
  have hs : (z.val : ℤ)+u.val ≤ 31 := by
    have hh : z.val+u.val ≤ 31 := by omega
    exact_mod_cast hh
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hcap := type112_endpoint_quadratic_sum_cap
    (z.val : ℤ) u.val 0 31 hz hu (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega)
  norm_num at hcap
  obtain ⟨⟨S,M⟩,hm,hlo,hhi⟩ :=
    type112_accept_catalog_quadratic_interval z 3 u Q ha
  dsimp only [Prod.fst,Prod.snd] at hlo hhi
  norm_num at hlo hhi
  have hM : M ≤ 1102 := by nlinarith only [hcap,hlo]
  have hcatalog : M-28-2*S ≤ 730 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hF : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 730 := by
    nlinarith only [hhi,hcatalog]
  have hzu' : (z.val : ℤ) ≤ u.val := by exact_mod_cast hzu
  constructor
  · have hh : (z.val : ℤ) ≤ 18 := by
      by_contra hn
      have hz19 : 19 ≤ (z.val : ℤ) := by omega
      have hu19 : 19 ≤ (u.val : ℤ) := by omega
      nlinarith only [hF,hz19,hu19,
        sq_nonneg ((z.val : ℤ)-19),sq_nonneg ((u.val : ℤ)-19)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 26 := by
      by_contra hn
      have hu27 : 27 ≤ (u.val : ℤ) := by omega
      nlinarith only [hF,hz,hu27,
        sq_nonneg ((u.val : ℤ)-27),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_three_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
