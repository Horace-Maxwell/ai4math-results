import Research.Backfill.Paper7.MomentB4Type112MiddleSixBounds

/-! SOURCE ONLY. Original t=0 guard, including all high catalogue moments.
Only actual573 generic Bounds and its successful imported closure are used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_zero_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,0,u,Q)) Q.val) :
    12+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 840 := by
  have hb := type112_accept_budget z 0 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 37 := by omega
  have hlin : (z.val : ℤ)+u.val+Q.val ≤ 37 := by exact_mod_cast hbudget
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,hlo⟩
  have he : M = 12+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith only [hM]
  have hd := type112_catalog_degree_lower z 0 u Q S hlo
  norm_num at hd
  have hupp : S ≤ 4+(z.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith only [hS]
  have hquad : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+4+2*S ≤ M := by
    nlinarith only [he,hupp]
  have hMbudget : M ≤ 86+(z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val := by
    nlinarith only [he,hlin]
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hcap33
      (hF : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 1188) :
      (z.val : ℤ) ≤ 33 ∧ (u.val : ℤ) ≤ 33 := by
    constructor
    · by_contra hnz
      have hz34 : 34 ≤ (z.val : ℤ) := by omega
      nlinarith only [hF,hz34,hu,
        sq_nonneg ((z.val : ℤ)-34),sq_nonneg (u.val : ℤ)]
    · by_contra hnu
      have hu34 : 34 ≤ (u.val : ℤ) := by omega
      nlinarith only [hF,hu34,hz,
        sq_nonneg ((u.val : ℤ)-34),sq_nonneg (z.val : ℤ)]
  have hMbound : M ≤ 840 := by
    by_contra hn
    have hhigh : (S = 36 ∧ M = 1260) ∨ (S = 40 ∧ M = 1272) := by
      norm_num [b4FeatureCatalog] at hm
      rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
        hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
        rcases hm with ⟨rfl,rfl⟩ <;> omega
    rcases hhigh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨hzcap,hucap⟩ := hcap33 (by nlinarith only [hquad])
      have hs : (z.val : ℤ)+u.val ≤ 34 := by omega
      have hcap := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 1 33 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by omega)
      norm_num at hcap
      nlinarith only [hcap,hMbudget]
    · obtain ⟨hzcap,hucap⟩ := hcap33 (by nlinarith only [hquad])
      have hcap := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 4 33 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by have := Int.natCast_nonneg Q.val; omega)
      norm_num at hcap
      nlinarith only [hcap,hMbudget]
  linarith only [he,hMbound]
#print axioms Paper7MomentCanonicalNumeric.type112_zero_moment_upper

theorem type112_zero_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,0,u,Q)) Q.val) :
    z.val ≤ 18 ∧ u.val ≤ 26 := by
  have hmoment := type112_zero_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 0 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 840 := by nlinarith only [he,hmoment]
  have hcatalog : M-4-2*S ≤ 754 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hF : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 754 := by
    nlinarith only [hquad,hcatalog]
  have hz := Int.natCast_nonneg z.val
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
#print axioms Paper7MomentCanonicalNumeric.type112_zero_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
