import Research.Backfill.Paper7.MomentB4Type112MiddleSixBounds

/-! SOURCE ONLY. The imported t6 Bounds package is a separately sealed
pending dependency unless a later actual successful producer is bound.
Its generic quadratic cap is reused; the entire original t=5 guard remains. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_five_moment_upper_from_endpoint_bound (z u Q N : ℕ)
    (hbudget : z+u+Q ≤ 27) (hs : z+u ≤ N) :
    92+3*((z : ℤ)+u)+(z : ℤ)^2+(u : ℤ)^2+2*(Q : ℤ) ≤
      146+(N : ℤ)+(N : ℤ)^2 := by
  have hsq : ((z : ℤ)+u)^2 ≤ (N : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hs 2
  have hlin : (z : ℤ)+u+Q ≤ 27 := by exact_mod_cast hbudget
  have hsum : (z : ℤ)+u ≤ N := by exact_mod_cast hs
  have hprod : 0 ≤ (z : ℤ)*u :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_five_moment_upper_from_endpoint_bound

theorem b4_catalog_below_902 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hhi : M ≤ 902) :
    M ≤ 396 ∨ (S = 25 ∧ M = 600) ∨ (S = 29 ∧ M = 612) ∨
      (S = 33 ∧ M = 624) ∨ (S = 34 ∧ M = 672) ∨ (S = 38 ∧ M = 684) ∨
      (S = 41 ∧ M = 840) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_below_902

theorem type112_five_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,5,u,Q)) Q.val) :
    92+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 396 := by
  have hb := type112_accept_budget z 5 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 27 := by omega
  have hlin : (z.val : ℤ)+u.val+Q.val ≤ 27 := by exact_mod_cast hbudget
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,hlo⟩
  have he : M = 92+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith only [hM]
  have hd := type112_catalog_degree_lower z 5 u Q S hlo
  norm_num at hd
  have hupp : S ≤ 14+(z.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith
  have hquad : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+64+2*S ≤ M := by
    nlinarith only [he, hupp]
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hMhi : M ≤ 902 := by
    have hh := b4_type112_moment_upper z.val 5 u.val Q.val 27 hbudget
    norm_num at hh
    nlinarith only [he, hh]
  have hMbound : M ≤ 396 := by
    rcases b4_catalog_below_902 S M hm hMhi with
      h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · have hs : z.val+u.val ≤ 13 := by
        have hh : (z.val : ℤ)+u.val ≤ 13 := by omega
        exact_mod_cast hh
      have hh := type112_five_moment_upper_from_endpoint_bound
        z.val u.val Q.val 13 hbudget hs
      norm_num at hh
      nlinarith only [he, hh]
    · have hs : z.val+u.val ≤ 17 := by
        have hh : (z.val : ℤ)+u.val ≤ 17 := by omega
        exact_mod_cast hh
      have hh := type112_five_moment_upper_from_endpoint_bound
        z.val u.val Q.val 17 hbudget hs
      norm_num at hh
      nlinarith only [he, hh]
    · have hs : z.val+u.val ≤ 21 := by
        have hh : (z.val : ℤ)+u.val ≤ 21 := by omega
        exact_mod_cast hh
      have hh := type112_five_moment_upper_from_endpoint_bound
        z.val u.val Q.val 21 hbudget hs
      norm_num at hh
      nlinarith only [he, hh]
    · have hzcap : (z.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (z.val : ℤ) := by omega
        nlinarith only [hquad, hh, hu, sq_nonneg ((z.val : ℤ)-23),sq_nonneg (u.val : ℤ)]
      have hucap : (u.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (u.val : ℤ) := by omega
        nlinarith only [hquad, hh, hz, sq_nonneg ((u.val : ℤ)-23),sq_nonneg (z.val : ℤ)]
      have hsmall := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 0 22 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by omega)
      norm_num at hsmall
      nlinarith only [he, hlin, hsmall]
    · have hzcap : (z.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (z.val : ℤ) := by omega
        nlinarith only [hquad, hh, hu, sq_nonneg ((z.val : ℤ)-23),sq_nonneg (u.val : ℤ)]
      have hucap : (u.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (u.val : ℤ) := by omega
        nlinarith only [hquad, hh, hz, sq_nonneg ((u.val : ℤ)-23),sq_nonneg (z.val : ℤ)]
      have hsmall := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 4 22 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by omega)
      norm_num at hsmall
      nlinarith only [he, hlin, hsmall]
    · have hzcap : (z.val : ℤ) ≤ 25 := by
        by_contra hn
        have hh : 26 ≤ (z.val : ℤ) := by omega
        nlinarith only [hquad, hh, hu, sq_nonneg ((z.val : ℤ)-26),sq_nonneg (u.val : ℤ)]
      have hucap : (u.val : ℤ) ≤ 25 := by
        by_contra hn
        have hh : 26 ≤ (u.val : ℤ) := by omega
        nlinarith only [hquad, hh, hz, sq_nonneg ((u.val : ℤ)-26),sq_nonneg (z.val : ℤ)]
      have hsmall := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 4 25 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by omega)
      norm_num at hsmall
      nlinarith only [he, hlin, hsmall]
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_five_moment_upper

theorem type112_five_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,5,u,Q)) Q.val) :
    z.val ≤ 10 ∧ u.val ≤ 15 := by
  have hmoment := type112_five_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 5 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 396 := by nlinarith
  have hcap : M-64-2*S ≤ 256 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hs : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 256 := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hzu' : (z.val : ℤ) ≤ u.val := by exact_mod_cast hzu
  constructor
  · have hh : (z.val : ℤ) ≤ 10 := by
      by_contra hn
      have hz11 : 11 ≤ (z.val : ℤ) := by omega
      have hu11 : 11 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((z.val : ℤ)-11),sq_nonneg ((u.val : ℤ)-11)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 15 := by
      by_contra hn
      have hu16 : 16 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-16),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_five_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
