import Research.Backfill.Paper7.MomentB4Type112MiddleElevenSupport

/-! SOURCE ONLY. Complete original t=7 guard and catalogue. No t8, t9
or t10 module is imported. The final high-moment case uses the original
quadratic inequality and budget, without any candidate support premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_seven_moment_upper_from_endpoint_bound (z u Q N : ℕ)
    (hbudget : z+u+Q ≤ 23) (hs : z+u ≤ N) :
    152+3*((z : ℤ)+u)+(z : ℤ)^2+(u : ℤ)^2+2*(Q : ℤ) ≤
      198+(N : ℤ)+(N : ℤ)^2 := by
  have hsq : ((z : ℤ)+u)^2 ≤ (N : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hs 2
  have hlin : (z : ℤ)+u+Q ≤ 23 := by exact_mod_cast hbudget
  have hsum : (z : ℤ)+u ≤ N := by exact_mod_cast hs
  have hprod : 0 ≤ (z : ℤ)*u :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_seven_moment_upper_from_endpoint_bound

theorem b4_catalog_below_750 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hhi : M ≤ 750) :
    M ≤ 396 ∨ (S = 25 ∧ M = 600) ∨ (S = 29 ∧ M = 612) ∨
      (S = 33 ∧ M = 624) ∨ (S = 34 ∧ M = 672) ∨ (S = 38 ∧ M = 684) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_below_750

theorem type112_seven_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,7,u,Q)) Q.val) :
    152+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 396 := by
  have hb := type112_accept_budget z 7 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 23 := by omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,hlo⟩
  have he : M = 152+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hd := type112_catalog_degree_lower z 7 u Q S hlo
  norm_num at hd
  have hupp : S ≤ 18+(z.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith
  have hquad : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+116+2*S ≤ M := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hMhi : M ≤ 750 := by
    have hh := b4_type112_moment_upper z.val 7 u.val Q.val 23 hbudget
    norm_num at hh
    nlinarith [hh]
  have hMbound : M ≤ 396 := by
    rcases b4_catalog_below_750 S M hm hMhi with
      h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · have hs : z.val+u.val ≤ 9 := by
        have hh : (z.val : ℤ)+u.val ≤ 9 := by omega
        exact_mod_cast hh
      have hh := type112_seven_moment_upper_from_endpoint_bound
        z.val u.val Q.val 9 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 13 := by
        have hh : (z.val : ℤ)+u.val ≤ 13 := by omega
        exact_mod_cast hh
      have hh := type112_seven_moment_upper_from_endpoint_bound
        z.val u.val Q.val 13 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 17 := by
        have hh : (z.val : ℤ)+u.val ≤ 17 := by omega
        exact_mod_cast hh
      have hh := type112_seven_moment_upper_from_endpoint_bound
        z.val u.val Q.val 17 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 18 := by
        have hh : (z.val : ℤ)+u.val ≤ 18 := by omega
        exact_mod_cast hh
      have hh := type112_seven_moment_upper_from_endpoint_bound
        z.val u.val Q.val 18 hbudget hs
      nlinarith
    · have hzcap : (z.val : ℤ) ≤ 21 := by
        by_contra hn
        have hh : 22 ≤ (z.val : ℤ) := by omega
        nlinarith [sq_nonneg ((z.val : ℤ)-22),sq_nonneg (u.val : ℤ)]
      have hucap : (u.val : ℤ) ≤ 21 := by
        by_contra hn
        have hh : 22 ≤ (u.val : ℤ) := by omega
        nlinarith [sq_nonneg ((u.val : ℤ)-22),sq_nonneg (z.val : ℤ)]
      have hzprod : 0 ≤ (z.val : ℤ)*(21-z.val) := mul_nonneg hz (by omega)
      have huprod : 0 ≤ (u.val : ℤ)*(21-u.val) := mul_nonneg hu (by omega)
      have hlin : (z.val : ℤ)+u.val+Q.val ≤ 23 := by exact_mod_cast hbudget
      nlinarith
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_seven_moment_upper

theorem type112_seven_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,7,u,Q)) Q.val) :
    z.val ≤ 9 ∧ u.val ≤ 13 := by
  have hmoment := type112_seven_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 7 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 396 := by nlinarith
  have hcap : M-116-2*S ≤ 204 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hs : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 204 := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hzu' : (z.val : ℤ) ≤ u.val := by exact_mod_cast hzu
  constructor
  · have hh : (z.val : ℤ) ≤ 9 := by
      by_contra hn
      have hz10 : 10 ≤ (z.val : ℤ) := by omega
      have hu10 : 10 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((z.val : ℤ)-10),sq_nonneg ((u.val : ℤ)-10)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 13 := by
      by_contra hn
      have hu14 : 14 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-14),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_seven_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
