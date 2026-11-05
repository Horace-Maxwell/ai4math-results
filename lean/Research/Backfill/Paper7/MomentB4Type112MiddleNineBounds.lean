import Research.Backfill.Paper7.MomentB4Type112MiddleElevenSupport

/-! SOURCE ONLY. Recovered t=9 proof, with the complete original guard.
The imported generic quadratic inequality is bound to Root542's actual
successful Support production; no t10 pending source is imported. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem b4_catalog_below_646 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hhi : M ≤ 646) :
    M ≤ 396 ∨ (S = 25 ∧ M = 600) ∨ (S = 29 ∧ M = 612) ∨
      (S = 33 ∧ M = 624) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_below_646

theorem type112_nine_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,9,u,Q)) Q.val) :
    228+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 396 := by
  have hb := type112_accept_budget z 9 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 19 := by omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,_hS,hlo⟩
  have he : M = 228+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hd := type112_catalog_degree_lower z 9 u Q S hlo
  norm_num at hd
  have hMhi : M ≤ 646 := by
    have hh := b4_type112_moment_upper z.val 9 u.val Q.val 19 hbudget
    norm_num at hh
    nlinarith [hh]
  have hQhi : (Q.val : ℤ) ≤ 19 := by
    exact_mod_cast (show Q.val ≤ 19 by omega)
  have hprod : 0 ≤ (z.val : ℤ)*u.val :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hMbound : M ≤ 396 := by
    rcases b4_catalog_below_646 S M hm hMhi with
      h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · have hs : z.val+u.val ≤ 5 := by
        have hh : (z.val : ℤ)+u.val ≤ 5 := by omega
        exact_mod_cast hh
      have hsq : ((z.val : ℤ)+u.val)^2 ≤ (5 : ℤ)^2 := by
        exact_mod_cast Nat.pow_le_pow_left hs 2
      nlinarith
    · have hs : z.val+u.val ≤ 9 := by
        have hh : (z.val : ℤ)+u.val ≤ 9 := by omega
        exact_mod_cast hh
      have hsq : ((z.val : ℤ)+u.val)^2 ≤ (9 : ℤ)^2 := by
        exact_mod_cast Nat.pow_le_pow_left hs 2
      nlinarith
    · have hs : z.val+u.val ≤ 13 := by
        have hh : (z.val : ℤ)+u.val ≤ 13 := by omega
        exact_mod_cast hh
      have hsq : ((z.val : ℤ)+u.val)^2 ≤ (13 : ℤ)^2 := by
        exact_mod_cast Nat.pow_le_pow_left hs 2
      nlinarith
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_nine_moment_upper

theorem type112_nine_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,9,u,Q)) Q.val) :
    z.val ≤ 7 ∧ u.val ≤ 11 := by
  have hmoment := type112_nine_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 9 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 396 := by nlinarith
  have hcap : M-184-2*S ≤ 136 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hs : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 136 := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hzu' : (z.val : ℤ) ≤ u.val := by exact_mod_cast hzu
  constructor
  · have hh : (z.val : ℤ) ≤ 7 := by
      by_contra hn
      have hz8 : 8 ≤ (z.val : ℤ) := by omega
      have hu8 : 8 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((z.val : ℤ)-8),sq_nonneg ((u.val : ℤ)-8)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 11 := by
      by_contra hn
      have hu12 : 12 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-12),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_nine_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
