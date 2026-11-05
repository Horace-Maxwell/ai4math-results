import Research.Backfill.Paper7.MomentB4Type112MiddleElevenSupport

/-! SOURCE ONLY. Original t=8 guard and catalogue, with no t9 or t10
dependency. The generic imported endpoint inequality is from Root542's
actual successful Support production. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem b4_type112_moment_upper_with_endpoint_bound (z t u Q K N : ℕ)
    (hbudget : z+u+Q ≤ K) (hs : z+u ≤ N) :
    12+6*(t : ℤ)+2*(t : ℤ)^2+3*((z : ℤ)+u)+(z : ℤ)^2+(u : ℤ)^2+
        2*(Q : ℤ) ≤
      12+6*(t : ℤ)+2*(t : ℤ)^2+2*(K : ℤ)+(N : ℤ)+(N : ℤ)^2 := by
  have hsq : ((z : ℤ)+u)^2 ≤ (N : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hs 2
  have hlin : (z : ℤ)+u+Q ≤ K := by exact_mod_cast hbudget
  have hsum : (z : ℤ)+u ≤ N := by exact_mod_cast hs
  have hprod : 0 ≤ (z : ℤ)*u :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.b4_type112_moment_upper_with_endpoint_bound

theorem b4_catalog_below_692 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hhi : M ≤ 692) :
    M ≤ 396 ∨ (S = 25 ∧ M = 600) ∨ (S = 29 ∧ M = 612) ∨
      (S = 33 ∧ M = 624) ∨ (S = 34 ∧ M = 672) ∨ (S = 38 ∧ M = 684) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_below_692

theorem type112_eight_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,8,u,Q)) Q.val) :
    188+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 396 := by
  have hb := type112_accept_budget z 8 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 21 := by omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,_hS,hlo⟩
  have he : M = 188+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hd := type112_catalog_degree_lower z 8 u Q S hlo
  norm_num at hd
  have hMhi : M ≤ 692 := by
    have hh := b4_type112_moment_upper z.val 8 u.val Q.val 21 hbudget
    norm_num at hh
    nlinarith [hh]
  have hMbound : M ≤ 396 := by
    rcases b4_catalog_below_692 S M hm hMhi with
      h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · have hs : z.val+u.val ≤ 7 := by
        have hh : (z.val : ℤ)+u.val ≤ 7 := by omega
        exact_mod_cast hh
      have hh := b4_type112_moment_upper_with_endpoint_bound
        z.val 8 u.val Q.val 21 7 hbudget hs
      norm_num at hh
      nlinarith
    · have hs : z.val+u.val ≤ 11 := by
        have hh : (z.val : ℤ)+u.val ≤ 11 := by omega
        exact_mod_cast hh
      have hh := b4_type112_moment_upper_with_endpoint_bound
        z.val 8 u.val Q.val 21 11 hbudget hs
      norm_num at hh
      nlinarith
    · have hs : z.val+u.val ≤ 15 := by
        have hh : (z.val : ℤ)+u.val ≤ 15 := by omega
        exact_mod_cast hh
      have hh := b4_type112_moment_upper_with_endpoint_bound
        z.val 8 u.val Q.val 21 15 hbudget hs
      norm_num at hh
      nlinarith
    · have hs : z.val+u.val ≤ 16 := by
        have hh : (z.val : ℤ)+u.val ≤ 16 := by omega
        exact_mod_cast hh
      have hh := b4_type112_moment_upper_with_endpoint_bound
        z.val 8 u.val Q.val 21 16 hbudget hs
      norm_num at hh
      nlinarith
    · have hs : z.val+u.val ≤ 20 := by
        have hh : (z.val : ℤ)+u.val ≤ 20 := by omega
        exact_mod_cast hh
      have hh := b4_type112_moment_upper_with_endpoint_bound
        z.val 8 u.val Q.val 21 20 hbudget hs
      norm_num at hh
      nlinarith
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_eight_moment_upper

theorem type112_eight_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,8,u,Q)) Q.val) :
    z.val ≤ 8 ∧ u.val ≤ 12 := by
  have hmoment := type112_eight_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 8 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 396 := by nlinarith
  have hcap : M-148-2*S ≤ 172 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hs : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 172 := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hzu' : (z.val : ℤ) ≤ u.val := by exact_mod_cast hzu
  constructor
  · have hh : (z.val : ℤ) ≤ 8 := by
      by_contra hn
      have hz9 : 9 ≤ (z.val : ℤ) := by omega
      have hu9 : 9 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((z.val : ℤ)-9),sq_nonneg ((u.val : ℤ)-9)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 12 := by
      by_contra hn
      have hu13 : 13 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-13),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_eight_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
