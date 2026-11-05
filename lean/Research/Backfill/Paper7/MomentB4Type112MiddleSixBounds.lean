import Research.Backfill.Paper7.MomentB4Type112MiddleElevenSupport

/-! SOURCE ONLY. Original t=6 guard. A generic endpoint quadratic cap
can also be reused in lower layers, but no lower-layer value is assumed.
The only external import is bound to Root542's successful Support source. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_accept_catalog_quadratic_interval
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) :
    ∃ sm ∈ b4FeatureCatalog,
      sm.2-86 ≤ (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+
        2*(t.val : ℤ)^2+2*t.val ∧
      (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+
        2*(t.val : ℤ)^2+2*t.val ≤ sm.2-4-2*sm.1 := by
  have hb := type112_accept_budget z t u Q ha
  have hbudget : (z.val : ℤ)+2*(t.val : ℤ)+u.val+Q.val ≤ 37 := by
    exact_mod_cast hb
  obtain ⟨sm,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z t u Q ha
  refine ⟨sm,hm,?_,?_⟩ <;> nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_accept_catalog_quadratic_interval

theorem type112_endpoint_quadratic_sum_cap (z u a b : ℤ)
    (hz : 0 ≤ z) (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzb : z ≤ b) (hub : u ≤ b) (hs : z+u ≤ a+b) :
    z^2+z+u^2+u ≤ a^2+a+b^2+b := by
  by_cases hza : z ≤ a
  · have hpz : 0 ≤ (a-z)*(a+z+1) := mul_nonneg (by omega) (by omega)
    have hpu : 0 ≤ (b-u)*(b+u+1) := mul_nonneg (by omega) (by omega)
    nlinarith
  · by_cases hua : u ≤ a
    · have hpz : 0 ≤ (b-z)*(b+z+1) := mul_nonneg (by omega) (by omega)
      have hpu : 0 ≤ (a-u)*(a+u+1) := mul_nonneg (by omega) (by omega)
      nlinarith
    · have hpz : 0 ≤ (z-a)*(b-z) := mul_nonneg (by omega) (by omega)
      have hpu : 0 ≤ (u-a)*(b-u) := mul_nonneg (by omega) (by omega)
      have hpsum : 0 ≤ (a+b+1)*(a+b-z-u) := mul_nonneg (by omega) (by omega)
      nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_endpoint_quadratic_sum_cap

theorem type112_six_moment_upper_from_endpoint_bound (z u Q N : ℕ)
    (hbudget : z+u+Q ≤ 25) (hs : z+u ≤ N) :
    120+3*((z : ℤ)+u)+(z : ℤ)^2+(u : ℤ)^2+2*(Q : ℤ) ≤
      170+(N : ℤ)+(N : ℤ)^2 := by
  have hsq : ((z : ℤ)+u)^2 ≤ (N : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hs 2
  have hlin : (z : ℤ)+u+Q ≤ 25 := by exact_mod_cast hbudget
  have hsum : (z : ℤ)+u ≤ N := by exact_mod_cast hs
  have hprod : 0 ≤ (z : ℤ)*u :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_six_moment_upper_from_endpoint_bound

theorem b4_catalog_below_820 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hhi : M ≤ 820) :
    M ≤ 396 ∨ (S = 25 ∧ M = 600) ∨ (S = 29 ∧ M = 612) ∨
      (S = 33 ∧ M = 624) ∨ (S = 34 ∧ M = 672) ∨ (S = 38 ∧ M = 684) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_below_820

theorem type112_six_moment_upper (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,6,u,Q)) Q.val) :
    120+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+
      2*(Q.val : ℤ) ≤ 396 := by
  have hb := type112_accept_budget z 6 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 25 := by omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,hlo⟩
  have he : M = 120+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hd := type112_catalog_degree_lower z 6 u Q S hlo
  norm_num at hd
  have hupp : S ≤ 16+(z.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith
  have hquad : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+88+2*S ≤ M := by
    nlinarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hMhi : M ≤ 820 := by
    have hh := b4_type112_moment_upper z.val 6 u.val Q.val 25 hbudget
    norm_num at hh
    nlinarith [hh]
  have hMbound : M ≤ 396 := by
    rcases b4_catalog_below_820 S M hm hMhi with
      h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · have hs : z.val+u.val ≤ 11 := by
        have hh : (z.val : ℤ)+u.val ≤ 11 := by omega
        exact_mod_cast hh
      have hh := type112_six_moment_upper_from_endpoint_bound
        z.val u.val Q.val 11 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 15 := by
        have hh : (z.val : ℤ)+u.val ≤ 15 := by omega
        exact_mod_cast hh
      have hh := type112_six_moment_upper_from_endpoint_bound
        z.val u.val Q.val 15 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 19 := by
        have hh : (z.val : ℤ)+u.val ≤ 19 := by omega
        exact_mod_cast hh
      have hh := type112_six_moment_upper_from_endpoint_bound
        z.val u.val Q.val 19 hbudget hs
      nlinarith
    · have hs : z.val+u.val ≤ 20 := by
        have hh : (z.val : ℤ)+u.val ≤ 20 := by omega
        exact_mod_cast hh
      have hh := type112_six_moment_upper_from_endpoint_bound
        z.val u.val Q.val 20 hbudget hs
      nlinarith
    · have hzcap : (z.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (z.val : ℤ) := by omega
        nlinarith [sq_nonneg ((z.val : ℤ)-23),sq_nonneg (u.val : ℤ)]
      have hucap : (u.val : ℤ) ≤ 22 := by
        by_contra hn
        have hh : 23 ≤ (u.val : ℤ) := by omega
        nlinarith [sq_nonneg ((u.val : ℤ)-23),sq_nonneg (z.val : ℤ)]
      have hsmall := type112_endpoint_quadratic_sum_cap
        (z.val : ℤ) u.val 2 22 hz hu (by norm_num) (by norm_num)
        hzcap hucap (by omega)
      norm_num at hsmall
      have hlin : (z.val : ℤ)+u.val+Q.val ≤ 25 := by exact_mod_cast hbudget
      nlinarith
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_six_moment_upper

theorem type112_six_ordered_endpoint_bounds (z u : Fin 38) (Q : Fin 19)
    (hzu : z ≤ u) (ha : B4CatalogRowAccept (type112Row (z,6,u,Q)) Q.val) :
    z.val ≤ 10 ∧ u.val ≤ 14 := by
  have hmoment := type112_six_moment_upper z u Q ha
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 6 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hM : M ≤ 396 := by nlinarith
  have hcap : M-88-2*S ≤ 232 := by
    norm_num [b4FeatureCatalog] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      rcases hm with ⟨rfl,rfl⟩ <;> omega
  have hs : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 232 := by
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
  · have hh : (u.val : ℤ) ≤ 14 := by
      by_contra hn
      have hu15 : 15 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-15),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_six_ordered_endpoint_bounds

end Paper7MomentCanonicalNumeric
