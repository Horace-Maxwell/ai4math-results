import Research.Backfill.Paper7.MomentB4Type112CatalogSum

/-! SOURCE ONLY. A whole original Type112 middle layer. Its accepted
endpoints are first bounded analytically; only the resulting Fin3 x Fin3
and original nineteen-member catalogue are used in the small certificate.
No value of the full Type112 count is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_catalog_between_372_580 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hlo : 372 ≤ M) (hhi : M ≤ 580) :
    (S = 34 ∧ M = 384) ∨ (S = 38 ∧ M = 396) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_between_372_580

theorem type112_twelve_endpoint_budget (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,12,u,Q)) Q.val) :
    z.val+u.val ≤ 2 := by
  have hb := type112_accept_budget z 12 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 13 := by
    omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,_hlo⟩
  have he : M = 372+3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+
      (u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hSupper : S ≤ 28+(z.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hQ := Int.natCast_nonneg Q.val
  have hMlo : 372 ≤ M := by
    nlinarith [sq_nonneg (z.val : ℤ),sq_nonneg (u.val : ℤ)]
  have hMhi : M ≤ 580 := by
    have hh := b4_type112_moment_upper z.val 12 u.val Q.val 13 hbudget
    norm_num at hh
    nlinarith [hh]
  have hcases := b4_catalog_between_372_580 S M hm hMlo hMhi
  have hzsq := Int.le_self_sq (z.val : ℤ)
  have husq := Int.le_self_sq (u.val : ℤ)
  have hs : (z.val : ℤ)+u.val ≤ 2 := by
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> nlinarith
  exact_mod_cast hs
#print axioms Paper7MomentCanonicalNumeric.type112_twelve_endpoint_budget

theorem type112_twelve_small_catalog_certificate :
    ∀ z u : Fin 3, ∀ sm ∈ b4FeatureCatalog,
      (z ≤ u ∧ b4Type112RecoveredGuard (z.val+u.val) 12 (u.val-z.val) sm) ↔
        (z = 0 ∧ u = 0 ∧ (sm = (34,384) ∨ sm = (38,396))) ∨
        (z = 0 ∧ u = 1 ∧ sm = (38,396)) ∨
        (z = 1 ∧ u = 1 ∧ sm = (38,396)) := by
  simp only [b4Type112RecoveredGuard,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_twelve_small_catalog_certificate

theorem type112_twelve_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 12 (u.val-z.val) sm) :
    (z = 0 ∧ u = 0 ∧ (sm = (34,384) ∨ sm = (38,396))) ∨
      (z = 0 ∧ u = 1 ∧ sm = (38,396)) ∨
      (z = 1 ∧ u = 1 ∧ sm = (38,396)) := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 12 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 12 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 12 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_twelve_endpoint_budget z u Q ha
  let z' : Fin 3 := ⟨z.val,by omega⟩
  let u' : Fin 3 := ⟨u.val,by omega⟩
  have hsmall := (type112_twelve_small_catalog_certificate z' u' sm hm).mp
    ⟨hzu,hg⟩
  rcases hsmall with ⟨hz, hu, hs⟩ | ⟨hz, hu, hs⟩ | ⟨hz, hu, hs⟩
  · exact Or.inl ⟨Fin.ext (congrArg (fun i : Fin 3 => i.val) hz), Fin.ext (congrArg (fun i : Fin 3 => i.val) hu), hs⟩
  · exact Or.inr (Or.inl ⟨Fin.ext (congrArg (fun i : Fin 3 => i.val) hz), Fin.ext (congrArg (fun i : Fin 3 => i.val) hu), hs⟩)
  · exact Or.inr (Or.inr ⟨Fin.ext (congrArg (fun i : Fin 3 => i.val) hz), Fin.ext (congrArg (fun i : Fin 3 => i.val) hu), hs⟩)
#print axioms Paper7MomentCanonicalNumeric.type112_twelve_recovered_support

end Paper7MomentCanonicalNumeric
