import Research.Backfill.Paper7.MomentB4Type112CatalogSum

/-! SOURCE ONLY. A general endpoint quadratic inequality and the entire
original t=11 layer. No t=12 candidate or full-count value is assumed.
The small certificate retains every member of the original catalogue. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

theorem type112_accept_catalog_endpoint_quadratic_bound
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) :
    ∃ sm ∈ b4FeatureCatalog,
      sm.2 = 12+6*(t.val : ℤ)+3*((z.val : ℤ)+u.val)+2*(t.val : ℤ)^2+
        (z.val : ℤ)^2+(u.val : ℤ)^2+2*(Q.val : ℤ) ∧
      (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val+
        4+2*(t.val : ℤ)+2*(t.val : ℤ)^2+2*sm.1 ≤ sm.2 := by
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,hM,hS,_hlo⟩
  have he : M = 12+6*(t.val : ℤ)+3*((z.val : ℤ)+u.val)+2*(t.val : ℤ)^2+
      (z.val : ℤ)^2+(u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at hM
    nlinarith [hM]
  have hu : S ≤ 4+(z.val : ℤ)+2*(t.val : ℤ)+u.val+Q.val := by
    norm_num [type112Row,Fin.sum_univ_four] at hS
    linarith
  refine ⟨(S,M),hm,he,?_⟩
  dsimp only [Prod.fst,Prod.snd]
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_accept_catalog_endpoint_quadratic_bound

theorem b4_catalog_between_320_590 (S M : ℤ) (hm : (S,M) ∈ b4FeatureCatalog)
    (hlo : 320 ≤ M) (hhi : M ≤ 590) :
    (S = 29 ∧ M = 324) ∨ (S = 33 ∧ M = 336) ∨
      (S = 34 ∧ M = 384) ∨ (S = 38 ∧ M = 396) := by
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_between_320_590

theorem type112_eleven_endpoint_bound (z u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,11,u,Q)) Q.val) :
    z.val ≤ 6 ∧ u.val ≤ 6 := by
  have hb := type112_accept_budget z 11 u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 15 := by
    omega
  obtain ⟨⟨S,M⟩,hm,he,hquad⟩ :=
    type112_accept_catalog_endpoint_quadratic_bound z 11 u Q ha
  dsimp only [Prod.fst,Prod.snd] at he hquad
  norm_num at he hquad
  have hz := Int.natCast_nonneg z.val
  have hu := Int.natCast_nonneg u.val
  have hQ := Int.natCast_nonneg Q.val
  have hMlo : 320 ≤ M := by
    nlinarith [sq_nonneg (z.val : ℤ),sq_nonneg (u.val : ℤ)]
  have hMhi : M ≤ 590 := by
    have hh := b4_type112_moment_upper z.val 11 u.val Q.val 15 hbudget
    norm_num at hh
    nlinarith [hh]
  have hcases := b4_catalog_between_320_590 S M hm hMlo hMhi
  have hsum : (z.val : ℤ)^2+z.val+(u.val : ℤ)^2+u.val ≤ 52 := by
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      nlinarith
  constructor
  · have hh : (z.val : ℤ) ≤ 6 := by
      by_contra hn
      have h7 : 7 ≤ (z.val : ℤ) := by omega
      nlinarith [sq_nonneg ((z.val : ℤ)-7),sq_nonneg (u.val : ℤ)]
    exact_mod_cast hh
  · have hh : (u.val : ℤ) ≤ 6 := by
      by_contra hn
      have h7 : 7 ≤ (u.val : ℤ) := by omega
      nlinarith [sq_nonneg ((u.val : ℤ)-7),sq_nonneg (z.val : ℤ)]
    exact_mod_cast hh
#print axioms Paper7MomentCanonicalNumeric.type112_eleven_endpoint_bound

theorem type112_eleven_small_catalog_certificate :
    ∀ z u : Fin 7, ∀ sm ∈ b4FeatureCatalog,
      (z ≤ u ∧ b4Type112RecoveredGuard (z.val+u.val) 11 (u.val-z.val) sm) ↔
        (sm = (33,336) ∧ ((z = 0 ∧ u = 0) ∨ (z = 0 ∧ u = 1))) ∨
        (sm = (34,384) ∧ ((z = 0 ∧ u = 6) ∨ (z = 1 ∧ u = 6) ∨
          (z = 2 ∧ u = 5) ∨ (z = 2 ∧ u = 6) ∨ (z = 3 ∧ u = 5) ∨
          (z = 4 ∧ u = 4))) ∨
        (sm = (38,396) ∧ ((z = 2 ∧ u = 6) ∨ (z = 4 ∧ u = 5))) := by
  intro z u ⟨S, M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl, rfl⟩
  all_goals
    revert z u
    simp only [b4Type112RecoveredGuard, b4Type112RecoveredQ,
      b4Type112CatalogResidual, b4Type112DoubleBase]
    decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_eleven_small_catalog_certificate

theorem type112_eleven_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 11 (u.val-z.val) sm) :
    (sm = (33,336) ∧ ((z = 0 ∧ u = 0) ∨ (z = 0 ∧ u = 1))) ∨
      (sm = (34,384) ∧ ((z = 0 ∧ u = 6) ∨ (z = 1 ∧ u = 6) ∨
        (z = 2 ∧ u = 5) ∨ (z = 2 ∧ u = 6) ∨ (z = 3 ∧ u = 5) ∨
        (z = 4 ∧ u = 4))) ∨
      (sm = (38,396) ∧ ((z = 2 ∧ u = 6) ∨ (z = 4 ∧ u = 5))) := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 11 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 11 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 11 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_eleven_endpoint_bound z u Q ha
  let z' : Fin 7 := ⟨z.val,by omega⟩
  let u' : Fin 7 := ⟨u.val,by omega⟩
  have hsmall := (type112_eleven_small_catalog_certificate z' u' sm hm).mp
    ⟨hzu,hg⟩
  rcases hsmall with ⟨hs, hp⟩ | ⟨hs, hp⟩ | ⟨hs, hp⟩
  · refine Or.inl ⟨hs, ?_⟩
    rcases hp with ⟨hz, hu⟩ | ⟨hz, hu⟩
    · exact Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩
    · exact Or.inr ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩
  · refine Or.inr (Or.inl ⟨hs, ?_⟩)
    rcases hp with ⟨hz, hu⟩ | ⟨hz, hu⟩ | ⟨hz, hu⟩ | ⟨hz, hu⟩ | ⟨hz, hu⟩ | ⟨hz, hu⟩
    · exact Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩
    · exact Or.inr (Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩))))
  · refine Or.inr (Or.inr ⟨hs, ?_⟩)
    rcases hp with ⟨hz, hu⟩ | ⟨hz, hu⟩
    · exact Or.inl ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩
    · exact Or.inr ⟨Fin.ext (congrArg (fun i : Fin 7 => i.val) hz), Fin.ext (congrArg (fun i : Fin 7 => i.val) hu)⟩
#print axioms Paper7MomentCanonicalNumeric.type112_eleven_recovered_support

end Paper7MomentCanonicalNumeric
