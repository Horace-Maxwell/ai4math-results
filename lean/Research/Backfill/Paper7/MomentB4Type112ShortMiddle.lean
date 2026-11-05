import Research.Backfill.Paper7.MomentB4FixedTypeTriangleSlices

/-! SOURCE ONLY. Whole middle layers 13 through 16 are excluded by an
analytic moment bound and the exact nineteen-pair catalogue. Combined with
the already proved layers 17 and 18, only middle parameters 0 through 12
remain. This does not evaluate the remaining sum or assume its value. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_catalog_degree_lower (z : Fin 38) (t : Fin 19)
    (u : Fin 38) (Q : Fin 19) (S : ℤ)
    (hlo : (4+((∑ i, type112Row (z,t,u,Q) i)+Q.val : ℕ) : ℤ) -
      max (Q.val : ℤ) 2 ≤ S) :
    2+(z.val : ℤ)+2*t.val+u.val ≤ S := by
  have hm : max (Q.val : ℤ) 2 ≤ (Q.val : ℤ)+2 := by
    apply max_le
    · omega
    · exact le_add_of_nonneg_left (Int.natCast_nonneg _)
  norm_num [type112Row,Fin.sum_univ_four] at hlo
  linarith
#print axioms Paper7MomentCanonicalNumeric.type112_catalog_degree_lower

theorem b4_type112_moment_upper (z t u Q K : ℕ)
    (hbudget : z+u+Q ≤ K) :
    12+6*(t : ℤ)+2*(t : ℤ)^2+3*((z : ℤ)+u)+(z : ℤ)^2+(u : ℤ)^2+
        2*(Q : ℤ) ≤
      12+6*(t : ℤ)+2*(t : ℤ)^2+3*(K : ℤ)+(K : ℤ)^2 := by
  have hs : z+u ≤ K := by omega
  have hsq : ((z : ℤ)+u)^2 ≤ (K : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hs 2
  have hlin : (z : ℤ)+u+Q ≤ K := by exact_mod_cast hbudget
  have hprod : 0 ≤ (z : ℤ)*u :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hQ := Int.natCast_nonneg Q
  nlinarith
#print axioms Paper7MomentCanonicalNumeric.b4_type112_moment_upper

theorem b4_catalog_middle_thirteen_to_sixteen_excluded
    (t : ℕ) (S M : ℤ) (htlo : 13 ≤ t) (hthi : t ≤ 16)
    (hm : (S,M) ∈ b4FeatureCatalog)
    (hS : 2+2*(t : ℤ) ≤ S)
    (hMlo : 12+6*(t : ℤ)+2*(t : ℤ)^2 ≤ M)
    (hMhi : M ≤ 12+6*(t : ℤ)+2*(t : ℤ)^2+
      3*((37-2*t : ℕ) : ℤ)+((37-2*t : ℕ) : ℤ)^2) : False := by
  interval_cases t <;>
    norm_num [b4FeatureCatalog] at hm hS hMlo hMhi <;>
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
      hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> omega
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_middle_thirteen_to_sixteen_excluded

theorem type112_accept_middle_lt_thirteen
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) : t.val < 13 := by
  by_contra h
  have htlo : 13 ≤ t.val := by omega
  have hthi : t.val ≤ 16 := by
    have := type112_accept_middle_lt_seventeen z t u Q ha
    omega
  have hb := type112_accept_budget z t u Q ha
  have hbudget : z.val+u.val+Q.val ≤ 37-2*t.val := by omega
  rcases ha with ⟨_hQ,_hp,_hn,⟨S,M⟩,hm,heq,_hSupper,hSlower⟩
  have hSlow := type112_catalog_degree_lower z t u Q S hSlower
  have hS : 2+2*(t.val : ℤ) ≤ S := by
    have hz := Int.natCast_nonneg z.val
    have hu := Int.natCast_nonneg u.val
    linarith
  have he : M = 12+6*(t.val : ℤ)+2*(t.val : ℤ)^2+
      3*((z.val : ℤ)+u.val)+(z.val : ℤ)^2+(u.val : ℤ)^2+2*(Q.val : ℤ) := by
    norm_num [b4Theta,type112Row,Fin.sum_univ_four] at heq
    nlinarith [heq]
  have hMlo : 12+6*(t.val : ℤ)+2*(t.val : ℤ)^2 ≤ M := by
    have hz := Int.natCast_nonneg z.val
    have hu := Int.natCast_nonneg u.val
    have hQ := Int.natCast_nonneg Q.val
    nlinarith [sq_nonneg (z.val : ℤ),sq_nonneg (u.val : ℤ)]
  have hMhi : M ≤ 12+6*(t.val : ℤ)+2*(t.val : ℤ)^2+
      3*((37-2*t.val : ℕ) : ℤ)+((37-2*t.val : ℕ) : ℤ)^2 := by
    rw [he]
    exact b4_type112_moment_upper z.val t.val u.val Q.val (37-2*t.val) hbudget
  exact b4_catalog_middle_thirteen_to_sixteen_excluded t.val S M htlo hthi hm
    hS hMlo hMhi
#print axioms Paper7MomentCanonicalNumeric.type112_accept_middle_lt_thirteen

theorem b4_type112_block_zero_of_middle_ge_thirteen
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (ht : 13 ≤ t.val) :
    b4Type112Block z t u = 0 := by
  unfold b4Type112Block
  apply Finset.sum_eq_zero
  intro Q _
  have ha : ¬ B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val := by
    intro h
    have := type112_accept_middle_lt_thirteen z t u Q h
    omega
  exact ite_eq_right ha
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_zero_of_middle_ge_thirteen

theorem b4_type112_finite_sum_eq_thirteen_middle_slices :
    b4Type112FiniteSum =
      ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 13),
        ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u := by
  rw [b4_type112_finite_sum_eq_blocks,Finset.sum_comm,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t.val < 13
  · exact (ite_eq_left ht).symm
  · have hz (z u : Fin 38) : b4Type112Block z t u = 0 :=
        b4_type112_block_zero_of_middle_ge_thirteen z t u (by omega)
    rw [ite_eq_right ht]
    exact Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => hz z u))
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_thirteen_middle_slices

end Paper7MomentCanonicalNumeric
