import Research.Backfill.Paper7.MomentB4FixedTypeGuardSlices

/-! Source-only analytic rejection of whole fixed-type strips. The only
closed catalogue certificate is the gap between fourth moments 684 and 840.
No Type22/Type112 total, external table or candidate coverage is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_catalog_gap_684_840 :
    ∀ sm ∈ b4FeatureCatalog, sm.2 ≤ 684 ∨ 840 ≤ sm.2 := by
  norm_num [b4FeatureCatalog]
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_gap_684_840

theorem type22_accept_left_lt_seventeen (z t : Fin 19) (R : Fin 10)
    (ha : type22Accept (z,t,R)) : z.val < 17 := by
  by_contra h
  have hz : 17 ≤ z.val := by omega
  have hb := type22_accept_budget z t R ha
  have hz18 : z.val ≤ 18 := by omega
  have ht1 : t.val ≤ 1 := by omega
  have hR1 : R.val ≤ 1 := by omega
  have hzlo : (17 : ℤ) ≤ z.val := by exact_mod_cast hz
  have hzhi : (z.val : ℤ) ≤ 18 := by exact_mod_cast hz18
  have hthi : (t.val : ℤ) ≤ 1 := by exact_mod_cast ht1
  have hRhi : (R.val : ℤ) ≤ 1 := by exact_mod_cast hR1
  have hzsqlo : (17 : ℤ)^2 ≤ (z.val : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hz 2
  have hzsqhi : (z.val : ℤ)^2 ≤ (18 : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hz18 2
  have htsqhi : (t.val : ℤ)^2 ≤ (1 : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left ht1 2
  have ht0 := Int.natCast_nonneg t.val
  have hR0 := Int.natCast_nonneg R.val
  rcases ha with ⟨_hQ,_hp,_hn,sm,hm,heq,_hlo,_hhi⟩
  have hgap := b4_catalog_gap_684_840 sm hm
  norm_num [b4Theta,type22Row,Fin.sum_univ_four] at heq
  rcases hgap with hlow | hhigh
  · nlinarith [sq_nonneg (t.val : ℤ)]
  · nlinarith
#print axioms Paper7MomentCanonicalNumeric.type22_accept_left_lt_seventeen

theorem type112_accept_middle_lt_seventeen
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) : t.val < 17 := by
  by_contra h
  have ht : 17 ≤ t.val := by omega
  have hb := type112_accept_budget z t u Q ha
  have ht18 : t.val ≤ 18 := by have := t.isLt; omega
  have hz3 : z.val ≤ 3 := by omega
  have hu3 : u.val ≤ 3 := by omega
  have hQ3 : Q.val ≤ 3 := by omega
  have htlo : (17 : ℤ) ≤ t.val := by exact_mod_cast ht
  have hthi : (t.val : ℤ) ≤ 18 := by exact_mod_cast ht18
  have hzhi : (z.val : ℤ) ≤ 3 := by exact_mod_cast hz3
  have huhi : (u.val : ℤ) ≤ 3 := by exact_mod_cast hu3
  have hQhi : (Q.val : ℤ) ≤ 3 := by exact_mod_cast hQ3
  have htsqlo : (17 : ℤ)^2 ≤ (t.val : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left ht 2
  have htsqhi : (t.val : ℤ)^2 ≤ (18 : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left ht18 2
  have hzsqhi : (z.val : ℤ)^2 ≤ (3 : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hz3 2
  have husqhi : (u.val : ℤ)^2 ≤ (3 : ℤ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hu3 2
  have hz0 := Int.natCast_nonneg z.val
  have hu0 := Int.natCast_nonneg u.val
  have hQ0 := Int.natCast_nonneg Q.val
  rcases ha with ⟨_hQ,_hp,_hn,sm,hm,heq,_hlo,_hhi⟩
  have hgap := b4_catalog_gap_684_840 sm hm
  norm_num [b4Theta,type112Row,Fin.sum_univ_four] at heq
  rcases hgap with hlow | hhigh
  · nlinarith [sq_nonneg (z.val : ℤ),sq_nonneg (u.val : ℤ)]
  · nlinarith
#print axioms Paper7MomentCanonicalNumeric.type112_accept_middle_lt_seventeen

theorem b4_type22_block_zero_of_left_ge_seventeen (z t : Fin 19)
    (hz : 17 ≤ z.val) : b4Type22Block z t = 0 := by
  unfold b4Type22Block
  apply Finset.sum_eq_zero
  intro R _
  have ha : ¬ type22Accept (z,t,R) := by
    intro h
    have := type22_accept_left_lt_seventeen z t R h
    omega
  exact ite_eq_right ha
#print axioms Paper7MomentCanonicalNumeric.b4_type22_block_zero_of_left_ge_seventeen

theorem b4_type112_block_zero_of_middle_ge_seventeen
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (ht : 17 ≤ t.val) :
    b4Type112Block z t u = 0 := by
  unfold b4Type112Block
  apply Finset.sum_eq_zero
  intro Q _
  have ha : ¬ B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val := by
    intro h
    have := type112_accept_middle_lt_seventeen z t u Q h
    omega
  exact ite_eq_right ha
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_zero_of_middle_ge_seventeen

theorem b4_type22_finite_sum_eq_short_budget_slices :
    b4Type22FiniteSum =
      ∑ z ∈ (Finset.univ : Finset (Fin 19)).filter (fun z => z.val < 17),
        ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => z.val+t.val ≤ 18),
          b4Type22Block z t := by
  rw [b4_type22_finite_sum_eq_budget_slices,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.val < 17
  · exact (ite_eq_left hz).symm
  · have hzero : ∀ t : Fin 19, b4Type22Block z t = 0 := fun t =>
      b4_type22_block_zero_of_left_ge_seventeen z t (by omega)
    rw [ite_eq_right hz]
    exact Finset.sum_eq_zero (fun t _ => hzero t)
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_short_budget_slices

theorem b4_type112_finite_sum_eq_short_middle_budget_slices :
    b4Type112FiniteSum = ∑ z : Fin 38,
      ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 17),
        ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
          (fun u => z.val+2*t.val+u.val ≤ 37), b4Type112Block z t u := by
  rw [b4_type112_finite_sum_eq_budget_slices]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t.val < 17
  · exact (ite_eq_left ht).symm
  · have hzero : ∀ u : Fin 38, b4Type112Block z t u = 0 := fun u =>
      b4_type112_block_zero_of_middle_ge_seventeen z t u (by omega)
    rw [ite_eq_right ht]
    exact Finset.sum_eq_zero (fun u _ => hzero u)
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_short_middle_budget_slices

end Paper7MomentCanonicalNumeric
