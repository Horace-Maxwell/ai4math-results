import Research.Backfill.Paper7.MomentB6EightSupport

/-! Source-only candidates for the original complete Z=9 slice.  Every original
catalog entry, all six ordered coordinates, Q=0/1, and the original q-fibre
weight are retained.  This module proves an analytic reduction; it does not
claim that the remaining weighted finite sum has been evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6FeatureCatalog_m4_le_138 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hM : sm.2 ≤ 138) : sm = (9,72) ∨ sm = (13,84) ∨ sm = (17,96) := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_le_138

def b6NineMomentGuard (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  (Q = 0 ∧ (∑ i, (z i : ℤ)^2) = 45) ∨
    (2 ≤ Q ∧ (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 57)
#print axioms Paper7MomentCounts.b6NineMomentGuard

theorem b6_zq_accept_total_nine_iff (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 9) (hQ : Q ≤ 9) :
    b6ZQAccept z Q ↔ b6NineMomentGuard z Q := by
  have hZi : ((∑ i, z i : ℕ) : ℤ) = 9 := by exact_mod_cast hZ
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg Q
  have hmax : max (Q : ℤ) 2 ≤ (Q : ℤ) + 2 := max_le (by omega) (by omega)
  have hu := b6_zq_theta_upper z Q (by omega)
  rw [hZi] at hu
  constructor
  · intro hg
    obtain ⟨sm,hsm,hM,hS,hload⟩ := hg.2.2
    have h138 : sm.2 ≤ 138 := by nlinarith only [hu,hM,hZi]
    have hc := b6FeatureCatalog_m4_le_138 sm hsm h138
    rw [hZ] at hS hload
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hS hload
    rcases hc with rfl | rfl | rfl
    · norm_num only [Prod.fst] at hload
      omega
    · have hq : Q = 0 := by
        by_cases htwo : (2 : ℤ) ≤ (Q : ℤ)
        · rw [max_eq_left htwo] at hload
          norm_num only [Prod.fst] at hload
          omega
        · rw [max_eq_right (by omega : (Q : ℤ) ≤ 2)] at hload
          norm_num only [Prod.fst] at hload
          omega
      refine Or.inl ⟨hq,?_⟩
      rw [hq] at hM
      norm_num only [Prod.snd,Nat.cast_zero,mul_zero,add_zero] at hM
      nlinarith only [hM,hZi]
    · refine Or.inr ⟨?_,?_⟩
      · norm_num only [Prod.fst] at hS
        exact_mod_cast (show (2 : ℤ) ≤ (Q : ℤ) by omega)
      · norm_num only [Prod.snd] at hM
        nlinarith only [hM,hZi]
  · intro hg
    refine ⟨by omega,by omega,?_⟩
    rcases hg with ⟨rfl,he⟩ | ⟨htwo,he⟩
    · refine ⟨(13,84),by norm_num [b6FeatureCatalog],?_,?_,?_⟩
      · norm_num only [Prod.snd,Nat.cast_zero,mul_zero,add_zero]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num
      · rw [hZ]
        norm_num
    · have htwoI : (2 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast htwo
      refine ⟨(17,96),by norm_num [b6FeatureCatalog],?_,?_,?_⟩
      · norm_num only [Prod.snd]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
      · rw [hZ,max_eq_left htwoI]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
#print axioms Paper7MomentCounts.b6_zq_accept_total_nine_iff

theorem b6_nine_guard_square_bounds (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) :
    39 ≤ (∑ i, (z i : ℤ)^2) ∧ (∑ i, (z i : ℤ)^2) ≤ 57 := by
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg Q
  have hQ9 : (Q : ℤ) ≤ 9 := by exact_mod_cast hQ
  rcases hg with ⟨_hq,he⟩ | ⟨_htwo,he⟩ <;> constructor <;> omega
#print axioms Paper7MomentCounts.b6_nine_guard_square_bounds

theorem b6_nine_guard_has_large_coordinate (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 9) (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) :
    ∃ i, 5 ≤ z i := by
  by_contra hn
  have hc : ∀ i, z i ≤ 4 := by
    intro i
    have hni : ¬ 5 ≤ z i := fun h => hn ⟨i,h⟩
    omega
  have hterm (i : Fin 6) : (z i : ℤ)^2 ≤ 4*(z i : ℤ) := by
    have h0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
    have h4 : (z i : ℤ) ≤ 4 := by exact_mod_cast hc i
    nlinarith only [h0,h4]
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
  have hZi : (∑ i, (z i : ℤ)) = 9 := by exact_mod_cast hZ
  rw [← Finset.mul_sum,hZi] at hs
  have hlo := (b6_nine_guard_square_bounds z Q hQ hg).1
  omega
#print axioms Paper7MomentCounts.b6_nine_guard_has_large_coordinate

theorem b6_nine_guard_coordinate_le_seven (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) (i : Fin 6) : z i ≤ 7 := by
  have hb := (b6_nine_guard_square_bounds z Q hQ hg).2
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 6)))
    (f := fun k => (z k : ℤ)^2) (fun k _ => sq_nonneg (z k : ℤ)) (Finset.mem_univ i)
  have hi0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
  have hi7 : (z i : ℤ) ≤ 7 := by nlinarith only [hb,hs,hi0]
  exact_mod_cast hi7
#print axioms Paper7MomentCounts.b6_nine_guard_coordinate_le_seven

theorem b6_total_nine_large_coordinate_unique (z : Fin 6 → ℕ)
    (hZ : (∑ k, z k) = 9) (i j : Fin 6) (hi : 5 ≤ z i) (hj : 5 ≤ z j) : i = j := by
  by_contra hne
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hjm : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_univ j⟩
  have hs := Finset.single_le_sum (s := Finset.univ.erase i) (f := z)
    (fun _ _ => Nat.zero_le _) hjm
  omega
#print axioms Paper7MomentCounts.b6_total_nine_large_coordinate_unique

theorem b6_nine_guard_unique_dominant (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ k, z k) = 9) (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) :
    ∃! i, 5 ≤ z i ∧ z i ≤ 7 := by
  obtain ⟨i,hi⟩ := b6_nine_guard_has_large_coordinate z Q hZ hQ hg
  refine ⟨i,⟨hi,b6_nine_guard_coordinate_le_seven z Q hQ hg i⟩,?_⟩
  intro j hj
  exact b6_total_nine_large_coordinate_unique z hZ j i hj.1 hi
#print axioms Paper7MomentCounts.b6_nine_guard_unique_dominant

theorem b6_nine_dominant_remainder (z : Fin 6 → ℕ)
    (hZ : (∑ k, z k) = 9) (i : Fin 6) (hi : 5 ≤ z i) (hi7 : z i ≤ 7) :
    (∑ k ∈ Finset.univ.erase i, z k) = 9 - z i ∧
      2 ≤ (∑ k ∈ Finset.univ.erase i, z k) ∧
      (∑ k ∈ Finset.univ.erase i, z k) ≤ 4 ∧
      ∀ k, k ≠ i → z k ≤ 4 := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  refine ⟨by omega,by omega,by omega,?_⟩
  intro k hki
  have hm : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
  have hb := Finset.single_le_sum (s := Finset.univ.erase i) (f := z)
    (fun _ _ => Nat.zero_le _) hm
  omega
#print axioms Paper7MomentCounts.b6_nine_dominant_remainder

theorem b6_nine_guard_at_dominant_iff (z : Fin 6 → ℕ) (Q : ℕ) (i : Fin 6) :
    b6NineMomentGuard z Q ↔
      (Q = 0 ∧ (z i : ℤ)^2 + (∑ k ∈ Finset.univ.erase i, (z k : ℤ)^2) = 45) ∨
      (2 ≤ Q ∧ (z i : ℤ)^2 + (∑ k ∈ Finset.univ.erase i, (z k : ℤ)^2) + 2*(Q : ℤ) = 57) := by
  have he := Finset.sum_erase_add Finset.univ (fun k => (z k : ℤ)^2) (Finset.mem_univ i)
  have hs : (∑ k, (z k : ℤ)^2) = (z i : ℤ)^2 + (∑ k ∈ Finset.univ.erase i, (z k : ℤ)^2) := by
    omega
  unfold b6NineMomentGuard
  rw [hs]
#print axioms Paper7MomentCounts.b6_nine_guard_at_dominant_iff

theorem b6_nine_nonzero_block_full_reduction (r : B6ZQIndex)
    (htag : b6TotalZTag r = (9 : Fin 37)) (hne : b6ZQBlock r ≠ 0) :
    r.2.val ≤ 9 ∧ b6NineMomentGuard r.1.val r.2.val ∧
      ∃! i, 5 ≤ r.1.val i ∧ r.1.val i ≤ 7 := by
  have hZ : (∑ i, r.1.val i) = 9 := congrArg Fin.val htag
  have hQ : r.2.val ≤ 9 := by
    by_contra hn
    exact hne (b6ZQBlock_zero_of_Q_above_capacity r (by omega))
  have ha : b6ZQAccept r.1.val r.2.val := by
    by_contra hn
    exact hne (ite_eq_right hn)
  have hg := (b6_zq_accept_total_nine_iff _ _ hZ hQ).mp ha
  exact ⟨hQ,hg,b6_nine_guard_unique_dominant _ _ hZ hQ hg⟩
#print axioms Paper7MomentCounts.b6_nine_nonzero_block_full_reduction

end Paper7MomentCounts
