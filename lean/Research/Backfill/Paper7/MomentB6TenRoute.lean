import Research.Backfill.Paper7.MomentB6NineRoute

/-! Source-only minimal analytic route for the complete original Z=10 layer.
No Z9 numerical result or assumed table coverage is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6FeatureCatalog_m4_le_162 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hM : sm.2 ≤ 162) : sm = (9,72) ∨ sm = (13,84) ∨ sm = (17,96) := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_le_162

def b6TenMomentGuard (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  1 ≤ Q ∧ (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 54
#print axioms Paper7MomentCounts.b6TenMomentGuard

theorem b6_zq_accept_total_ten_iff (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 10) (hQ : Q ≤ 10) :
    b6ZQAccept z Q ↔ b6TenMomentGuard z Q := by
  have hZi : ((∑ i, z i : ℕ) : ℤ) = 10 := by exact_mod_cast hZ
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg Q
  have hmax : max (Q : ℤ) 2 ≤ (Q : ℤ) + 2 := max_le (by omega) (by omega)
  have hleft : (Q : ℤ) ≤ max (Q : ℤ) 2 := le_max_left _ _
  have hu := b6_zq_theta_upper z Q (by omega)
  rw [hZi] at hu
  constructor
  · intro hg
    obtain ⟨sm,hsm,hM,hS,hload⟩ := hg.2.2
    have hm : sm.2 ≤ 162 := by nlinarith only [hu,hM,hZi]
    have hc := b6FeatureCatalog_m4_le_162 sm hsm hm
    rw [hZ] at hS hload
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hS hload
    rcases hc with rfl | rfl | rfl
    · norm_num only [Prod.fst] at hload
      omega
    · norm_num only [Prod.fst] at hload
      omega
    · constructor
      · norm_num only [Prod.fst] at hS
        exact_mod_cast (show (1 : ℤ) ≤ (Q : ℤ) by omega)
      · norm_num only [Prod.snd] at hM
        nlinarith only [hM,hZi]
  · rintro ⟨hpos,he⟩
    have hposI : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hpos
    refine ⟨by omega,by omega,(17,96),by norm_num [b6FeatureCatalog],?_,?_,?_⟩
    · norm_num only [Prod.snd]
      nlinarith only [he,hZi]
    · rw [hZ]
      norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
      omega
    · rw [hZ]
      norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
      omega
#print axioms Paper7MomentCounts.b6_zq_accept_total_ten_iff

theorem b6_ten_guard_square_bounds (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ 10) (hg : b6TenMomentGuard z Q) :
    34 ≤ (∑ i, (z i : ℤ)^2) ∧ (∑ i, (z i : ℤ)^2) ≤ 52 := by
  have hQ1 : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hg.1
  have hQ10 : (Q : ℤ) ≤ 10 := by exact_mod_cast hQ
  have he := hg.2
  constructor <;> omega
#print axioms Paper7MomentCounts.b6_ten_guard_square_bounds

theorem b6_ten_guard_has_large_coordinate (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 10) (hQ : Q ≤ 10) (hg : b6TenMomentGuard z Q) :
    ∃ i, 4 ≤ z i := by
  by_contra hn
  have hc : ∀ i, z i ≤ 3 := by
    intro i
    have hni : ¬ 4 ≤ z i := fun h => hn ⟨i,h⟩
    omega
  have hterm (i : Fin 6) : (z i : ℤ)^2 ≤ 3*(z i : ℤ) := by
    have h0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
    have h3 : (z i : ℤ) ≤ 3 := by exact_mod_cast hc i
    nlinarith only [h0,h3]
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
  have hZi : (∑ i, (z i : ℤ)) = 10 := by exact_mod_cast hZ
  rw [← Finset.mul_sum,hZi] at hs
  have hlo := (b6_ten_guard_square_bounds z Q hQ hg).1
  omega
#print axioms Paper7MomentCounts.b6_ten_guard_has_large_coordinate

theorem b6_ten_guard_coordinate_le_seven (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ 10) (hg : b6TenMomentGuard z Q) (i : Fin 6) : z i ≤ 7 := by
  have hb := (b6_ten_guard_square_bounds z Q hQ hg).2
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 6)))
    (f := fun k => (z k : ℤ)^2) (fun k _ => sq_nonneg (z k : ℤ)) (Finset.mem_univ i)
  have hi0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
  have hi7 : (z i : ℤ) ≤ 7 := by nlinarith only [hb,hs,hi0]
  exact_mod_cast hi7
#print axioms Paper7MomentCounts.b6_ten_guard_coordinate_le_seven

theorem b6_ten_large_coordinate_remainder (z : Fin 6 → ℕ)
    (hZ : (∑ k, z k) = 10) (i : Fin 6) (hi : 4 ≤ z i) (hi7 : z i ≤ 7) :
    (∑ k ∈ Finset.univ.erase i, z k) = 10 - z i ∧
      3 ≤ (∑ k ∈ Finset.univ.erase i, z k) ∧
      (∑ k ∈ Finset.univ.erase i, z k) ≤ 6 := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  exact ⟨by omega,by omega,by omega⟩
#print axioms Paper7MomentCounts.b6_ten_large_coordinate_remainder

theorem b6_ten_zero_Q_rejected (z : Fin 6 → ℕ) (hZ : (∑ i, z i) = 10) :
    ¬ b6ZQAccept z 0 := by
  rw [b6_zq_accept_total_ten_iff z 0 hZ (by decide)]
  simp [b6TenMomentGuard]
#print axioms Paper7MomentCounts.b6_ten_zero_Q_rejected

theorem b6_ten_nonzero_block_full_reduction (r : B6ZQIndex)
    (htag : b6TotalZTag r = (10 : Fin 37)) (hne : b6ZQBlock r ≠ 0) :
    1 ≤ r.2.val ∧ r.2.val ≤ 10 ∧
      (∑ i, (r.1.val i : ℤ)^2) + 2*(r.2.val : ℤ) = 54 ∧
      ∃ i, 4 ≤ r.1.val i ∧ r.1.val i ≤ 7 := by
  have hZ : (∑ i, r.1.val i) = 10 := congrArg Fin.val htag
  have hQ : r.2.val ≤ 10 := by
    by_contra hn
    exact hne (b6ZQBlock_zero_of_Q_above_capacity r (by omega))
  have ha : b6ZQAccept r.1.val r.2.val := by
    by_contra hn
    exact hne (ite_eq_right hn)
  have hg := (b6_zq_accept_total_ten_iff _ _ hZ hQ).mp ha
  obtain ⟨i,hi⟩ := b6_ten_guard_has_large_coordinate _ _ hZ hQ hg
  exact ⟨hg.1,hQ,hg.2,i,hi,b6_ten_guard_coordinate_le_seven _ _ hQ hg i⟩
#print axioms Paper7MomentCounts.b6_ten_nonzero_block_full_reduction

end Paper7MomentCounts
