import Research.Backfill.Paper7.MomentB6LabelledLowZ

/-! Source-only route by /root/moment_b6_recovery_1530.
The complete original Z=7 slice is reduced analytically to its two possible
moment equations. The exact finite weighted certificate below is an obligation,
not an evaluated count. No mathematical enumeration or DP execution was used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6FeatureCatalog_m4_le_96 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hM : sm.2 ≤ 96) : sm = (9,72) ∨ sm = (13,84) ∨ sm = (17,96) := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_le_96

/-- Both equations retain all six ordered coordinates and original Q weights. -/
def b6SevenMomentGuard (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 51 ∨
    (4 ≤ Q ∧ (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 63)
#print axioms Paper7MomentCounts.b6SevenMomentGuard

theorem b6_zq_accept_total_seven_iff (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 7) (hQ : Q ≤ 7) :
    b6ZQAccept z Q ↔ b6SevenMomentGuard z Q := by
  have hZi : ((∑ i, z i : ℕ) : ℤ) = 7 := by exact_mod_cast hZ
  have hQi : (Q : ℤ) ≤ 7 := by exact_mod_cast hQ
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg Q
  have hmax : max (Q : ℤ) 2 ≤ (Q : ℤ) + 2 := max_le (by omega) (by omega)
  have hleft : (Q : ℤ) ≤ max (Q : ℤ) 2 := le_max_left _ _
  have htheta := b6_zq_theta_upper z Q (by omega)
  rw [hZi] at htheta
  constructor
  · intro hg
    obtain ⟨sm,hsm,hM,hS,hload⟩ := hg.2.2
    have hM96 : sm.2 ≤ 96 := by nlinarith only [htheta,hM,hZi]
    have hcases := b6FeatureCatalog_m4_le_96 sm hsm hM96
    rw [hZ] at hS hload
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hS hload
    rcases hcases with rfl | rfl | rfl
    · norm_num at hload
      omega
    · apply Or.inl
      norm_num only [Prod.snd] at hM
      nlinarith only [hM,hZi]
    · refine Or.inr ⟨?_, ?_⟩
      · norm_num only [Prod.fst] at hS
        exact_mod_cast (show (4 : ℤ) ≤ (Q : ℤ) by omega)
      · norm_num only [Prod.snd] at hM
        nlinarith only [hM,hZi]
  · intro hg
    refine ⟨by omega, by omega, ?_⟩
    rcases hg with he | ⟨hfour,he⟩
    · refine ⟨(13,84), by norm_num [b6FeatureCatalog], ?_, ?_, ?_⟩
      · norm_num only [Prod.snd]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num only [Prod.fst, Nat.cast_add, Nat.cast_ofNat]
        omega
      · rw [hZ]
        norm_num only [Prod.fst, Nat.cast_add, Nat.cast_ofNat]
        omega
    · have hfourI : (4 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hfour
      refine ⟨(17,96), by norm_num [b6FeatureCatalog], ?_, ?_, ?_⟩
      · norm_num only [Prod.snd]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num only [Prod.fst, Nat.cast_add, Nat.cast_ofNat]
        omega
      · rw [hZ]
        norm_num only [Prod.fst, Nat.cast_add, Nat.cast_ofNat]
        omega
#print axioms Paper7MomentCounts.b6_zq_accept_total_seven_iff

/-- The effective original domain has z_i,Q in0..7; no coordinate order is quotiented. -/
theorem b6_total_seven_coordinate_bound (z : Fin 6 → ℕ)
    (hZ : (∑ i, z i) = 7) (i : Fin 6) : z i ≤ 7 := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 6)))
    (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
#print axioms Paper7MomentCounts.b6_total_seven_coordinate_bound

def b6SevenReducedBlock (r : B6ZQIndex) : ℕ :=
  if r.2.val ≤ 7 then
    if b6SevenMomentGuard r.1.val r.2.val then
      Paper7MomentDP.boundedQDP 6 r.1.val r.2.val else 0
  else 0
#print axioms Paper7MomentCounts.b6SevenReducedBlock

theorem b6ZQBlock_eq_seven_reduced (r : B6ZQIndex)
    (hZ : (∑ i, r.1.val i) = 7) : b6ZQBlock r = b6SevenReducedBlock r := by
  by_cases hQ : r.2.val ≤ 7
  · unfold b6SevenReducedBlock b6ZQBlock
    rw [ite_eq_left hQ, b6_zq_accept_total_seven_iff r.1.val r.2.val hZ hQ]
  · rw [b6ZQBlock_zero_of_Q_above_capacity r (by omega)]
    exact (ite_eq_right hQ).symm
#print axioms Paper7MomentCounts.b6ZQBlock_eq_seven_reduced

theorem finite_tagged_sum_congr_on_fibre {α : Type} [Fintype α] {n : ℕ}
    (tag : α → Fin n) (f g : α → ℕ) (b : Fin n)
    (h : ∀ a, tag a = b → f a = g a) :
    (∑ a, if tag a = b then f a else 0) =
      ∑ a, if tag a = b then g a else 0 := by
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases he : tag a = b
  · rw [ite_eq_left he, ite_eq_left he, h a he]
  · rw [ite_eq_right he, ite_eq_right he]
#print axioms Paper7MomentCounts.finite_tagged_sum_congr_on_fibre

theorem b6_seven_block_eq_of_tag (r : B6ZQIndex)
    (he : b6TotalZTag r = (7 : Fin 37)) : b6ZQBlock r = b6SevenReducedBlock r :=
  b6ZQBlock_eq_seven_reduced r (congrArg Fin.val he)
#print axioms Paper7MomentCounts.b6_seven_block_eq_of_tag

def b6SevenExactWeightedSum : ℕ :=
  ∑ r : B6ZQIndex, if b6TotalZTag r = (7 : Fin 37) then b6SevenReducedBlock r else 0
#print axioms Paper7MomentCounts.b6SevenExactWeightedSum

theorem b6LabelledZSlice_seven_eq_exact_weighted_sum :
    b6LabelledZSlice 7 = b6SevenExactWeightedSum := by
  exact finite_tagged_sum_congr_on_fibre b6TotalZTag b6ZQBlock
    b6SevenReducedBlock 7 b6_seven_block_eq_of_tag
#print axioms Paper7MomentCounts.b6LabelledZSlice_seven_eq_exact_weighted_sum

/-- Future finite support and original-weight verification must prove this equation. -/
def B6SevenExactWeightedCertificate (n : ℕ) : Prop := b6SevenExactWeightedSum = n
#print axioms Paper7MomentCounts.B6SevenExactWeightedCertificate

theorem b6LabelledZSlice_seven_of_exact_weighted_certificate (n : ℕ)
    (h : B6SevenExactWeightedCertificate n) : b6LabelledZSlice 7 = n := by
  exact b6LabelledZSlice_seven_eq_exact_weighted_sum.trans h
#print axioms Paper7MomentCounts.b6LabelledZSlice_seven_of_exact_weighted_certificate

end Paper7MomentCounts
