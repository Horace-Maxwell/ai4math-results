import Research.Backfill.Paper7.MomentB6LabelledZQSum

/-! Source-only candidate by /root/moment_t9_recovery_0906.
Complete original total-Z slices0 through6 vanish. The full21-entry catalog,
six ordered coordinates and genuine bounded-q weights are retained. The
imported ZQ partition/sum bridge is pending, not a successful producer yet. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6FeatureCatalog_m4_lower (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    72 ≤ sm.2 := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_lower

theorem b6FeatureCatalog_m4_le_78 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hM : sm.2 ≤ 78) : sm.1 = 9 := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_le_78

/-- The original theta is bounded by concentrating all z mass in one coordinate. -/
theorem b6_zq_theta_upper (z : Fin 6 → ℕ) (Q : ℕ) (hQ : Q ≤ ∑ i, z i) :
    12 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) + ∑ i, (z i : ℤ)^2 ≤
      12 + 5*((∑ i, z i : ℕ) : ℤ) + ((∑ i, z i : ℕ) : ℤ)^2 := by
  have hsq : (∑ i, (z i : ℤ)^2) ≤ ((∑ i, z i : ℕ) : ℤ)^2 := by
    simpa only [Nat.cast_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin 6)))
        (f := fun i => (z i : ℤ)) (fun i _ => Int.natCast_nonneg (z i)))
  have hQi : (Q : ℤ) ≤ ((∑ i, z i : ℕ) : ℤ) := by exact_mod_cast hQ
  nlinarith only [hsq,hQi]
#print axioms Paper7MomentCounts.b6_zq_theta_upper

theorem b6ZQBlock_zero_total_le_five (r : B6ZQIndex)
    (hZ : (∑ i, r.1.val i) ≤ 5) : b6ZQBlock r = 0 := by
  by_cases hQ : (∑ i, r.1.val i) < r.2.val
  · exact b6ZQBlock_zero_of_Q_above_capacity r hQ
  · have ha : ¬ b6ZQAccept r.1.val r.2.val := by
      intro hg
      obtain ⟨sm,hsm,hM,_hS,_hload⟩ := hg.2.2
      have hlow := b6FeatureCatalog_m4_lower sm hsm
      have hu := b6_zq_theta_upper r.1.val r.2.val (Nat.le_of_not_gt hQ)
      have hz0 : (0 : ℤ) ≤ ((∑ i, r.1.val i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hz5 : ((∑ i, r.1.val i : ℕ) : ℤ) ≤ 5 := by exact_mod_cast hZ
      have hprod := mul_nonneg (sub_nonneg.mpr hz5)
        (add_nonneg (show (0 : ℤ) ≤ 5 by norm_num) hz0)
      nlinarith only [hlow,hM,hu,hz5,hprod]
    exact ite_eq_right ha
#print axioms Paper7MomentCounts.b6ZQBlock_zero_total_le_five

theorem finite_tagged_sum_zero_of_property {α : Type} [Fintype α] {n : ℕ}
    (tag : α → Fin n) (weight : α → ℕ) (P : ℕ → Prop) (b : Fin n)
    (hb : P b.val) (h : ∀ a, P (tag a).val → weight a = 0) :
    (∑ a, if tag a = b then weight a else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a _ha
  by_cases he : tag a = b
  · rw [ite_eq_left he]
    exact h a (by rw [he]; exact hb)
  · exact ite_eq_right he
#print axioms Paper7MomentCounts.finite_tagged_sum_zero_of_property

theorem b6LabelledZSlice_zero_le_five (Z : Fin 37) (hZ : Z.val ≤ 5) :
    b6LabelledZSlice Z = 0 := by
  exact finite_tagged_sum_zero_of_property b6TotalZTag b6ZQBlock
    (fun n => n ≤ 5) Z hZ b6ZQBlock_zero_total_le_five
#print axioms Paper7MomentCounts.b6LabelledZSlice_zero_le_five

/-- The full requested Z=0 layer, with all Q and all six coordinates. -/
theorem b6LabelledZSlice_zero : b6LabelledZSlice 0 = 0 :=
  b6LabelledZSlice_zero_le_five 0 (by decide)
#print axioms Paper7MomentCounts.b6LabelledZSlice_zero

theorem b6ZQBlock_zero_total_six (r : B6ZQIndex)
    (hZ : (∑ i, r.1.val i) = 6) : b6ZQBlock r = 0 := by
  by_cases hQ : (∑ i, r.1.val i) < r.2.val
  · exact b6ZQBlock_zero_of_Q_above_capacity r hQ
  · have ha : ¬ b6ZQAccept r.1.val r.2.val := by
      intro hg
      obtain ⟨sm,hsm,hM,_hS,hload⟩ := hg.2.2
      have hu := b6_zq_theta_upper r.1.val r.2.val (Nat.le_of_not_gt hQ)
      have hzi : ((∑ i, r.1.val i : ℕ) : ℤ) = 6 := by exact_mod_cast hZ
      have hm78 : sm.2 ≤ 78 := by nlinarith only [hu,hzi,hM]
      have hs9 := b6FeatureCatalog_m4_le_78 sm hsm hm78
      have hq0 : (0 : ℤ) ≤ (r.2.val : ℤ) := Int.natCast_nonneg _
      have hmax : max (r.2.val : ℤ) 2 ≤ (r.2.val : ℤ) + 2 :=
        max_le (by omega) (by omega)
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hload
      nlinarith only [hload,hs9,hzi,hmax]
    exact ite_eq_right ha
#print axioms Paper7MomentCounts.b6ZQBlock_zero_total_six

theorem b6LabelledZSlice_six_zero : b6LabelledZSlice 6 = 0 := by
  exact finite_tagged_sum_zero_of_property b6TotalZTag b6ZQBlock
    (fun n => n = 6) 6 rfl b6ZQBlock_zero_total_six
#print axioms Paper7MomentCounts.b6LabelledZSlice_six_zero

theorem b6LabelledZSlice_zero_le_six (Z : Fin 37) (hZ : Z.val ≤ 6) :
    b6LabelledZSlice Z = 0 := by
  by_cases h5 : Z.val ≤ 5
  · exact b6LabelledZSlice_zero_le_five Z h5
  · have he : Z = (6 : Fin 37) := Fin.ext (by omega)
    rw [he]
    exact b6LabelledZSlice_six_zero
#print axioms Paper7MomentCounts.b6LabelledZSlice_zero_le_six

end Paper7MomentCounts
