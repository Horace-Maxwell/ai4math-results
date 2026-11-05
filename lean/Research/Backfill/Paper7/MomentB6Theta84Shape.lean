import Research.Backfill.Paper7.MomentB6NineShapes

/-! Source-only candidate for the original theta=84 fibre.
The original whole 21-pair catalogue, six ordered coordinates, positive
budget and genuine q-capacity are preserved.  Only successful parent shape
interfaces are reused; no catalogue completeness or proposed shape list is
assumed.  This module does not reconstruct PQ rows or count any fibre. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

/-- The original complete catalogue has just one pair with this theta. -/
theorem b6FeatureCatalog_theta84 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (ht : sm.2 = 84) : sm = (13,84) := by
  have hc := b6FeatureCatalog_m4_le_138 sm hsm (by omega)
  rcases hc with rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_theta84

/-- Full coordinate coverage comes from the original guard and the actual
successful seven/eight/nine shape proofs, not from layer totals. -/
theorem b6_theta84_complete_zq_shapes (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ ∑ i, z i) (hg : b6ZQAccept z Q)
    (ht : 12 + 3 * ((∑ i, z i : ℕ) : ℤ) + 2 * (Q : ℤ) +
      ∑ i, (z i : ℤ)^2 = 84) :
    (∃ i, z = b6SevenSingle i ∧ Q = 1) ∨
    (∃ i j, i ≠ j ∧ z = b6SevenDouble i j ∧ Q = 7) ∨
    (∃ i j, i ≠ j ∧ z = b6TwoPoint 6 3 i j ∧ Q = 0) := by
  have hload : (6 + ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ)) -
      max (Q : ℤ) 2 ≤ 13 := by
    obtain ⟨sm,hsm,hM,_hS,hl⟩ := hg.2.2
    have hs := b6FeatureCatalog_theta84 sm hsm (hM.trans ht)
    rw [hs] at hl
    simpa only [Prod.fst, Nat.cast_add, add_assoc] using hl
  have hlarge : 2 ≤ Q → (∑ i, z i) ≤ 7 := by
    intro htwo
    have htwoI : (2 : ℤ) ≤ Q := by exact_mod_cast htwo
    have hl := hload
    rw [max_eq_left htwoI] at hl
    have hz : ((∑ i, z i : ℕ) : ℤ) ≤ 7 := by omega
    exact_mod_cast hz
  have hsmall : Q ≤ 1 → (∑ i, z i) + Q ≤ 9 := by
    intro hone
    have honeI : (Q : ℤ) ≤ 2 := by exact_mod_cast (show Q ≤ 2 by omega)
    have hl := hload
    rw [max_eq_right honeI] at hl
    have hz : ((∑ i, z i : ℕ) : ℤ) + (Q : ℤ) ≤ 9 := by omega
    exact_mod_cast hz
  have hZ9 : (∑ i, z i) ≤ 9 := by
    by_cases htwo : 2 ≤ Q
    · have hz := hlarge htwo
      omega
    · have hz := hsmall (by omega)
      omega
  have hZ7 : 7 ≤ ∑ i, z i := by
    by_contra hn
    have hZ6 : (∑ i, z i) ≤ 6 := by omega
    have hu := b6_zq_theta_upper z Q hQ
    have hZ0 : (0 : ℤ) ≤ ((∑ i, z i : ℕ) : ℤ) := Int.natCast_nonneg _
    have hZ6I : ((∑ i, z i : ℕ) : ℤ) ≤ 6 := by exact_mod_cast hZ6
    have hp := mul_nonneg (sub_nonneg.mpr hZ6I)
      (add_nonneg (show (0 : ℤ) ≤ 6 by norm_num) hZ0)
    nlinarith only [hu, ht, hZ6I, hp]
  have hcases : (∑ i, z i) = 7 ∨ (∑ i, z i) = 8 ∨ (∑ i, z i) = 9 := by
    omega
  rcases hcases with hZ | hZ | hZ
  · have hQ7 : Q ≤ 7 := by omega
    have hseven := (b6_zq_accept_total_seven_iff z Q hZ hQ7).mp hg
    rcases b6_seven_guard_complete_shapes z Q hZ hQ7 hseven with
      ⟨i,hz,hq⟩ | ⟨i,j,hij,hz,hq⟩
    · rcases hq with hq | hq
      · exact Or.inl ⟨i,hz,hq⟩
      · rw [hz, hq, b6SevenSingle_sum, b6SevenSingle_sq_sum] at ht
        norm_num at ht
    · exact Or.inr (Or.inl ⟨i,j,hij,hz,hq⟩)
  · have hQ8 : Q ≤ 8 := by omega
    have height := (b6_zq_accept_total_eight_iff z Q hZ hQ8).mp hg
    obtain ⟨i,j,_hij,_hz,hq⟩ := b6_eight_guard_complete_shape z Q hZ hQ8 height
    have hz7 := hlarge (by omega : 2 ≤ Q)
    omega
  · have hQ9 : Q ≤ 9 := by omega
    have hq0 : Q = 0 := by
      by_cases htwo : 2 ≤ Q
      · have hz7 := hlarge htwo
        omega
      · have hz9 := hsmall (by omega)
        omega
    have hnine := (b6_zq_accept_total_nine_iff z Q hZ hQ9).mp hg
    rcases b6_nine_guard_complete_shapes z Q hZ hQ9 hnine with
      ⟨i,j,hij,hz,_hq⟩ | ⟨_,_,_,_,hq⟩ | ⟨_,_,_,_,_,hq⟩ |
      ⟨_,_,_,_,_,_,_,hq⟩ | ⟨_,_,_,_,_,hq⟩ | ⟨_,_,_,_,hq⟩
    · exact Or.inr (Or.inr ⟨i,j,hij,hz,hq0⟩)
    all_goals omega
#print axioms Paper7MomentCounts.b6_theta84_complete_zq_shapes

/-- Original PQ statement: q capacity and the ZQ guard are derived from the
actual coordinates and original acceptance predicate. -/
theorem b6_candidate_theta84_shapes (x : PQ 6) (hg : b6CandidateGuard x)
    (htheta : theta x = 84) :
    (∃ i, (fun k => x.1 k + x.2 k) = b6SevenSingle i ∧ qSum x = 1) ∨
    (∃ i j, i ≠ j ∧ (fun k => x.1 k + x.2 k) = b6SevenDouble i j ∧ qSum x = 7) ∨
    (∃ i j, i ≠ j ∧ (fun k => x.1 k + x.2 k) = b6TwoPoint 6 3 i j ∧ qSum x = 0) := by
  let z : Fin 6 → ℕ := fun i => x.1 i + x.2 i
  have hQ : qSum x ≤ ∑ i, z i := by
    change (∑ i, x.2 i) ≤ ∑ i, z i
    apply Finset.sum_le_sum
    intro i _hi
    dsimp only [z]
    omega
  have ha : b6ZQAccept z (qSum x) :=
    (b6_candB1_on_zq_fibre z (qSum x) x (fun _ => rfl) rfl).mp
      ((b6_candB1_iff_guard x).mpr hg)
  have ht := b6_zq_theta (pqToZQ x)
  have hback : zqToPQ (pqToZQ x) = x := (pqEquivZQ 6).left_inv x
  rw [hback, htheta] at ht
  change (84 : ℤ) = 12 + 3 * ((∑ i, z i : ℕ) : ℤ) + 2 * (qSum x : ℤ) +
    ∑ i, (z i : ℤ)^2 at ht
  exact b6_theta84_complete_zq_shapes z (qSum x) hQ ha ht.symm
#print axioms Paper7MomentCounts.b6_candidate_theta84_shapes

end Paper7MomentCounts
