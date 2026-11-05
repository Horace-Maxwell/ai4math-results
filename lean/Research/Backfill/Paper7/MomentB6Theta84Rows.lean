import Research.Backfill.Paper7.MomentB6Theta84Shape

/-! Source-only reconstruction of the original theta=84 fibre.
The actual successful shape theorem supplies coverage.  The q coordinates
are recovered from their original nonnegative values and exact total, and
each reconstructed row satisfies the full original catalogue guard.
No cardinality or injectivity conclusion is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6Theta84SingleRow (i : Fin 6) : PQ 6 :=
  (fun k => if k = i then 6 else 0, fun k => if k = i then 1 else 0)
#print axioms Paper7MomentCounts.b6Theta84SingleRow

def b6Theta84FullQRow (i j : Fin 6) : PQ 6 :=
  (fun _ => 0, b6SevenDouble i j)
#print axioms Paper7MomentCounts.b6Theta84FullQRow

def b6Theta84ZeroQRow (i j : Fin 6) : PQ 6 :=
  (b6TwoPoint 6 3 i j, fun _ => 0)
#print axioms Paper7MomentCounts.b6Theta84ZeroQRow

theorem b6Theta84SingleRow_accept (i : Fin 6) :
    b6CandidateGuard (b6Theta84SingleRow i) ∧ theta (b6Theta84SingleRow i) = 84 := by
  have hp : pSum (b6Theta84SingleRow i) = 6 := by
    simp [pSum, b6Theta84SingleRow]
  have hq : qSum (b6Theta84SingleRow i) = 1 := by
    simp [qSum, b6Theta84SingleRow]
  have hw : weight (b6Theta84SingleRow i) = 8 := by
    simp [weight, hp, hq]
  have he : theta (b6Theta84SingleRow i) =
      ∑ k : Fin 6, (2 + if k = i then 72 else 0 : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hki : k = i <;> norm_num [b6Theta84SingleRow, thetaV, hki]
  have ht : theta (b6Theta84SingleRow i) = 84 := by
    rw [he]
    norm_num [Finset.sum_add_distrib]
  refine ⟨?_, ht⟩
  unfold b6CandidateGuard
  rw [hw, hq, ht]
  refine ⟨by norm_num, by norm_num, (13,84), ?_, rfl, by norm_num, by norm_num⟩
  simp [b6FeatureCatalog]
#print axioms Paper7MomentCounts.b6Theta84SingleRow_accept

theorem b6Theta84FullQRow_accept (i j : Fin 6) (hij : i ≠ j) :
    b6CandidateGuard (b6Theta84FullQRow i j) ∧ theta (b6Theta84FullQRow i j) = 84 := by
  have hp : pSum (b6Theta84FullQRow i j) = 0 := by
    simp [pSum, b6Theta84FullQRow]
  have hq : qSum (b6Theta84FullQRow i j) = 7 := by
    simpa only [qSum, b6Theta84FullQRow] using b6SevenDouble_sum i j hij
  have hw : weight (b6Theta84FullQRow i j) = 14 := by
    simp [weight, hp, hq]
  have he : theta (b6Theta84FullQRow i j) =
      ∑ k : Fin 6, (2 + (if k = i then 66 else 0) +
        (if k = j then 6 else 0) : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hki : k = i
    · subst k
      norm_num [b6Theta84FullQRow, b6SevenDouble, thetaV, hij]
    · by_cases hkj : k = j
      · subst k
        norm_num [b6Theta84FullQRow, b6SevenDouble, thetaV, hki]
      · norm_num [b6Theta84FullQRow, b6SevenDouble, thetaV, hki, hkj]
  have ht : theta (b6Theta84FullQRow i j) = 84 := by
    rw [he]
    norm_num [Finset.sum_add_distrib]
  refine ⟨?_, ht⟩
  unfold b6CandidateGuard
  rw [hw, hq, ht]
  refine ⟨by norm_num, by norm_num, (13,84), ?_, rfl, by norm_num, by norm_num⟩
  simp [b6FeatureCatalog]
#print axioms Paper7MomentCounts.b6Theta84FullQRow_accept

theorem b6Theta84ZeroQRow_accept (i j : Fin 6) (hij : i ≠ j) :
    b6CandidateGuard (b6Theta84ZeroQRow i j) ∧ theta (b6Theta84ZeroQRow i j) = 84 := by
  have hp : pSum (b6Theta84ZeroQRow i j) = 9 := by
    simpa only [pSum, b6Theta84ZeroQRow] using (b6TwoPoint_sums 6 3 i j hij).1
  have hq : qSum (b6Theta84ZeroQRow i j) = 0 := by
    simp [qSum, b6Theta84ZeroQRow]
  have hw : weight (b6Theta84ZeroQRow i j) = 9 := by
    simp [weight, hp, hq]
  have he : theta (b6Theta84ZeroQRow i j) =
      ∑ k : Fin 6, (2 + (if k = i then 54 else 0) +
        (if k = j then 18 else 0) : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hki : k = i
    · subst k
      norm_num [b6Theta84ZeroQRow, b6TwoPoint, thetaV, hij]
    · by_cases hkj : k = j
      · subst k
        norm_num [b6Theta84ZeroQRow, b6TwoPoint, thetaV, hki]
      · norm_num [b6Theta84ZeroQRow, b6TwoPoint, thetaV, hki, hkj]
  have ht : theta (b6Theta84ZeroQRow i j) = 84 := by
    rw [he]
    norm_num [Finset.sum_add_distrib]
  refine ⟨?_, ht⟩
  unfold b6CandidateGuard
  rw [hw, hq, ht]
  refine ⟨by norm_num, by norm_num, (13,84), ?_, rfl, by norm_num, by norm_num⟩
  simp [b6FeatureCatalog]
#print axioms Paper7MomentCounts.b6Theta84ZeroQRow_accept

theorem b6_theta84_single_reconstruct (x : PQ 6) (i : Fin 6)
    (hz : (fun k => x.1 k + x.2 k) = b6SevenSingle i) (hq : qSum x = 1) :
    x = b6Theta84SingleRow i := by
  have hzero (k : Fin 6) (hki : k ≠ i) : x.1 k = 0 ∧ x.2 k = 0 := by
    have h := congrFun hz k
    simp only [b6SevenSingle, ite_eq_right hki] at h
    omega
  have hqi : x.2 i = 1 := by
    have he : qSum x = x.2 i := by
      apply Finset.sum_eq_single i
      · intro k _hk hki
        exact (hzero k hki).2
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    omega
  have hpi : x.1 i = 6 := by
    have h := congrFun hz i
    simp only [b6SevenSingle, ite_true] at h
    omega
  apply Prod.ext
  · funext k
    change x.1 k = if k = i then 6 else 0
    by_cases hki : k = i
    · subst k
      simpa only [ite_true] using hpi
    · simpa only [ite_eq_right hki] using (hzero k hki).1
  · funext k
    change x.2 k = if k = i then 1 else 0
    by_cases hki : k = i
    · subst k
      simpa only [ite_true] using hqi
    · simpa only [ite_eq_right hki] using (hzero k hki).2
#print axioms Paper7MomentCounts.b6_theta84_single_reconstruct

theorem b6_theta84_fullQ_reconstruct (x : PQ 6) (i j : Fin 6) (hij : i ≠ j)
    (hz : (fun k => x.1 k + x.2 k) = b6SevenDouble i j) (hq : qSum x = 7) :
    x = b6Theta84FullQRow i j := by
  have hs := congrArg (fun z : Fin 6 → ℕ => ∑ k, z k) hz
  have hpq : pSum x + qSum x = 7 := by
    simpa only [pSum, qSum, Finset.sum_add_distrib, b6SevenDouble_sum i j hij] using hs
  have hp : pSum x = 0 := by omega
  have hpzero (k : Fin 6) : x.1 k = 0 := by
    have hb := Finset.single_le_sum (s := Finset.univ) (f := x.1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    change x.1 k ≤ pSum x at hb
    omega
  apply Prod.ext
  · funext k
    change x.1 k = 0
    exact hpzero k
  · funext k
    change x.2 k = b6SevenDouble i j k
    have h := congrFun hz k
    simpa only [hpzero k, zero_add] using h
#print axioms Paper7MomentCounts.b6_theta84_fullQ_reconstruct

theorem b6_theta84_zeroQ_reconstruct (x : PQ 6) (i j : Fin 6)
    (hz : (fun k => x.1 k + x.2 k) = b6TwoPoint 6 3 i j) (hq : qSum x = 0) :
    x = b6Theta84ZeroQRow i j := by
  have hqzero (k : Fin 6) : x.2 k = 0 := by
    have hb := Finset.single_le_sum (s := Finset.univ) (f := x.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    change x.2 k ≤ qSum x at hb
    omega
  apply Prod.ext
  · funext k
    change x.1 k = b6TwoPoint 6 3 i j k
    have h := congrFun hz k
    simpa only [hqzero k, add_zero] using h
  · funext k
    change x.2 k = 0
    exact hqzero k
#print axioms Paper7MomentCounts.b6_theta84_zeroQ_reconstruct

theorem b6_theta84_guard_iff (x : PQ 6) :
    b6CandidateGuard x ∧ theta x = 84 ↔
    (∃ i, x = b6Theta84SingleRow i) ∨
    (∃ i j, i ≠ j ∧ x = b6Theta84FullQRow i j) ∨
    (∃ i j, i ≠ j ∧ x = b6Theta84ZeroQRow i j) := by
  constructor
  · rintro ⟨hg, ht⟩
    rcases b6_candidate_theta84_shapes x hg ht with
      ⟨i, hz, hq⟩ | ⟨i, j, hij, hz, hq⟩ | ⟨i, j, hij, hz, hq⟩
    · exact Or.inl ⟨i, b6_theta84_single_reconstruct x i hz hq⟩
    · exact Or.inr (Or.inl ⟨i, j, hij, b6_theta84_fullQ_reconstruct x i j hij hz hq⟩)
    · exact Or.inr (Or.inr ⟨i, j, hij, b6_theta84_zeroQ_reconstruct x i j hz hq⟩)
  · rintro (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact b6Theta84SingleRow_accept i
    · exact b6Theta84FullQRow_accept i j hij
    · exact b6Theta84ZeroQRow_accept i j hij
#print axioms Paper7MomentCounts.b6_theta84_guard_iff

end Paper7MomentCounts
