import Research.Backfill.Paper7.LegacyEnumeration

/-! Coordinate, lower-window and fixed-count guards only. No assertion about
monotonicity of WindowPass or windowHi is made. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem prefix_coordinate_mono (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) :
    ∀ i, («prefix» d x).1 i ≤ («prefix» d y).1 i ∧
      («prefix» d x).2 i ≤ («prefix» d y).2 i := by
  intro i
  by_cases hi : i.val < d
  · simpa only [«prefix», ite_eq_left hi] using hxy i
  · simp only [«prefix», ite_eq_right hi, le_refl, and_self]
#print axioms Paper7Pruning.prefix_coordinate_mono

theorem prefix_sums_mono (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) :
    pSum («prefix» d x) ≤ pSum («prefix» d y) ∧
      qSum («prefix» d x) ≤ qSum («prefix» d y) ∧
      weight («prefix» d x) ≤ weight («prefix» d y) := by
  have hp : pSum («prefix» d x) ≤ pSum («prefix» d y) :=
    Finset.sum_le_sum (fun i _ => (prefix_coordinate_mono b d x y hxy i).1)
  have hq : qSum («prefix» d x) ≤ qSum («prefix» d y) :=
    Finset.sum_le_sum (fun i _ => (prefix_coordinate_mono b d x y hxy i).2)
  refine ⟨hp, hq, ?_⟩
  unfold weight
  omega
#print axioms Paper7Pruning.prefix_sums_mono

theorem thetaV_coordinate_mono (p q p' q' : ℕ) (hp : p ≤ p') (hq : q ≤ q') :
    thetaV p q ≤ thetaV p' q' := by
  have hpZ : (p : ℤ) ≤ p' := by exact_mod_cast hp
  have hqZ : (q : ℤ) ≤ q' := by exact_mod_cast hq
  unfold thetaV
  apply add_le_add
  · exact mul_le_mul (by omega) (by omega) (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_left hqZ (by norm_num)
#print axioms Paper7Pruning.thetaV_coordinate_mono

theorem windowLo_coordinate_mono (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) : windowLo d x ≤ windowLo d y := by
  have h : prefixTheta d x ≤ prefixTheta d y := by
    apply Finset.sum_le_sum
    intro i _
    exact thetaV_coordinate_mono _ _ _ _ (hxy i).1 (hxy i).2
  unfold windowLo
  omega
#print axioms Paper7Pruning.windowLo_coordinate_mono

theorem partialCountPass_downward (b N d : ℕ) (x y : PQ b) (s : SpectralCounts)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i)
    (hy : PartialCountPass b N d y s) : PartialCountPass b N d x s := by
  have hm := prefix_sums_mono b d x y hxy
  dsimp only [PartialCountPass] at hy ⊢
  refine ⟨?_, ?_⟩
  · apply le_trans _ hy.1
    apply max_le_max
    · exact_mod_cast Nat.add_le_add_left hm.2.2 b
    · exact le_refl _
  · intro hp
    have hp' : 2 ≤ pSum («prefix» d y) := hp.trans hm.1
    have hy' := hy.2 hp'
    have hqZ : (qSum («prefix» d x) : ℤ) ≤ qSum («prefix» d y) := by
      exact_mod_cast hm.2.1
    omega
#print axioms Paper7Pruning.partialCountPass_downward

end Paper7Pruning
