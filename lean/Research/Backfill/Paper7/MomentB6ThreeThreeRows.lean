import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Pending exact four-row fibre for two interlaced blocks repeated three
 times. The complete original guard and both candidate predicates remain
 unchanged. The small finite certificate is over all budget-bounded actual
 block coordinates; it neither asserts a list is complete nor assumes the
 final labelled or canonical count. No native evaluation is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6ThreeThreeRow (p r q s : ℕ) : PQ 6 :=
  (![p,r,p,r,p,r], ![q,s,q,s,q,s])
#print axioms Paper7MomentCounts.b6ThreeThreeRow

theorem b6ThreeThreeRow_features (p r q s : ℕ) :
    weight (b6ThreeThreeRow p r q s) = 3 * (p+r) + 6 * (q+s) ∧
    qSum (b6ThreeThreeRow p r q s) = 3 * (q+s) ∧
    theta (b6ThreeThreeRow p r q s) = 3 * (thetaV p q + thetaV r s) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [b6ThreeThreeRow, weight, pSum, qSum, Fin.sum_univ_succ]
    ring
  · simp [b6ThreeThreeRow, qSum, Fin.sum_univ_succ]
    ring
  · simp [b6ThreeThreeRow, theta, Fin.sum_univ_succ]
    ring
#print axioms Paper7MomentCounts.b6ThreeThreeRow_features

theorem b6_three_three_small_certificate :
    ∀ p r : Fin 13, ∀ q s : Fin 7,
      (0 < 3 * (p.val+r.val) + 6 * (q.val+s.val) ∧
        3 * (p.val+r.val) + 6 * (q.val+s.val) ≤ 36 ∧
        b6FeatureGuard (3 * (p.val+r.val) + 6 * (q.val+s.val))
          (3 * (q.val+s.val)) (3 * (thetaV p.val q.val + thetaV r.val s.val))) ↔
      (q.val = 0 ∧ s.val = 0 ∧
        ((p.val = 4 ∧ r.val = 0) ∨ (p.val = 0 ∧ r.val = 4) ∨
         (p.val = 9 ∧ r.val = 0) ∨ (p.val = 0 ∧ r.val = 9))) := by
  let accepted (p r q s : ℕ) : Bool :=
    let W := 3 * (p+r) + 6 * (q+s)
    let Q := 3 * (q+s)
    let T := 3 * (thetaV p q + thetaV r s)
    decide (0 < W ∧ W ≤ 36) &&
      decide (∃ sm ∈ b6FeatureCatalog, sm.2 = T ∧
        sm.1 ≤ (6 + W : ℤ) ∧ (6 + W : ℤ) - max (Q : ℤ) 2 ≤ sm.1)
  let classified (p r q s : ℕ) : Bool :=
    decide (q = 0 ∧ s = 0 ∧
      ((p = 4 ∧ r = 0) ∨ (p = 0 ∧ r = 4) ∨
       (p = 9 ∧ r = 0) ∨ (p = 0 ∧ r = 9)))
  have reflect (p r q s : ℕ) : accepted p r q s = true ↔
      (0 < 3 * (p+r) + 6 * (q+s) ∧ 3 * (p+r) + 6 * (q+s) ≤ 36 ∧
        b6FeatureGuard (3 * (p+r) + 6 * (q+s))
          (3 * (q+s)) (3 * (thetaV p q + thetaV r s))) := by
    simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, b6FeatureGuard, and_assoc]
  have certificate : ∀ p r : Fin 13, ∀ q s : Fin 7,
      accepted p.val r.val q.val s.val = classified p.val r.val q.val s.val := by
    decide +kernel
  intro p r q s
  rw [← reflect p.val r.val q.val s.val, certificate p r q s]
  simp only [classified, decide_eq_true_eq]
#print axioms Paper7MomentCounts.b6_three_three_small_certificate

theorem b6_candB1_threeThreeRow_iff (p r q s : ℕ) :
    b6ThreeThreeRow p r q s ∈ CandB1 6 42 ↔
      q = 0 ∧ s = 0 ∧
        ((p = 4 ∧ r = 0) ∨ (p = 0 ∧ r = 4) ∨
         (p = 9 ∧ r = 0) ∨ (p = 0 ∧ r = 9)) := by
  rw [b6_candB1_iff_guard]
  have hf := b6ThreeThreeRow_features p r q s
  change (0 < weight (b6ThreeThreeRow p r q s) ∧
    weight (b6ThreeThreeRow p r q s) ≤ 36 ∧
    b6FeatureGuard (weight (b6ThreeThreeRow p r q s))
      (qSum (b6ThreeThreeRow p r q s)) (theta (b6ThreeThreeRow p r q s))) ↔ _
  rw [hf.1, hf.2.1, hf.2.2]
  constructor
  · intro h
    have hp : p < 13 := by omega
    have hr : r < 13 := by omega
    have hq : q < 7 := by omega
    have hs : s < 7 := by omega
    exact (b6_three_three_small_certificate ⟨p,hp⟩ ⟨r,hr⟩ ⟨q,hq⟩ ⟨s,hs⟩).mp h
  · rintro ⟨rfl, rfl, h⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      norm_num [b6FeatureGuard, b6FeatureCatalog, thetaV]
#print axioms Paper7MomentCounts.b6_candB1_threeThreeRow_iff

def b6ThreeThreeTemplate : Fin 4 → PQ 6 :=
  ![b6ThreeThreeRow 4 0 0 0, b6ThreeThreeRow 0 4 0 0,
    b6ThreeThreeRow 9 0 0 0, b6ThreeThreeRow 0 9 0 0]
#print axioms Paper7MomentCounts.b6ThreeThreeTemplate

theorem b6ThreeThreeTemplate_injective : Function.Injective b6ThreeThreeTemplate := by
  decide +kernel
#print axioms Paper7MomentCounts.b6ThreeThreeTemplate_injective

theorem b6ThreeThreeTemplate_accept (i : Fin 4) :
    b6ThreeThreeTemplate i ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, b6ThreeThreeTemplate i = b6ThreeThreeRow p r q s := by
  fin_cases i
  · exact ⟨(b6_candB1_threeThreeRow_iff 4 0 0 0).mpr
      ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩,4,0,0,0,rfl⟩
  · exact ⟨(b6_candB1_threeThreeRow_iff 0 4 0 0).mpr
      ⟨rfl,rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩,0,4,0,0,rfl⟩
  · exact ⟨(b6_candB1_threeThreeRow_iff 9 0 0 0).mpr
      ⟨rfl,rfl,Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩,9,0,0,0,rfl⟩
  · exact ⟨(b6_candB1_threeThreeRow_iff 0 9 0 0).mpr
      ⟨rfl,rfl,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩,0,9,0,0,rfl⟩
#print axioms Paper7MomentCounts.b6ThreeThreeTemplate_accept

def b6ThreeThreeB1Equiv : Fin 4 ≃
    {x : PQ 6 // x ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} :=
  Equiv.ofBijective (fun i => ⟨b6ThreeThreeTemplate i,b6ThreeThreeTemplate_accept i⟩)
    ⟨fun _ _ h => b6ThreeThreeTemplate_injective (congrArg Subtype.val h),by
      rintro ⟨x,hx,p,r,q,s,he⟩
      have hx' : b6ThreeThreeRow p r q s ∈ CandB1 6 42 := he ▸ hx
      obtain ⟨hq,hs,hpr⟩ := (b6_candB1_threeThreeRow_iff p r q s).mp hx'
      subst q s
      rcases hpr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨0,Subtype.ext he.symm⟩
      · exact ⟨1,Subtype.ext he.symm⟩
      · exact ⟨2,Subtype.ext he.symm⟩
      · exact ⟨3,Subtype.ext he.symm⟩⟩
#print axioms Paper7MomentCounts.b6ThreeThreeB1Equiv

theorem b6_three_three_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s}.ncard = 4 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧
    ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} = 4
  rw [Nat.card_congr b6ThreeThreeB1Equiv.symm]
  simp
#print axioms Paper7MomentCounts.b6_three_three_candB1_ncard

theorem b6_three_three_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s}.ncard = 4 := by
  have he : {x : PQ 6 | x ∈ CandD2 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} =
    {x : PQ 6 | x ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} := by
    ext x
    exact and_congr ((b6_candD2_iff_guard x).trans (b6_candB1_iff_guard x).symm) Iff.rfl
  rw [he]
  exact b6_three_three_candB1_ncard
#print axioms Paper7MomentCounts.b6_three_three_candD2_ncard

end Paper7MomentCounts
