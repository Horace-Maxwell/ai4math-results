import Research.Backfill.Paper7.ChallengeV3

/-!
# Paper 7: the frozen window inequality

Source-only author candidate. The finite-set bound below includes the empty
set: its upper bound is `gW 0 + 2 * (0 - 1) = 0`. Thus the final proof also
covers `d = b`, including `b = 0`, without a positive-remainder hypothesis.
-/

set_option autoImplicit false

open Finset
open BackfillPaper7.Challenge

namespace BackfillPaper7.WindowProof

theorem thetaV_bounds (p q : ℕ) :
    2 ≤ thetaV p q ∧ thetaV p q ≤ gW ((p : ℤ) + 2 * q) := by
  have hp : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  constructor
  · unfold thetaV
    nlinarith [sq_nonneg (p : ℤ), sq_nonneg (q : ℤ), mul_nonneg hp hq]
  · unfold thetaV gW
    nlinarith [sq_nonneg (q : ℤ), mul_nonneg hp hq]

theorem gW_mono {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) : gW x ≤ gW y := by
  have hm : 0 ≤ (y - x) * (x + y + 3) :=
    mul_nonneg (by linarith) (by linarith)
  unfold gW
  nlinarith only [hm]

theorem sum_thetaV_bounds {α : Type*} (s : Finset α) (p q : α → ℕ) :
    2 * (s.card : ℤ) ≤ (∑ k ∈ s, thetaV (p k) (q k)) ∧
    (∑ k ∈ s, thetaV (p k) (q k)) ≤
      gW (∑ k ∈ s, ((p k : ℤ) + 2 * q k)) + 2 * ((s.card : ℤ) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num [gW]
  | @insert a s ha ih =>
    have hpoint := thetaV_bounds (p a) (q a)
    have hwa : (0 : ℤ) ≤ (p a : ℤ) + 2 * q a := by positivity
    have hws : (0 : ℤ) ≤ ∑ k ∈ s, ((p k : ℤ) + 2 * q k) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hmerge :
        gW ((p a : ℤ) + 2 * q a) +
            gW (∑ k ∈ s, ((p k : ℤ) + 2 * q k)) ≤
          gW (((p a : ℤ) + 2 * q a) +
            ∑ k ∈ s, ((p k : ℤ) + 2 * q k)) + 2 := by
      unfold gW
      nlinarith only [mul_nonneg hwa hws]
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one]
    constructor
    · linarith only [hpoint.1, ih.1]
    · linarith only [hpoint.2, ih.2, hmerge]

theorem prefix_card (b d : ℕ) (hdb : d ≤ b) :
    (Finset.univ.filter (fun k : Fin b => k.val < d)).card = d := by
  classical
  calc
    (Finset.univ.filter (fun k : Fin b => k.val < d)).card =
        (Finset.univ : Finset (Fin d)).card := by
      refine Finset.card_bij
        (fun k hk => (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin d)) ?_ ?_ ?_
      · intro _ _
        exact Finset.mem_univ _
      · intro _ _ _ _ hac
        exact Fin.ext (congrArg (fun k : Fin d => k.val) hac)
      · intro j _
        refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hdb⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
        · rfl
    _ = d := by simp

end BackfillPaper7.WindowProof

theorem check_Lemma53 : BackfillPaper7.Challenge.Lemma53 := by
  classical
  intro b d N p q hdb hn
  let s : Finset (Fin b) := Finset.univ.filter (fun k => k.val < d)
  let t : Finset (Fin b) := Finset.univ.filter (fun k => ¬k.val < d)
  let w : Fin b → ℤ := fun k => (p k : ℤ) + 2 * q k
  change
    (∑ k ∈ s, thetaV (p k) (q k)) + 2 * ((b : ℤ) - d) ≤
        (∑ k, thetaV (p k) (q k)) ∧
      (∑ k, thetaV (p k) (q k)) ≤
        (∑ k ∈ s, thetaV (p k) (q k)) +
          gW ((N : ℤ) - b - ∑ k ∈ s, w k) + 2 * ((b : ℤ) - d - 1)
  have hscard : s.card = d := BackfillPaper7.WindowProof.prefix_card b d hdb
  have hcards : s.card + t.card = b := by
    simpa only [s, t, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin b))) (fun k => k.val < d))
  have htcard : (t.card : ℤ) = (b : ℤ) - d := by
    have hcardsZ : (s.card : ℤ) + (t.card : ℤ) = b := by exact_mod_cast hcards
    rw [hscard] at hcardsZ
    linarith only [hcardsZ]
  have hthsplit :
      (∑ k ∈ s, thetaV (p k) (q k)) + (∑ k ∈ t, thetaV (p k) (q k)) =
        ∑ k, thetaV (p k) (q k) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin b => k.val < d) (fun k => thetaV (p k) (q k))
  have hwsplit : (∑ k ∈ s, w k) + (∑ k ∈ t, w k) = ∑ k, w k :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin b => k.val < d) w
  have hnZ : (b : ℤ) + (∑ k, w k) ≤ N := by
    have hnZ' : (nOf b p q : ℤ) ≤ N := by exact_mod_cast hn
    unfold nOf at hnZ'
    push_cast at hnZ'
    dsimp only [w]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith only [hnZ']
  have htw : (0 : ℤ) ≤ ∑ k ∈ t, w k := by
    apply Finset.sum_nonneg
    intro k _
    dsimp only [w]
    positivity
  have hremaining : (∑ k ∈ t, w k) ≤ (N : ℤ) - b - ∑ k ∈ s, w k := by
    linarith only [hnZ, hwsplit]
  have hg := BackfillPaper7.WindowProof.gW_mono htw hremaining
  obtain ⟨hlower, hupper⟩ := BackfillPaper7.WindowProof.sum_thetaV_bounds t p q
  change (∑ k ∈ t, thetaV (p k) (q k)) ≤
    gW (∑ k ∈ t, w k) + 2 * ((t.card : ℤ) - 1) at hupper
  rw [htcard] at hlower hupper
  constructor
  · linarith only [hthsplit, hlower]
  · linarith only [hthsplit, hupper, hg]

#print axioms BackfillPaper7.WindowProof.thetaV_bounds
#print axioms BackfillPaper7.WindowProof.gW_mono
#print axioms BackfillPaper7.WindowProof.sum_thetaV_bounds
#print axioms BackfillPaper7.WindowProof.prefix_card
#print axioms check_Lemma53
