import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false

namespace Paper7Reduced

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem positive_pred_sum_add_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < a i), (a i - 1)) +
        (Finset.univ.filter (fun i => 0 < a i)).card = ∑ i, a i := by
  classical
  let S := Finset.univ.filter (fun i => 0 < a i)
  change (∑ i ∈ S, (a i - 1)) + S.card = ∑ i, a i
  calc
    (∑ i ∈ S, (a i - 1)) + S.card = ∑ i ∈ S, ((a i - 1) + 1) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ i ∈ S, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpos : 0 < a i := (Finset.mem_filter.mp hi).2
      omega
    _ = ∑ i, a i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _hi hn
      have hpos : ¬0 < a i := by
        intro h
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      omega

#print axioms Paper7Reduced.positive_pred_sum_add_card

theorem positive_pred_sum_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < a i), (a i - 1)) = ∑ i, (a i - 1) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : 0 < a i
  · simp only [hi, ite_true]
  · have hz : a i = 0 := by omega
    simp [hz]

#print axioms Paper7Reduced.positive_pred_sum_filter

theorem freeP_add_card (b : ℕ) (p : Fin b → ℕ) :
    freeP b p + (Kp b p).card = totalP b p := by
  simpa only [freeP, Kp, totalP] using positive_pred_sum_add_card p

#print axioms Paper7Reduced.freeP_add_card

theorem freeQ_add_card (b : ℕ) (q : Fin b → ℕ) :
    freeQ b q + (Kq b q).card = totalQ b q := by
  simpa only [freeQ, Kq, totalQ] using positive_pred_sum_add_card q

#print axioms Paper7Reduced.freeQ_add_card

theorem freeP_eq_sub (b : ℕ) (p : Fin b → ℕ) :
    freeP b p = totalP b p - (Kp b p).card := by
  have h := freeP_add_card b p
  omega

#print axioms Paper7Reduced.freeP_eq_sub

theorem freeQ_eq_sub (b : ℕ) (q : Fin b → ℕ) :
    freeQ b q = totalQ b q - (Kq b q).card := by
  have h := freeQ_add_card b q
  omega

#print axioms Paper7Reduced.freeQ_eq_sub

end Paper7Reduced
