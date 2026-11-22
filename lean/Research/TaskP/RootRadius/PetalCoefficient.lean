import Research.TaskP.RootRadius.Challenge

open Polynomial
namespace TaskP.GraphRootRadius.Proof
open Challenge

variable {V : Type*} [Fintype V]

/-- The complement of a nondominating set contains a whole closed neighborhood. -/
def Misses (B : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ v, closedNeighborhood B v ⊆ T

theorem misses_iff (B : SimpleGraph V) (T : Finset V) [DecidableEq V] :
    Misses B T ↔ ¬ Dominates B Tᶜ := by
  classical
  simp only [Misses, Dominates, Finset.mem_compl, not_forall, not_or, not_not,
    not_exists, not_and]
  apply exists_congr
  intro v
  simp only [closedNeighborhood, Finset.subset_iff, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  grind

theorem neighborhood_card (B : SimpleGraph V) (v : V) :
    (closedNeighborhood B v).card = by classical exact B.degree v + 1 := by
  classical
  simp [closedNeighborhood, B.card_neighborFinset_eq_degree]
  
theorem min_le_closed_card (B : SimpleGraph V) (v : V) :
    minimumSize B ≤ (closedNeighborhood B v).card := by
  classical
  rw [neighborhood_card, minimumSize]
  exact Nat.add_le_add_right (B.minDegree_le_degree v) 1

theorem min_le_misses (B : SimpleGraph V) {T : Finset V} (h : Misses B T) :
    minimumSize B ≤ T.card := by
  obtain ⟨v,hv⟩ := h
  exact (min_le_closed_card B v).trans (Finset.card_le_card hv)

noncomputable def bad (B : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (Misses B)

theorem bad_count (B : SimpleGraph V) :
    (by classical exact ((bad B).filter fun T => T.card = minimumSize B).card) =
      minimumCount B := by
  classical
  unfold minimumCount
  apply congrArg Finset.card
  ext T
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨v, hv⟩, he⟩
    exact ⟨⟨v, Finset.eq_of_subset_of_card_le hv (he ▸ min_le_closed_card B v)⟩, he⟩
  · rintro ⟨⟨v, rfl⟩, he⟩
    exact ⟨⟨v, Finset.Subset.rfl⟩, he⟩

noncomputable def normalized (B : SimpleGraph V) : ℂ[X] :=
  1 - ∑ T ∈ bad B, X ^ T.card * (1-X) ^ (Fintype.card V - T.card)

theorem normalized_tail (B : SimpleGraph V) : ∃ E : ℂ[X],
    normalized B = 1 - C (minimumCount B : ℂ) * X ^ minimumSize B +
      X ^ (minimumSize B + 1) * E := by
  classical
  let c := minimumSize B
  let f := fun T : Finset V => (X : ℂ[X]) ^ T.card * (1-X) ^ (Fintype.card V - T.card)
  have hdiv (T : Finset V) (hT : T ∈ bad B) :
      (X : ℂ[X]) ^ (c+1) ∣ (if T.card = c then X ^ c else 0) - f T := by
    have hle : c ≤ T.card := min_le_misses B (Finset.mem_filter.mp hT).2
    by_cases h : T.card = c
    · simp only [h, ite_true, f]
      obtain ⟨q,hq⟩ : (X : ℂ[X]) ∣ 1 - (1 - X) ^ (Fintype.card V - c) := by
        rw [X_dvd_iff, coeff_zero_eq_eval_zero]
        simp
      use q
      rw [pow_succ, mul_assoc, ← hq, mul_sub, mul_one]
    · simp only [h, ite_false, zero_sub, dvd_neg]
      exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
  obtain ⟨E,hE⟩ := Finset.dvd_sum hdiv
  refine ⟨E, ?_⟩
  have hcount : (∑ T ∈ bad B, if T.card = c then (X : ℂ[X]) ^ c else 0) =
      C (minimumCount B : ℂ) * X ^ c := by
    rw [← Finset.sum_filter]
    simp [c, bad_count]
  rw [Finset.sum_sub_distrib, hcount] at hE
  change 1 - ∑ T ∈ bad B, f T = _
  change 1 - ∑ T ∈ bad B, f T = 1 - C (minimumCount B : ℂ) * X ^ c + X ^ (c + 1) * E
  rw [← hE]
  ring

end TaskP.GraphRootRadius.Proof
