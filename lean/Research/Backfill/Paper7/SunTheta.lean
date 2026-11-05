import Research.Backfill.Paper7.SunDegrees

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

/-- A positive arm with one or two vertices contributes twice its number of
internal arm vertices to the degree-factorial sum. -/
theorem sun_arm_theta {b : ℕ} {L : Fin b → List ℕ} (k : Fin b)
    (j : Fin (L k).length) (hL : (L k).get j = 1 ∨ (L k).get j = 2) :
    (∑ a : Fin ((L k).get j),
      ((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) *
        (((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) - 1)) =
      2 * (((L k).get j : ℤ) - 1) := by
  rcases hL with hL | hL
  · calc
      (∑ a : Fin ((L k).get j),
        ((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) *
          (((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) - 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro a _ha
        rw [sun_arm_degree_one k j hL a]
        norm_num
      _ = 2 * (((L k).get j : ℤ) - 1) := by
        rw [hL]
        norm_num
  · let a0 : Fin ((L k).get j) := ⟨0, by omega⟩
    let a1 : Fin ((L k).get j) := ⟨1, by omega⟩
    calc
      (∑ a : Fin ((L k).get j),
        ((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) *
          (((sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) : ℤ) - 1)) =
          ((sunGraph b L).degree (Sum.inr ⟨k, j, a0⟩) : ℤ) *
            (((sunGraph b L).degree (Sum.inr ⟨k, j, a0⟩) : ℤ) - 1) := by
        apply Finset.sum_eq_single a0
        · intro a _ha hne
          have hane : a.val ≠ 0 := by
            intro hav
            exact hne (Fin.ext hav)
          have hav : a.val = 1 := by have := a.isLt; omega
          have hae : a = a1 := Fin.ext hav
          rw [hae, sun_arm_degree_two_last k j hL]
          norm_num
        · simp
      _ = 2 := by
        rw [sun_arm_degree_two_first k j hL]
        norm_num
      _ = 2 * (((L k).get j : ℤ) - 1) := by
        rw [hL]
        norm_num

#print axioms Paper7Setup.sun_arm_theta

theorem sg_arms_theta_at (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) :
    (∑ j : Fin (pq b p q k).length, ∑ a : Fin ((pq b p q k).get j),
      ((SG b p q).degree (Sum.inr ⟨k, j, a⟩) : ℤ) *
        (((SG b p q).degree (Sum.inr ⟨k, j, a⟩) : ℤ) - 1)) = 2 * (q k : ℤ) := by
  have hsum : (∑ j : Fin (pq b p q k).length, ((pq b p q k).get j : ℤ)) =
      (p k : ℤ) + 2 * (q k : ℤ) := by
    exact_mod_cast Paper7Cleared.pq_sum_lengths b p q k
  calc
    (∑ j : Fin (pq b p q k).length, ∑ a : Fin ((pq b p q k).get j),
      ((SG b p q).degree (Sum.inr ⟨k, j, a⟩) : ℤ) *
        (((SG b p q).degree (Sum.inr ⟨k, j, a⟩) : ℤ) - 1)) =
        ∑ j : Fin (pq b p q k).length, 2 * (((pq b p q k).get j : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact sun_arm_theta k j (pq_get_one_or_two b p q k j)
    _ = 2 * ((∑ j : Fin (pq b p q k).length, ((pq b p q k).get j : ℤ)) -
        ((pq b p q k).length : ℤ)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    _ = 2 * (q k : ℤ) := by
      rw [hsum, pq_length]
      push_cast
      ring

#print axioms Paper7Setup.sg_arms_theta_at

theorem sg_theta (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    Theta (SG b p q) = ∑ k, thetaV (p k) (q k) := by
  unfold Theta
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sigma]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [sg_root_degree b p q hb k, sg_arms_theta_at b p q k]
  unfold thetaV
  push_cast
  ring

#print axioms Paper7Setup.sg_theta

/-- The three exact numerical conjuncts of SetupFacts; the graph-isomorphism
classification remains a separate required conjunct of the full contract. -/
theorem setup_counts (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    order b (pq b p q) = nOf b p q ∧
    (SG b p q).edgeFinset.card = nOf b p q ∧
    Theta (SG b p q) = ∑ k, thetaV (p k) (q k) :=
  ⟨sg_order b p q, sg_edges b p q hb, sg_theta b p q hb⟩

#print axioms Paper7Setup.setup_counts

end Paper7Setup
