import Research.TaskP.RootRadius.PetalCoefficient

open Polynomial
namespace TaskP.GraphRootRadius.Proof
open Challenge

variable {V : Type*} [Fintype V]

theorem normalized_eval (B : SimpleGraph V) (w : ℂ) :
    (normalized B).eval w =
      ∑ S : Finset V, (by classical exact if Dominates B S then
        (1-w)^S.card * w^(Fintype.card V - S.card) else 0) := by
  classical
  let weight := fun S : Finset V => (1-w)^S.card * w^(Fintype.card V-S.card)
  have total : ∑ S, weight S = 1 := by
    simpa [weight] using Fintype.sum_pow_mul_eq_add_pow V (1-w) w
  have reindex : (∑ T ∈ bad B, w^T.card * (1-w)^(Fintype.card V-T.card)) =
      ∑ S : Finset V, if Dominates B S then 0 else weight S := by
    simp only [bad, Finset.sum_filter]
    calc
      _ = ∑ T : Finset V, if Dominates B Tᶜ then 0 else weight Tᶜ := by
        apply Finset.sum_congr rfl
        intro T _
        by_cases h : Dominates B Tᶜ
        · simp [h, misses_iff]
        · simp [h, misses_iff, weight, Finset.card_compl, Nat.sub_sub_self T.card_le_univ, mul_comm]
      _ = _ := compl_bijective.sum_comp (fun S : Finset V => if Dominates B S then 0 else weight S)
  simp only [normalized, eval_sub, eval_one, eval_finsetSum, eval_mul, eval_pow, eval_X]
  rw [reindex]
  conv_lhs => lhs; rw [← total]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : Dominates B S <;> simp [h, weight]

theorem normalized_at_inverse (B : SimpleGraph V) {y : ℂ} (hy : y ≠ 0) :
    y^(Fintype.card V) * (normalized B).eval y⁻¹ =
      (dominationPolynomial B).eval (y-1) := by
  classical
  rw [normalized_eval, dominationPolynomial, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : Dominates B S
  · simp only [h, ite_true, eval_pow, eval_X]
    have e : 1 - y⁻¹ = (y-1)/y := by field_simp
    rw [e, div_pow, inv_pow_sub₀ hy S.card_le_univ]
    field_simp
  · simp [h]

theorem minimumCount_pos [Nonempty V] (B : SimpleGraph V) : 0 < minimumCount B := by
  classical
  obtain ⟨v,hv⟩ := B.exists_minimal_degree_vertex
  have hc : (closedNeighborhood B v).card = minimumSize B := by
    rw [neighborhood_card, minimumSize, hv]
  apply Finset.card_pos.mpr
  exact ⟨closedNeighborhood B v, Finset.mem_filter.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ v), hc⟩⟩

end TaskP.GraphRootRadius.Proof
