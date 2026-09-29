import Research.Backfill.Paper3.Proof.L67.Switch
import Research.Backfill.Paper3.Proof.L67.Marked

/-!
# Lemma 6: the switch identity `P_{2K} - P_{H_d} = 2 (z - 1) D`

For a vertex set `A` of `2 K_{d,d}` with sides `(L₀, R₀, L₁, R₁)`, `α_k = [u_k ∈ A]`,
`β_k = [w_k ∈ A]`, the 2-switch identity gives `z^{e_{2K}(A)} - z^{e_H(A)} =`
`(z - 1)(α₁ - α₂)(β₁ - β₂) z^{|L₀||R₀| - α₁β₁} z^{|L₁||R₁| - α₂β₂}`; the marked sums of
`Research.Backfill.Paper3.Proof.L67.Marked` and `W₁₀ = W₀₁` turn the sum into `2 (z - 1)(W₀₀ W₁₁ - W₁₀²)`. The second
assertion follows by telescoping `Σ_{s ≤ t} [z^s]((z - 1) R) = -[z^t] R`.
-/

set_option autoImplicit false

namespace P3L67

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

/-- `H_d` is a valid 2-switch of `2 K_{d,d}`. -/
theorem validSwitch_Hd (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) :
    ValidSwitch (KddUnion 2 d) ((0 : Fin 2), (Sum.inl a₁ : Fin d ⊕ Fin d)) (0, Sum.inr b₁)
      (1, Sum.inl a₂) (1, Sum.inr b₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [boxProd_adj]

theorem ite_and_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then 1 else 0 : ℕ) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ite_le_one (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≤ 1 := by
  split_ifs <;> simp

theorem ite_mul_ite_le_card {α : Type*} [DecidableEq α] (a b : α) (L R : Finset α) :
    (if a ∈ L then 1 else 0 : ℕ) * (if b ∈ R then 1 else 0) ≤ #L * #R := by
  by_cases ha : a ∈ L
  · by_cases hb : b ∈ R
    · rw [ite_eq_left ha, ite_eq_left hb]
      exact Nat.mul_le_mul (Finset.card_pos.2 ⟨a, ha⟩) (Finset.card_pos.2 ⟨b, hb⟩)
    · rw [ite_eq_right hb, mul_zero]
      exact Nat.zero_le _
  · rw [ite_eq_right ha, zero_mul]
    exact Nat.zero_le _

/-- `z^{αβ + α'β'} - z^{αβ' + α'β} = (z - 1)(α - α')(β - β')` for `α, β, α', β' ∈ {0, 1}`. -/
theorem core_pow (x y z w : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (hw : w ≤ 1) :
    (X : ℤ[X]) ^ (x * y + z * w) - X ^ (x * w + z * y) =
      (X - 1) * C (((x : ℤ) - z) * ((y : ℤ) - w)) := by
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> simp

theorem pow_switch (N₀ N₁ E x y z w : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (hw : w ≤ 1)
    (h₀ : x * y ≤ N₀) (h₁ : z * w ≤ N₁) (hE : E + x * y + z * w = N₀ + N₁ + x * w + z * y) :
    (X : ℤ[X]) ^ (N₀ + N₁) - X ^ E =
      (X - 1) * (C (((x : ℤ) - z) * ((y : ℤ) - w)) * X ^ (N₀ - x * y) * X ^ (N₁ - z * w)) := by
  obtain ⟨n₀, rfl⟩ : ∃ n₀, N₀ = n₀ + x * y := ⟨N₀ - x * y, by omega⟩
  obtain ⟨n₁, rfl⟩ : ∃ n₁, N₁ = n₁ + z * w := ⟨N₁ - z * w, by omega⟩
  obtain rfl : E = n₀ + n₁ + (x * w + z * y) := by omega
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  have h := core_pow x y z w hx hy hz hw
  calc (X : ℤ[X]) ^ (n₀ + x * y + (n₁ + z * w)) - X ^ (n₀ + n₁ + (x * w + z * y)) =
        X ^ n₀ * X ^ n₁ * (X ^ (x * y + z * w) - X ^ (x * w + z * y)) := by ring
    _ = _ := by rw [h]; ring

/-- **Lemma 6**, first part: `P_{2K}(z) - P_{H_d}(z) = 2 (z - 1) D(z)`. -/
theorem lemma6_poly (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) :
    edgePoly (KddUnion 2 d) - edgePoly (Hd d a₁ b₁ a₂ b₂) = 2 * (X - 1) * Dpoly d := by
  have hv := validSwitch_Hd d a₁ b₁ a₂ b₂
  have hpt : ∀ L₀ R₀ L₁ R₁ : Finset (Fin d),
      (X : ℤ[X]) ^ edgesIn (KddUnion 2 d) (quad L₀ R₀ L₁ R₁) -
          X ^ edgesIn (Hd d a₁ b₁ a₂ b₂) (quad L₀ R₀ L₁ R₁) =
        (X - 1) * (C ((((if a₁ ∈ L₀ then 1 else 0 : ℕ) : ℤ) -
              ((if a₂ ∈ L₁ then 1 else 0 : ℕ) : ℤ)) *
            (((if b₁ ∈ R₀ then 1 else 0 : ℕ) : ℤ) - ((if b₂ ∈ R₁ then 1 else 0 : ℕ) : ℤ))) *
          X ^ (#L₀ * #R₀ - (if a₁ ∈ L₀ then 1 else 0) * (if b₁ ∈ R₀ then 1 else 0)) *
          X ^ (#L₁ * #R₁ - (if a₂ ∈ L₁ then 1 else 0) * (if b₂ ∈ R₁ then 1 else 0))) := by
    intro L₀ R₀ L₁ R₁
    have hsw := edgesIn_twoSwitch (H := Hd d a₁ b₁ a₂ b₂) rfl hv (quad L₀ R₀ L₁ R₁)
    rw [edgesIn_quad] at hsw ⊢
    simp only [mem_quad_0_inl, mem_quad_0_inr, mem_quad_1_inl, mem_quad_1_inr, ite_and_one] at hsw
    exact pow_switch _ _ _ _ _ _ _ (ite_le_one _) (ite_le_one _) (ite_le_one _) (ite_le_one _)
      (ite_mul_ite_le_card _ _ _ _) (ite_mul_ite_le_card _ _ _ _) (by linarith [hsw])
  unfold edgePoly
  rw [← Finset.sum_sub_distrib, sum_quad]
  simp only [hpt, ← Finset.mul_sum]
  rw [sum_marked2 d (by omega) a₁ b₁ a₂ b₂ (fun x y z w => C (((x : ℤ) - z) * ((y : ℤ) - w)))]
  simp only [Wsum, Nat.cast_zero, Nat.cast_one, sub_self, sub_zero, zero_sub, mul_zero, zero_mul,
    mul_one, one_mul, mul_neg, neg_mul, neg_zero, map_zero, map_one, map_neg, zero_add, add_zero]
  rw [Dpoly, wSymm]
  ring

/-- `Σ_{s ≤ t} [z^s]((z - 1) R) = -[z^t] R`. -/
theorem sum_coeff_X_sub_one_mul (R : ℤ[X]) (t : ℕ) :
    ∑ s ∈ range (t + 1), ((X - 1) * R).coeff s = -R.coeff t := by
  induction t with
  | zero => simp [sub_mul]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, sub_mul, coeff_sub, one_mul, coeff_X_mul]
    ring

/-- **Lemma 6**, second part. -/
theorem lemma6_count (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) (W : Type) [Fintype W]
    [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj] (t : ℕ) :
    (iCount (Hd d a₁ b₁ a₂ b₂ ⊕g F) t : ℤ) - iCount (KddUnion 2 d ⊕g F) t =
      2 * (Dpoly d * edgePoly F).coeff t := by
  rw [iCount_eq_sum_coeff, iCount_eq_sum_coeff, edgePoly_sum, edgePoly_sum,
    ← Finset.sum_sub_distrib]
  have hH : edgePoly (Hd d a₁ b₁ a₂ b₂) = edgePoly (KddUnion 2 d) - 2 * (X - 1) * Dpoly d := by
    rw [← lemma6_poly d hd a₁ b₁ a₂ b₂]
    ring
  have e : ∀ s, (edgePoly (Hd d a₁ b₁ a₂ b₂) * edgePoly F).coeff s -
      (edgePoly (KddUnion 2 d) * edgePoly F).coeff s =
        -2 * ((X - 1) * (Dpoly d * edgePoly F)).coeff s := by
    intro s
    have hC : (C (-2 : ℤ) : ℤ[X]) = -2 := by simp
    have hp : (edgePoly (KddUnion 2 d) - 2 * (X - 1) * Dpoly d) * edgePoly F -
        edgePoly (KddUnion 2 d) * edgePoly F = C (-2) * ((X - 1) * (Dpoly d * edgePoly F)) := by
      rw [hC]
      ring
    rw [hH, ← coeff_sub, hp, coeff_C_mul]
  simp only [e]
  rw [← Finset.mul_sum, sum_coeff_X_sub_one_mul]
  ring

end P3L67
