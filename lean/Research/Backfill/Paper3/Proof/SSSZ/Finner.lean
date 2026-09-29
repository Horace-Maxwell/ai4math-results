import Mathlib

/-!
# Two-point Hölder inequality and Finner's inequality on the Boolean cube

`holder_two`: if `#R = d ≥ 1` and `a, b ≥ 0`, then
`∏ a_r^{1/d} + ∏ b_r^{1/d} ≤ ∏ (a_r + b_r)^{1/d}` (the geometric mean is superadditive; proof
by weighted AM–GM). `finner`: if every point of `L` lies in exactly `d` of the sets `N r ⊆ L`,
then `∑_{S ⊆ L} ∏_r h_r(S ∩ N_r)^{1/d} ≤ ∏_r (∑_{T ⊆ N_r} h_r(T))^{1/d}` for `h ≥ 0`, by
induction on `L`, merging the two values of a new point with `holder_two`.
-/

set_option autoImplicit false

open Finset

namespace P3SSSZ

/-- Superadditivity of the geometric mean of `d` numbers (Hölder for two-point sums). -/
theorem holder_two {ι : Type*} (R : Finset ι) (d : ℕ) (hR : #R = d) (hd : d ≠ 0)
    (a b : ι → ℝ) (ha : ∀ r ∈ R, 0 ≤ a r) (hb : ∀ r ∈ R, 0 ≤ b r) :
    ∏ r ∈ R, a r ^ ((d : ℝ)⁻¹) + ∏ r ∈ R, b r ^ ((d : ℝ)⁻¹) ≤
      ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hinv : (d : ℝ)⁻¹ ≠ 0 := inv_ne_zero hdpos.ne'
  have hRHS : 0 ≤ ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹) :=
    prod_nonneg fun r hr => Real.rpow_nonneg (add_nonneg (ha r hr) (hb r hr)) _
  by_cases hz : ∃ r ∈ R, a r + b r = 0
  · obtain ⟨r, hr, hab⟩ := hz
    have har : a r = 0 := by linarith [ha r hr, hb r hr]
    have hbr : b r = 0 := by linarith [ha r hr, hb r hr]
    have h1 : ∏ r ∈ R, a r ^ ((d : ℝ)⁻¹) = 0 :=
      prod_eq_zero hr (by rw [har, Real.zero_rpow hinv])
    have h2 : ∏ r ∈ R, b r ^ ((d : ℝ)⁻¹) = 0 :=
      prod_eq_zero hr (by rw [hbr, Real.zero_rpow hinv])
    rw [h1, h2, add_zero]
    exact hRHS
  · simp only [not_exists, not_and] at hz
    have hs : ∀ r ∈ R, 0 < a r + b r := fun r hr =>
      lt_of_le_of_ne (add_nonneg (ha r hr) (hb r hr)) (Ne.symm (hz r hr))
    have hw : ∑ _r ∈ R, (d : ℝ)⁻¹ = 1 := by
      rw [sum_const, hR, nsmul_eq_mul, mul_inv_cancel₀ hdpos.ne']
    have hwn : ∀ r ∈ R, (0 : ℝ) ≤ (d : ℝ)⁻¹ := fun _ _ => inv_nonneg.mpr hdpos.le
    have amx := Real.geom_mean_le_arith_mean_weighted R (fun _ => (d : ℝ)⁻¹)
      (fun r => a r / (a r + b r)) hwn hw (fun r hr => div_nonneg (ha r hr) (hs r hr).le)
    have amy := Real.geom_mean_le_arith_mean_weighted R (fun _ => (d : ℝ)⁻¹)
      (fun r => b r / (a r + b r)) hwn hw (fun r hr => div_nonneg (hb r hr) (hs r hr).le)
    have hsum : ∑ r ∈ R, (d : ℝ)⁻¹ * (a r / (a r + b r)) +
        ∑ r ∈ R, (d : ℝ)⁻¹ * (b r / (a r + b r)) = 1 := by
      rw [← sum_add_distrib, ← hw]
      refine sum_congr rfl fun r hr => ?_
      rw [← mul_add, ← add_div, div_self (hs r hr).ne', mul_one]
    have hsplit : ∀ c : ι → ℝ, (∀ r ∈ R, 0 ≤ c r) →
        ∏ r ∈ R, c r ^ ((d : ℝ)⁻¹) =
          (∏ r ∈ R, (c r / (a r + b r)) ^ ((d : ℝ)⁻¹)) *
            ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹) := by
      intro c hc
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r hr => ?_
      rw [← Real.mul_rpow (div_nonneg (hc r hr) (hs r hr).le) (hs r hr).le,
        div_mul_cancel₀ _ (hs r hr).ne']
    rw [hsplit a ha, hsplit b hb, ← add_mul]
    calc (∏ r ∈ R, (a r / (a r + b r)) ^ ((d : ℝ)⁻¹) +
            ∏ r ∈ R, (b r / (a r + b r)) ^ ((d : ℝ)⁻¹)) *
          ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹)
        ≤ 1 * ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ hRHS
          linarith
      _ = ∏ r ∈ R, (a r + b r) ^ ((d : ℝ)⁻¹) := one_mul _

/-- **Finner's inequality** on the Boolean cube `𝒫(L)` with counting measure, when every point
of `L` lies in exactly `d` of the sets `N r`. -/
theorem finner {α ι : Type*} [DecidableEq α] [Fintype ι] (d : ℕ) (hd : d ≠ 0)
    (L : Finset α) :
    ∀ (N : ι → Finset α), (∀ r, N r ⊆ L) →
      (∀ l ∈ L, #(univ.filter fun r => l ∈ N r) = d) →
      ∀ (h : ι → Finset α → ℝ), (∀ r T, 0 ≤ h r T) →
        ∑ S ∈ L.powerset, ∏ r, h r (S ∩ N r) ^ ((d : ℝ)⁻¹) ≤
          ∏ r, (∑ T ∈ (N r).powerset, h r T) ^ ((d : ℝ)⁻¹) := by
  induction L using Finset.induction_on with
  | empty =>
    intro N hN _ h _
    have hN' : ∀ r, N r = ∅ := fun r => Finset.subset_empty.mp (hN r)
    simp [hN']
  | insert l L hl ih =>
    intro N hN hdeg h h0
    set N' : ι → Finset α := fun r => (N r).erase l with hN'def
    set h' : ι → Finset α → ℝ :=
      fun r T => if l ∈ N r then h r T + h r (insert l T) else h r T with hh'def
    have hN'L : ∀ r, N' r ⊆ L := by
      intro r x hx
      rw [hN'def, Finset.mem_erase] at hx
      have := hN r hx.2
      rw [Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hdeg' : ∀ l' ∈ L, #(univ.filter fun r => l' ∈ N' r) = d := by
      intro l' hl'
      have hne : l' ≠ l := fun h => hl (h ▸ hl')
      rw [← hdeg l' (Finset.mem_insert_of_mem hl')]
      congr 1
      apply Finset.filter_congr
      intro r _
      rw [hN'def, Finset.mem_erase]
      exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
    have h'0 : ∀ r T, 0 ≤ h' r T := by
      intro r T
      simp only [hh'def]
      split_ifs
      · exact add_nonneg (h0 r T) (h0 r (insert l T))
      · exact h0 r T
    have key := ih N' hN'L hdeg' h' h'0
    have hRl : #(univ.filter fun r => l ∈ N r) = d := hdeg l (Finset.mem_insert_self l L)
    rw [sum_powerset_insert hl, ← sum_add_distrib]
    calc ∑ S ∈ L.powerset, (∏ r, h r (S ∩ N r) ^ ((d : ℝ)⁻¹) +
            ∏ r, h r (insert l S ∩ N r) ^ ((d : ℝ)⁻¹))
        ≤ ∑ S ∈ L.powerset, ∏ r, h' r (S ∩ N' r) ^ ((d : ℝ)⁻¹) := by
          apply sum_le_sum
          intro S hS
          have hlS : l ∉ S := fun h => hl (Finset.mem_powerset.mp hS h)
          have e1 : ∀ r, S ∩ N r = S ∩ N' r := by
            intro r
            rw [hN'def, Finset.inter_erase, Finset.erase_eq_of_notMem]
            exact fun h => hlS (Finset.mem_inter.mp h).1
          -- split every product according to whether `l ∈ N r`
          rw [← prod_filter_mul_prod_filter_not univ (fun r => l ∈ N r)
              (fun r => h r (S ∩ N r) ^ ((d : ℝ)⁻¹)),
            ← prod_filter_mul_prod_filter_not univ (fun r => l ∈ N r)
              (fun r => h r (insert l S ∩ N r) ^ ((d : ℝ)⁻¹)),
            ← prod_filter_mul_prod_filter_not univ (fun r => l ∈ N r)
              (fun r => h' r (S ∩ N' r) ^ ((d : ℝ)⁻¹))]
          have q1 : ∏ r ∈ univ.filter (fun r => l ∈ N r), h r (insert l S ∩ N r) ^ ((d : ℝ)⁻¹) =
              ∏ r ∈ univ.filter (fun r => l ∈ N r),
                h r (insert l (S ∩ N' r)) ^ ((d : ℝ)⁻¹) := by
            refine prod_congr rfl fun r hr => ?_
            rw [Finset.insert_inter_of_mem (Finset.mem_filter.mp hr).2, e1 r]
          have q2 : ∏ r ∈ univ.filter (fun r => l ∈ N r), h r (S ∩ N r) ^ ((d : ℝ)⁻¹) =
              ∏ r ∈ univ.filter (fun r => l ∈ N r), h r (S ∩ N' r) ^ ((d : ℝ)⁻¹) := by
            refine prod_congr rfl fun r _ => ?_
            rw [e1 r]
          have q3 : ∏ r ∈ univ.filter (fun r => l ∈ N r), h' r (S ∩ N' r) ^ ((d : ℝ)⁻¹) =
              ∏ r ∈ univ.filter (fun r => l ∈ N r),
                (h r (S ∩ N' r) + h r (insert l (S ∩ N' r))) ^ ((d : ℝ)⁻¹) := by
            refine prod_congr rfl fun r hr => ?_
            simp only [hh'def, (Finset.mem_filter.mp hr).2, ↓reduceIte]
          have q4 : ∏ r ∈ univ.filter (fun r => ¬ l ∈ N r),
                h r (insert l S ∩ N r) ^ ((d : ℝ)⁻¹) =
              ∏ r ∈ univ.filter (fun r => ¬ l ∈ N r), h r (S ∩ N r) ^ ((d : ℝ)⁻¹) := by
            refine prod_congr rfl fun r hr => ?_
            rw [Finset.insert_inter_of_notMem (Finset.mem_filter.mp hr).2]
          have q5 : ∏ r ∈ univ.filter (fun r => ¬ l ∈ N r), h' r (S ∩ N' r) ^ ((d : ℝ)⁻¹) =
              ∏ r ∈ univ.filter (fun r => ¬ l ∈ N r), h r (S ∩ N r) ^ ((d : ℝ)⁻¹) := by
            refine prod_congr rfl fun r hr => ?_
            simp only [hh'def, (Finset.mem_filter.mp hr).2, ↓reduceIte, e1 r]
          rw [q1, q2, q3, q4, q5, ← add_mul]
          apply mul_le_mul_of_nonneg_right
          · exact holder_two _ d hRl hd _ _ (fun r _ => h0 r _) (fun r _ => h0 r _)
          · exact prod_nonneg fun r _ => Real.rpow_nonneg (h0 r _) _
      _ ≤ ∏ r, (∑ T ∈ (N' r).powerset, h' r T) ^ ((d : ℝ)⁻¹) := key
      _ = ∏ r, (∑ T ∈ (N r).powerset, h r T) ^ ((d : ℝ)⁻¹) := by
          refine prod_congr rfl fun r _ => ?_
          congr 1
          by_cases hlr : l ∈ N r
          · have hNr : N r = insert l (N' r) := by
              rw [hN'def]; exact (Finset.insert_erase hlr).symm
            have hlN' : l ∉ N' r := by rw [hN'def]; exact Finset.notMem_erase l (N r)
            rw [hNr, sum_powerset_insert hlN', ← sum_add_distrib]
            refine sum_congr rfl fun T _ => ?_
            simp only [hh'def, hlr, ↓reduceIte]
          · have hNr : N' r = N r := by rw [hN'def]; exact Finset.erase_eq_of_notMem hlr
            rw [hNr]
            refine sum_congr rfl fun T _ => ?_
            simp only [hh'def, hlr, ↓reduceIte]

end P3SSSZ
