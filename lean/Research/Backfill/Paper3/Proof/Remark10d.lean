import Research.Backfill.Paper3.Proof.Tier0

/-!
# Paper 3 back-fill: Remark 10, mean and variance of `e_G(A)` (`Remark10d`)

For a `d`-regular `G` on `n` vertices, summing over all `2^n` vertex sets `A`:
`Σ_A e_G(A) = 2^n dn/8` and `Σ_A (e_G(A) - dn/8)² = 2^n dn(2d+1)/32`.
Proof with the signs `z_v(A) = ±1`, `[v ∈ A] = (1 + z_v(A))/2`:
`e_G(A) = dn/8 + (d/4) Σ_v z_v + (1/8) Σ_{u ~ v} z_u z_v` (ordered pairs), and a product of signs
sums to zero over all `A` as soon as some vertex occurs in it an odd number of times (flip that
vertex).
-/

set_option autoImplicit false

namespace P3Basic

open Finset SimpleGraph BackfillPaper3.Challenge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sign `z_v(A)`: `1` if `v ∈ A`, `-1` otherwise. -/
def zv (v : V) (A : Finset V) : ℝ := if v ∈ A then 1 else -1

omit [Fintype V] in
theorem zv_mul_self (v : V) (A : Finset V) : zv v A * zv v A = 1 := by
  unfold zv; split_ifs <;> norm_num

omit [Fintype V] in
theorem zv_symmDiff (v w : V) (A : Finset V) :
    zv v (symmDiff A {w}) = if v = w then -zv v A else zv v A := by
  unfold zv
  by_cases h : v = w
  · subst h
    by_cases hv : v ∈ A <;> simp [hv, Finset.mem_symmDiff]
  · simp [h, Finset.mem_symmDiff]

omit [Fintype V] in
theorem zv_flip_self (w : V) (A : Finset V) : zv w (symmDiff A {w}) = -zv w A := by
  rw [zv_symmDiff]
  simp

omit [Fintype V] in
theorem zv_flip_ne {v w : V} (h : v ≠ w) (A : Finset V) : zv v (symmDiff A {w}) = zv v A := by
  rw [zv_symmDiff]
  simp [h]

/-- Flipping the membership of one vertex. -/
def flipEquiv (w : V) : Finset V ≃ Finset V where
  toFun A := symmDiff A {w}
  invFun A := symmDiff A {w}
  left_inv _ := symmDiff_symmDiff_cancel_right _ _
  right_inv _ := symmDiff_symmDiff_cancel_right _ _

/-- A function of `A` that changes sign when one vertex is flipped sums to zero. -/
theorem sum_eq_zero_of_flip (f : Finset V → ℝ) (w : V) (h : ∀ A, f (symmDiff A {w}) = -f A) :
    ∑ A, f A = 0 := by
  have h1 : ∑ A, f (symmDiff A {w}) = ∑ A, f A :=
    Fintype.sum_equiv (flipEquiv w) (fun A => f (symmDiff A {w})) f (fun _ => rfl)
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith

omit [DecidableEq V] in
theorem sum_one_finset : ∑ _A : Finset V, (1 : ℝ) = 2 ^ Fintype.card V := by
  simp [Finset.card_univ, Fintype.card_finset]

theorem sum_zv (u : V) : ∑ A : Finset V, zv u A = 0 :=
  sum_eq_zero_of_flip _ u fun A => zv_flip_self u A

theorem sum_zv_mul (u w : V) :
    ∑ A : Finset V, zv u A * zv w A = if u = w then 2 ^ Fintype.card V else 0 := by
  split_ifs with h
  · subst h
    simp only [zv_mul_self]
    exact sum_one_finset
  · refine sum_eq_zero_of_flip _ u fun A => ?_
    rw [zv_flip_self, zv_flip_ne (Ne.symm h)]
    ring

theorem sum_zv_mul3 (w u v : V) (huv : u ≠ v) :
    ∑ A : Finset V, zv w A * (zv u A * zv v A) = 0 := by
  by_cases hw : w = u
  · subst hw
    refine sum_eq_zero_of_flip _ v fun A => ?_
    rw [zv_flip_ne huv, zv_flip_self]
    ring
  · refine sum_eq_zero_of_flip _ u fun A => ?_
    rw [zv_flip_ne hw, zv_flip_self, zv_flip_ne (Ne.symm huv)]
    ring

theorem sum_zv_mul4 (u v u' v' : V) (huv : u ≠ v) :
    ∑ A : Finset V, (zv u A * zv v A) * (zv u' A * zv v' A) =
      if (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) then 2 ^ Fintype.card V else 0 := by
  split_ifs with h
  · have hone : ∀ A : Finset V, (zv u A * zv v A) * (zv u' A * zv v' A) = 1 := by
      intro A
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · calc _ = (zv u' A * zv u' A) * (zv v' A * zv v' A) := by ring
          _ = 1 := by rw [zv_mul_self, zv_mul_self, one_mul]
      · calc _ = (zv v' A * zv v' A) * (zv u' A * zv u' A) := by ring
          _ = 1 := by rw [zv_mul_self, zv_mul_self, one_mul]
    simp only [hone]
    exact sum_one_finset
  · by_cases hu1 : u' = u
    · -- `v` occurs once: `u ≠ v`, `u' = u ≠ v`, `v' ≠ v`
      have hv' : v' ≠ v := fun hv => h (Or.inl ⟨hu1, hv⟩)
      have hu' : u' ≠ v := by rw [hu1]; exact huv
      refine sum_eq_zero_of_flip _ v fun A => ?_
      rw [zv_flip_ne huv, zv_flip_self, zv_flip_ne hu', zv_flip_ne hv']
      ring
    · by_cases hu2 : v' = u
      · -- `v` occurs once: `v' = u ≠ v`, `u' ≠ v`
        have hu' : u' ≠ v := fun hv => h (Or.inr ⟨hv, hu2⟩)
        have hv' : v' ≠ v := by rw [hu2]; exact huv
        refine sum_eq_zero_of_flip _ v fun A => ?_
        rw [zv_flip_ne huv, zv_flip_self, zv_flip_ne hu', zv_flip_ne hv']
        ring
      · -- `u` occurs once
        refine sum_eq_zero_of_flip _ u fun A => ?_
        rw [zv_flip_self, zv_flip_ne (Ne.symm huv), zv_flip_ne hu1, zv_flip_ne hu2]
        ring

/-- The adjacency indicator. -/
noncomputable def adjR (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  if G.Adj u v then 1 else 0

/-- `Z₂(A) = Σ_{u ~ v} z_u z_v` over ordered pairs. -/
noncomputable def Z2 (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℝ :=
  ∑ u, ∑ v, adjR G u v * (zv u A * zv v A)

omit [DecidableEq V] in
theorem sum_adjR_right (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hG : G.IsRegularOfDegree d) (u : V) : ∑ v, adjR G u v = d := by
  unfold adjR
  rw [Finset.sum_boole, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.card_neighborFinset_eq_degree, hG u]

omit [DecidableEq V] in
theorem sum_adjR_left (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hG : G.IsRegularOfDegree d) (v : V) : ∑ u, adjR G u v = d := by
  rw [← sum_adjR_right G d hG v]
  exact Finset.sum_congr rfl fun u _ => by unfold adjR; exact if_congr (G.adj_comm u v) rfl rfl

omit [DecidableEq V] in
theorem sum_sum_adjR (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hG : G.IsRegularOfDegree d) : ∑ u : V, ∑ v, adjR G u v = d * Fintype.card V := by
  simp only [sum_adjR_right G d hG, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- `e_G(A) = dn/8 + (d/4) Σ_v z_v + (1/8) Z₂(A)` for a `d`-regular `G`. -/
theorem edgesIn_eq_signs (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hG : G.IsRegularOfDegree d) (A : Finset V) :
    (edgesIn G A : ℝ) = d * Fintype.card V / 8 + d / 4 * ∑ v, zv v A + 1 / 8 * Z2 G A := by
  have h2 := two_mul_edgesIn G A
  have hx : ∀ u : V, (if u ∈ A then (1 : ℝ) else 0) = (1 + zv u A) / 2 := by
    intro u; unfold zv; split_ifs <;> norm_num
  have h3 : 2 * (edgesIn G A : ℝ) =
      ∑ u, ∑ v, adjR G u v * ((1 + zv u A) / 2) * ((1 + zv v A) / 2) := by
    have h2' : ((2 * edgesIn G A : ℕ) : ℝ) = ((#(univ.filter fun p : V × V =>
        G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) : ℕ) : ℝ) := congrArg _ h2
    rw [Finset.card_filter] at h2'
    push_cast at h2'
    rw [h2', Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [← hx u, ← hx v]
    unfold adjR
    by_cases ha : G.Adj u v <;> by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [ha, hu, hv]
  have hS1 : ∑ u : V, ∑ v, zv u A * adjR G u v = d * ∑ v, zv v A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum, sum_adjR_right G d hG, mul_comm]
  have hS2 : ∑ u : V, ∑ v, zv v A * adjR G u v = d * ∑ v, zv v A := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum, sum_adjR_left G d hG, mul_comm]
  have key : ∑ u, ∑ v, adjR G u v * ((1 + zv u A) / 2) * ((1 + zv v A) / 2) =
      1 / 4 * ((∑ u : V, ∑ v, adjR G u v) + (∑ u : V, ∑ v, zv u A * adjR G u v) +
        (∑ u : V, ∑ v, zv v A * adjR G u v) + Z2 G A) := by
    unfold Z2
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [key, sum_sum_adjR G d hG, hS1, hS2] at h3
  linarith

/-- `Σ_A Σ_v z_v(A) = 0`. -/
theorem sum_Z1 : ∑ A : Finset V, ∑ v, zv v A = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun v _ => sum_zv v

/-- `Σ_A Z₂(A) = 0`. -/
theorem sum_Z2 (G : SimpleGraph V) [DecidableRel G.Adj] : ∑ A : Finset V, Z2 G A = 0 := by
  unfold Z2
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← Finset.mul_sum]
  unfold adjR
  split_ifs with ha
  · simp [sum_zv_mul, ha.ne]
  · rw [zero_mul]

/-- `Σ_A (Σ_v z_v)² = n 2^n`. -/
theorem sum_Z1_sq : ∑ A : Finset V, (∑ v, zv v A) ^ 2 = Fintype.card V * 2 ^ Fintype.card V := by
  have h : ∀ A : Finset V, (∑ v, zv v A) ^ 2 = ∑ u, ∑ w, zv u A * zv w A := fun A => by
    rw [sq, Finset.sum_mul_sum]
  have hu : ∀ u : V, ∑ A : Finset V, ∑ w, zv u A * zv w A = 2 ^ Fintype.card V := by
    intro u
    rw [Finset.sum_comm]
    simp [sum_zv_mul]
  simp only [h]
  rw [Finset.sum_comm]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `Σ_A (Σ_w z_w) Z₂(A) = 0`. -/
theorem sum_Z1_mul_Z2 (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ A : Finset V, (∑ w, zv w A) * Z2 G A = 0 := by
  have h : ∀ A : Finset V, (∑ w, zv w A) * Z2 G A =
      ∑ w, ∑ u, ∑ v, adjR G u v * (zv w A * (zv u A * zv v A)) := by
    intro A
    unfold Z2
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← Finset.mul_sum]
  unfold adjR
  split_ifs with ha
  · rw [sum_zv_mul3 w u v ha.ne, mul_zero]
  · rw [zero_mul]

omit [DecidableEq V] in
theorem sum_comm5 {α : Type*} [Fintype α] (f : α → V → V → V → V → ℝ) :
    ∑ a, ∑ u, ∑ v, ∑ u', ∑ v', f a u v u' v' = ∑ u, ∑ v, ∑ u', ∑ v', ∑ a, f a u v u' v' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' _ => ?_
  rw [Finset.sum_comm]

/-- `Σ_A Z₂(A)² = 2 · 2^n · Σ_{u,v} [u ~ v]`. -/
theorem sum_Z2_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ A : Finset V, Z2 G A ^ 2 = 2 * 2 ^ Fintype.card V * ∑ u, ∑ v, adjR G u v := by
  have h : ∀ A : Finset V, Z2 G A ^ 2 = ∑ u, ∑ v, ∑ u', ∑ v',
      adjR G u v * adjR G u' v' * ((zv u A * zv v A) * (zv u' A * zv v' A)) := by
    intro A
    unfold Z2
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v' _ => by ring
  have hval : ∀ u v : V, ∑ u', ∑ v', ∑ A : Finset V,
      adjR G u v * adjR G u' v' * ((zv u A * zv v A) * (zv u' A * zv v' A)) =
        2 * 2 ^ Fintype.card V * adjR G u v := by
    intro u v
    by_cases ha : G.Adj u v
    · have huv : u ≠ v := ha.ne
      have hinner : ∀ u' v' : V, ∑ A : Finset V,
          adjR G u v * adjR G u' v' * ((zv u A * zv v A) * (zv u' A * zv v' A)) =
            if (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) then 2 ^ Fintype.card V else 0 := by
        intro u' v'
        rw [← Finset.mul_sum, sum_zv_mul4 u v u' v' huv]
        by_cases hc : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u)
        · have ha' : G.Adj u' v' := by
            rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ha
            · exact ha.symm
          simp [adjR, ha, ha', hc]
        · simp [hc]
      simp only [hinner]
      rw [← Fintype.sum_prod_type' (fun u' v' => if (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u)
        then (2 : ℝ) ^ Fintype.card V else 0)]
      rw [Finset.sum_eq_add_of_mem (u, v) (v, u) (Finset.mem_univ _) (Finset.mem_univ _)
        (by simp [huv])]
      · simp [adjR, ha, huv, Ne.symm huv]
        ring
      · rintro ⟨a, b⟩ _ ⟨h1, h2⟩
        have hc : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
          rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact h1 rfl
          · exact h2 rfl
        simp only [hc, ite_false]
    · have h0 : adjR G u v = 0 := by simp [adjR, ha]
      simp [h0]
  simp only [h]
  rw [sum_comm5]
  simp only [hval]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]

/-- **Remark 10** (mean and variance). -/
theorem check_Remark10d : Remark10d := by
  intro d V _ _ G _ hG
  have he := edgesIn_eq_signs G d hG
  constructor
  · simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Z1, sum_Z2, Finset.sum_const,
      Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
    push_cast
    ring
  · have hsq : ∀ A : Finset V, ((edgesIn G A : ℝ) - d * Fintype.card V / 8) ^ 2 =
        (d : ℝ) ^ 2 / 16 * (∑ v, zv v A) ^ 2 + d / 16 * ((∑ v, zv v A) * Z2 G A) +
          1 / 64 * Z2 G A ^ 2 := by
      intro A
      rw [he A]
      ring
    simp only [hsq, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Z1_sq, sum_Z1_mul_Z2, sum_Z2_sq,
      sum_sum_adjR G d hG]
    ring

#print axioms check_Remark10d

end P3Basic
