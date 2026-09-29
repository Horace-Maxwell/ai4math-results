import Research.Backfill.Paper3.Proof.Tier0

/-!
# The polynomial `P_d` as a real function

`P_d(q) = Σ_{a,b ≤ d} C(d,a) C(d,b) q^{ab}` (`Pf`), with `evalR (Pd d) = Pf d`; sums over the
vertex sets of `K_{d,d}`; `P_d ≥ 1`, `P_d(1) = 4^d`, `P_d(q) ≥ q^{d²}`, monotonicity, continuity,
the derivative with `P_d'(1) = (d 2^{d-1})²`, the Jensen bound `P_d(q) ≥ 4^d q^{d²/4}`, and the
monotonicity of the tilted mean `q P_d'(q) / P_d(q)` (symmetrised double sums).
-/

set_option autoImplicit false

namespace P3CD

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

/-- The weight `C(d,a) C(d,b)` of the monomial `q^{ab}` in `P_d`. -/
noncomputable def wt (d a b : ℕ) : ℝ := (d.choose a : ℝ) * (d.choose b : ℝ)

theorem wt_nonneg (d a b : ℕ) : 0 ≤ wt d a b := by unfold wt; positivity

/-- `P_d(q)` as an explicit double sum. -/
noncomputable def Pf (d : ℕ) (q : ℝ) : ℝ :=
  ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * q ^ (a * b)

theorem evalR_Pd (d : ℕ) (q : ℝ) : evalR (Pd d) q = Pf d q := by
  unfold evalR Pd Pf wt
  simp [map_sum]

/-- `P_G(q) = Σ_A q^{e_G(A)}`. -/
theorem evalR_edgePoly {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (q : ℝ) : evalR (edgePoly G) q = ∑ A : Finset V, q ^ edgesIn G A := by
  unfold evalR edgePoly
  simp [map_sum]

/-- `Σ_{S ⊆ [d]} g(|S|) = Σ_a C(d,a) g(a)`. -/
theorem sum_finset_fin_card (d : ℕ) (g : ℕ → ℝ) :
    ∑ S : Finset (Fin d), g #S = ∑ a ∈ range (d + 1), (d.choose a : ℝ) * g a := by
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- Sums over the vertex sets of `K_{d,d}` of a function of the number of spanned edges. -/
theorem sum_Kdd (d : ℕ) (f : ℕ → ℝ) :
    ∑ A : Finset (Fin d ⊕ Fin d), f (edgesIn (Kdd d) A) =
      ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * f (a * b) := by
  have h1 : ∑ A : Finset (Fin d ⊕ Fin d), f (edgesIn (Kdd d) A) =
      ∑ S : Finset (Fin d), ∑ T : Finset (Fin d), f (#S * #T) := by
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (finsetSumEquiv (Fin d) (Fin d)) _ _ (fun A => ?_)
    have := edgesIn_Kdd d A.toLeft A.toRight
    rw [Finset.toLeft_disjSum_toRight] at this
    simp [finsetSumEquiv, this]
  rw [h1]
  have h2 : ∀ S : Finset (Fin d), ∑ T : Finset (Fin d), f (#S * #T) =
      ∑ b ∈ range (d + 1), (d.choose b : ℝ) * f (#S * b) :=
    fun S => sum_finset_fin_card d (fun k => f (#S * k))
  simp only [h2]
  rw [sum_finset_fin_card d (fun k => ∑ b ∈ range (d + 1), (d.choose b : ℝ) * f (k * b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold wt
  ring

theorem Pf_eq_sum_Kdd (d : ℕ) (q : ℝ) :
    Pf d q = ∑ A : Finset (Fin d ⊕ Fin d), q ^ edgesIn (Kdd d) A :=
  (sum_Kdd d (fun s => q ^ s)).symm

theorem sum_choose_real (d : ℕ) : ∑ a ∈ range (d + 1), (d.choose a : ℝ) = 2 ^ d := by
  exact_mod_cast Nat.sum_range_choose d

theorem four_pow_eq (d : ℕ) : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by
  rw [← mul_pow]; norm_num

/-- `Σ_{a,b} C(d,a) C(d,b) = 4^d`. -/
theorem sum_wt (d : ℕ) : ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b = 4 ^ d := by
  unfold wt
  rw [← Finset.sum_mul_sum, sum_choose_real, four_pow_eq]

/-- `Σ_{a,b} C(d,a) C(d,b) ab = (d 2^{d-1})²`. -/
theorem sum_wt_mul (d : ℕ) :
    ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * ((a * b : ℕ) : ℝ) =
      ((d : ℝ) * 2 ^ (d - 1)) ^ 2 := by
  have h : ∑ a ∈ range (d + 1), (d.choose a : ℝ) * a = d * 2 ^ (d - 1) := by
    have := Nat.sum_range_mul_choose d
    have h' : ∑ a ∈ range (d + 1), ((a * d.choose a : ℕ) : ℝ) = ((d * 2 ^ (d - 1) : ℕ) : ℝ) := by
      rw [← this, Nat.cast_sum]
    push_cast at h'
    rw [← h']
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [sq, ← h, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold wt
  push_cast
  ring

/-- `(d 2^{d-1})² = 4^d · d²/4` for `d ≥ 1`. -/
theorem mean_eq (d : ℕ) (hd : 1 ≤ d) : ((d : ℝ) * 2 ^ (d - 1)) ^ 2 = 4 ^ d * ((d : ℝ) ^ 2 / 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [four_pow_eq, Nat.add_sub_cancel]
  push_cast
  ring

theorem Pf_one (d : ℕ) : Pf d 1 = 4 ^ d := by
  simp only [Pf, one_pow, mul_one]
  exact sum_wt d

theorem Pf_term_nonneg (d a b : ℕ) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ wt d a b * q ^ (a * b) :=
  mul_nonneg (wt_nonneg d a b) (pow_nonneg hq _)

/-- A single term of the double sum is at most `P_d(q)`. -/
theorem term_le_Pf (d : ℕ) {q : ℝ} (hq : 0 ≤ q) {a b : ℕ} (ha : a ≤ d) (hb : b ≤ d) :
    wt d a b * q ^ (a * b) ≤ Pf d q := by
  unfold Pf
  calc wt d a b * q ^ (a * b) ≤ ∑ b' ∈ range (d + 1), wt d a b' * q ^ (a * b') :=
        Finset.single_le_sum (f := fun b' => wt d a b' * q ^ (a * b'))
          (fun b' _ => Pf_term_nonneg d a b' hq) (by simp; omega)
    _ ≤ ∑ a' ∈ range (d + 1), ∑ b' ∈ range (d + 1), wt d a' b' * q ^ (a' * b') :=
        Finset.single_le_sum (f := fun a' => ∑ b' ∈ range (d + 1), wt d a' b' * q ^ (a' * b'))
          (fun a' _ => Finset.sum_nonneg fun b' _ => Pf_term_nonneg d a' b' hq) (by simp; omega)

theorem one_le_Pf (d : ℕ) {q : ℝ} (hq : 0 ≤ q) : 1 ≤ Pf d q := by
  have h := term_le_Pf d hq (a := 0) (b := 0) (Nat.zero_le _) (Nat.zero_le _)
  simpa [wt] using h

theorem Pf_pos (d : ℕ) {q : ℝ} (hq : 0 ≤ q) : 0 < Pf d q :=
  lt_of_lt_of_le one_pos (one_le_Pf d hq)

theorem pow_le_Pf (d : ℕ) {q : ℝ} (hq : 0 ≤ q) : q ^ (d ^ 2) ≤ Pf d q := by
  have h := term_le_Pf d hq (a := d) (b := d) le_rfl le_rfl
  simpa [wt, sq] using h

theorem Pf_mono (d : ℕ) {q q' : ℝ} (hq : 0 ≤ q) (hqq' : q ≤ q') : Pf d q ≤ Pf d q' :=
  Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqq' _) (wt_nonneg d a b)

theorem Pf_le_four_pow (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Pf d q ≤ 4 ^ d :=
  (Pf_mono d hq0 hq1).trans_eq (Pf_one d)

theorem continuous_Pf (d : ℕ) : Continuous (Pf d) := by
  unfold Pf
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul (continuous_pow _)

/-- The derivative `P_d'(q) = Σ C(d,a) C(d,b) ab q^{ab-1}`. -/
noncomputable def dPf (d : ℕ) (q : ℝ) : ℝ :=
  ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * (((a * b : ℕ) : ℝ) * q ^ (a * b - 1))

theorem hasDerivAt_Pf (d : ℕ) (q : ℝ) : HasDerivAt (Pf d) (dPf d q) q := by
  unfold Pf dPf
  exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
    (hasDerivAt_pow (a * b) q).const_mul (wt d a b)

/-- `q P_d'(q) = Σ C(d,a) C(d,b) ab q^{ab}`. -/
theorem mul_dPf (d : ℕ) (q : ℝ) :
    q * dPf d q =
      ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * (((a * b : ℕ) : ℝ) * q ^ (a * b)) := by
  unfold dPf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases Nat.eq_zero_or_pos (a * b) with h | h
  · simp [h]
  · have : q ^ (a * b) = q * q ^ (a * b - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    ring

theorem dPf_one (d : ℕ) : dPf d 1 = ((d : ℝ) * 2 ^ (d - 1)) ^ 2 := by
  simp only [dPf, one_pow, mul_one]
  exact sum_wt_mul d

/-- `P_d'(1) / P_d(1) = d²/4` (the mean of `ξ`). -/
theorem dPf_div_Pf_one (d : ℕ) (hd : 1 ≤ d) : dPf d 1 / Pf d 1 = (d : ℝ) ^ 2 / 4 := by
  rw [dPf_one, Pf_one, mean_eq d hd]
  field_simp

/-! ### Jensen: `P_d(q) ≥ 4^d q^{d²/4}` -/

theorem sum_product_eq (d : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ range (d + 1) ×ˢ range (d + 1), F i.1 i.2 =
      ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), F a b :=
  Finset.sum_product _ _ _

theorem Pf_ge_jensen (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 0 < q) :
    4 ^ d * q ^ ((d : ℝ) ^ 2 / 4) ≤ Pf d q := by
  set t := range (d + 1) ×ˢ range (d + 1)
  set w : ℕ × ℕ → ℝ := fun i => wt d i.1 i.2 / 4 ^ d
  set p : ℕ × ℕ → ℝ := fun i => ((i.1 * i.2 : ℕ) : ℝ) * Real.log q
  have h4 : (0 : ℝ) < 4 ^ d := by positivity
  have hw0 : ∀ i ∈ t, 0 ≤ w i := fun i _ => div_nonneg (wt_nonneg _ _ _) h4.le
  have hw1 : ∑ i ∈ t, w i = 1 := by
    simp only [w, t]
    rw [← Finset.sum_div, sum_product_eq d (fun a b => wt d a b), sum_wt, div_self h4.ne']
  have hJ := convexOn_exp.map_sum_le hw0 hw1 (fun i _ => Set.mem_univ (p i))
  have hL : ∑ i ∈ t, w i • p i = Real.log q * ((d : ℝ) ^ 2 / 4) := by
    simp only [w, p, t, smul_eq_mul]
    rw [sum_product_eq d (fun a b => wt d a b / 4 ^ d * (((a * b : ℕ) : ℝ) * Real.log q))]
    have : ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b / 4 ^ d * (((a * b : ℕ) : ℝ) *
        Real.log q) = (∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1), wt d a b * ((a * b : ℕ) : ℝ)) *
          Real.log q / 4 ^ d := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, sum_wt_mul, mean_eq d hd]
    field_simp
  have hR : ∑ i ∈ t, w i • Real.exp (p i) = Pf d q / 4 ^ d := by
    simp only [w, p, t, smul_eq_mul]
    rw [sum_product_eq d (fun a b => wt d a b / 4 ^ d * Real.exp (((a * b : ℕ) : ℝ) *
      Real.log q)), Pf, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.exp_nat_mul, Real.exp_log hq]
    ring
  rw [hL, hR, ← Real.rpow_def_of_pos hq] at hJ
  rw [le_div_iff₀ h4] at hJ
  linarith

/-! ### The tilted mean is monotone -/

theorem tilt_key {ι : Type*} (s : ι → ℕ) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ ≤ q₂) (i j : ι) :
    0 ≤ ((s i : ℝ) - s j) * (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j) := by
  rcases le_total (s j) (s i) with h | h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    have e : q₂ ^ (s j + k) * q₁ ^ s j - q₁ ^ (s j + k) * q₂ ^ s j =
        (q₁ ^ s j * q₂ ^ s j) * (q₂ ^ k - q₁ ^ k) := by ring
    rw [e]
    push_cast
    apply mul_nonneg (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
    exact mul_nonneg (mul_nonneg (pow_nonneg h1.le _) (pow_nonneg (h1.le.trans h12) _))
      (sub_nonneg.2 (pow_le_pow_left₀ h1.le h12 k))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    have e : q₂ ^ s i * q₁ ^ (s i + k) - q₁ ^ s i * q₂ ^ (s i + k) =
        -((q₁ ^ s i * q₂ ^ s i) * (q₂ ^ k - q₁ ^ k)) := by ring
    rw [e]
    push_cast
    have : 0 ≤ (q₁ ^ s i * q₂ ^ s i) * (q₂ ^ k - q₁ ^ k) :=
      mul_nonneg (mul_nonneg (pow_nonneg h1.le _) (pow_nonneg (h1.le.trans h12) _))
        (sub_nonneg.2 (pow_le_pow_left₀ h1.le h12 k))
    have hk0 := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith

theorem tilt_key_strict {ι : Type*} (s : ι → ℕ) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ < q₂)
    {i j : ι} (hs : s j < s i) :
    0 < ((s i : ℝ) - s j) * (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hs
  rw [hk]
  have e : q₂ ^ (s j + k + 1) * q₁ ^ s j - q₁ ^ (s j + k + 1) * q₂ ^ s j =
      (q₁ ^ s j * q₂ ^ s j) * (q₂ ^ (k + 1) - q₁ ^ (k + 1)) := by ring
  rw [e]
  push_cast
  apply mul_pos (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  exact mul_pos (mul_pos (pow_pos h1 _) (pow_pos (h1.trans h12) _))
    (sub_pos.2 (pow_lt_pow_left₀ h12 h1.le (Nat.succ_ne_zero k)))

/-- Symmetrisation: `N(q₂) P(q₁) - N(q₁) P(q₂) = ½ Σ_{i,j} w_i w_j (s_i - s_j)(q₂^{s_i} q₁^{s_j} -
q₁^{s_i} q₂^{s_j})`, in the form `2 (N(q₂) P(q₁) - N(q₁) P(q₂)) = Σ_{i,j} (…)`. -/
theorem tilt_identity {ι : Type*} (t : Finset ι) (w : ι → ℝ) (s : ι → ℕ) (q₁ q₂ : ℝ) :
    2 * ((∑ i ∈ t, w i * (s i * q₂ ^ s i)) * (∑ j ∈ t, w j * q₁ ^ s j) -
      (∑ i ∈ t, w i * (s i * q₁ ^ s i)) * (∑ j ∈ t, w j * q₂ ^ s j)) =
    ∑ i ∈ t, ∑ j ∈ t, w i * w j * (((s i : ℝ) - s j) *
      (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j)) := by
  set F : ι → ι → ℝ := fun i j => w i * w j * (s i * (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j))
  have hX : (∑ i ∈ t, w i * (s i * q₂ ^ s i)) * (∑ j ∈ t, w j * q₁ ^ s j) -
      (∑ i ∈ t, w i * (s i * q₁ ^ s i)) * (∑ j ∈ t, w j * q₂ ^ s j) =
      ∑ i ∈ t, ∑ j ∈ t, F i j := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [F]
    ring
  have hswap : ∑ i ∈ t, ∑ j ∈ t, F i j = ∑ i ∈ t, ∑ j ∈ t, F j i := Finset.sum_comm
  rw [hX, two_mul]
  nth_rewrite 2 [hswap]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [F]
  ring

theorem tilt_mono {ι : Type*} (t : Finset ι) (w : ι → ℝ) (s : ι → ℕ) (hw : ∀ i ∈ t, 0 ≤ w i)
    {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ ≤ q₂) :
    (∑ i ∈ t, w i * (s i * q₁ ^ s i)) * (∑ j ∈ t, w j * q₂ ^ s j) ≤
      (∑ i ∈ t, w i * (s i * q₂ ^ s i)) * (∑ j ∈ t, w j * q₁ ^ s j) := by
  have h := tilt_identity t w s q₁ q₂
  have hpos : 0 ≤ ∑ i ∈ t, ∑ j ∈ t, w i * w j * (((s i : ℝ) - s j) *
      (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j)) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (tilt_key s h1 h12 i j)
  linarith

theorem tilt_strict {ι : Type*} (t : Finset ι) (w : ι → ℝ) (s : ι → ℕ) (hw : ∀ i ∈ t, 0 ≤ w i)
    {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ < q₂) {i₀ j₀ : ι} (hi₀ : i₀ ∈ t) (hj₀ : j₀ ∈ t)
    (hwi : 0 < w i₀) (hwj : 0 < w j₀) (hs : s j₀ < s i₀) :
    (∑ i ∈ t, w i * (s i * q₁ ^ s i)) * (∑ j ∈ t, w j * q₂ ^ s j) <
      (∑ i ∈ t, w i * (s i * q₂ ^ s i)) * (∑ j ∈ t, w j * q₁ ^ s j) := by
  have h := tilt_identity t w s q₁ q₂
  set G : ι → ι → ℝ := fun i j => w i * w j * (((s i : ℝ) - s j) *
      (q₂ ^ s i * q₁ ^ s j - q₁ ^ s i * q₂ ^ s j))
  have hG : ∀ i ∈ t, ∀ j ∈ t, 0 ≤ G i j := fun i hi j hj =>
    mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (tilt_key s h1 h12.le i j)
  have hG0 : 0 < G i₀ j₀ := mul_pos (mul_pos hwi hwj) (tilt_key_strict s h1 h12 hs)
  have hpos : 0 < ∑ i ∈ t, ∑ j ∈ t, G i j := by
    apply Finset.sum_pos' (fun i hi => Finset.sum_nonneg fun j hj => hG i hi j hj)
    exact ⟨i₀, hi₀, Finset.sum_pos' (fun j hj => hG i₀ hi₀ j hj) ⟨j₀, hj₀, hG0⟩⟩
  linarith

/-- The tilted mean `μ(q) = q P_d'(q) / P_d(q)`. -/
noncomputable def tmean (d : ℕ) (q : ℝ) : ℝ := q * dPf d q / Pf d q

theorem Pf_eq_sum_product (d : ℕ) (q : ℝ) :
    Pf d q = ∑ i ∈ range (d + 1) ×ˢ range (d + 1), wt d i.1 i.2 * q ^ (i.1 * i.2) :=
  (sum_product_eq d (fun a b => wt d a b * q ^ (a * b))).symm

theorem mul_dPf_eq_sum_product (d : ℕ) (q : ℝ) :
    q * dPf d q = ∑ i ∈ range (d + 1) ×ˢ range (d + 1),
      wt d i.1 i.2 * (((i.1 * i.2 : ℕ) : ℝ) * q ^ (i.1 * i.2)) := by
  rw [mul_dPf]
  exact (sum_product_eq d (fun a b => wt d a b * (((a * b : ℕ) : ℝ) * q ^ (a * b)))).symm

theorem tmean_mono (d : ℕ) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ ≤ q₂) :
    tmean d q₁ ≤ tmean d q₂ := by
  unfold tmean
  rw [div_le_div_iff₀ (Pf_pos d h1.le) (Pf_pos d (h1.le.trans h12)), mul_dPf_eq_sum_product d q₁,
    mul_dPf_eq_sum_product d q₂, Pf_eq_sum_product d q₁, Pf_eq_sum_product d q₂]
  exact tilt_mono (range (d + 1) ×ˢ range (d + 1)) (fun i : ℕ × ℕ => wt d i.1 i.2)
    (fun i : ℕ × ℕ => i.1 * i.2) (fun i _ => wt_nonneg _ _ _) h1 h12

theorem tmean_strict (d : ℕ) (hd : 1 ≤ d) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h12 : q₁ < q₂) :
    tmean d q₁ < tmean d q₂ := by
  unfold tmean
  rw [div_lt_div_iff₀ (Pf_pos d h1.le) (Pf_pos d (h1.le.trans h12.le)),
    mul_dPf_eq_sum_product d q₁, mul_dPf_eq_sum_product d q₂, Pf_eq_sum_product d q₁,
    Pf_eq_sum_product d q₂]
  have hmem : ∀ a ∈ ({0, d} : Finset ℕ), (a, a) ∈ range (d + 1) ×ˢ range (d + 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp
  refine tilt_strict (range (d + 1) ×ˢ range (d + 1)) (fun i : ℕ × ℕ => wt d i.1 i.2)
    (fun i : ℕ × ℕ => i.1 * i.2) (fun i _ => wt_nonneg _ _ _) h1 h12 (i₀ := (d, d)) (j₀ := (0, 0))
    (hmem d (by simp))
    (hmem 0 (by simp)) (by simp [wt]) (by simp [wt]) ?_
  simp only [mul_zero]
  exact Nat.mul_pos hd hd

theorem tmean_one (d : ℕ) (hd : 1 ≤ d) : tmean d 1 = (d : ℝ) ^ 2 / 4 := by
  unfold tmean
  rw [one_mul]
  exact dPf_div_Pf_one d hd

end P3CD
