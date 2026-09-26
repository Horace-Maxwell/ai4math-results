import Mathlib
import Research.ICGEqualParityA

/-!
# Corollary A (round 4): maximal energy of `ICG(p q^m)`, `m` odd

For distinct odd primes `p, q` and odd `m`, every set `D` of proper divisors of `n = p q^m` satisfies

  `E(ICG_n(D)) ≤ E(ICG_n(D⁻))`,  `D⁻ = {p^i q^j : i + j odd}` (the anti-checkerboard),

and `2 E(ICG_n(D⁻)) = n + (3p - 4) d_m(q) - 2 (p - 2) δ_m(q)` with `d_m(q) = ‖T_m(q) s‖₁`,
`δ_m(q) = (T_m(q) s)_m`.  The energy is the genuine graph energy (`ICGBridge.energy`, the sum of
the absolute values of the Hermitian eigenvalues of the adjacency matrix), as in `ICGGeneralMain`.
-/

noncomputable section

namespace ICGEqualParity

open Finset ICGGeneral

variable {p q : ℕ}

/-! ### The anti-checkerboard set -/

/-- `D⁻ = {p^i q^j : i ≤ a, j ≤ b, i + j odd}`. -/
def DantiPQ (p q a b : ℕ) : Finset ℕ :=
  (((range (a + 1)) ×ˢ (range (b + 1))).filter (fun ij => Odd (ij.1 + ij.2))).image
    (fun ij => p ^ ij.1 * q ^ ij.2)

lemma mem_DantiPQ_iff {a b x : ℕ} :
    x ∈ DantiPQ p q a b ↔ ∃ i ≤ a, ∃ j ≤ b, Odd (i + j) ∧ p ^ i * q ^ j = x := by
  unfold DantiPQ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨hi, hj⟩, he⟩, rfl⟩
    exact ⟨i, by omega, j, by omega, he, rfl⟩
  · rintro ⟨i, hi, j, hj, he, rfl⟩
    exact ⟨i, j, ⟨⟨by omega, by omega⟩, he⟩, rfl⟩

lemma pq_mem_DantiPQ (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b c e : ℕ} (hc : c ≤ a)
    (he : e ≤ b) : p ^ c * q ^ e ∈ DantiPQ p q a b ↔ Odd (c + e) := by
  rw [mem_DantiPQ_iff]
  constructor
  · rintro ⟨i, _, j, _, hev, h⟩
    obtain ⟨rfl, rfl⟩ := (pq_inj hp hq hpq).mp h
    exact hev
  · intro hev
    exact ⟨c, hc, e, he, hev, rfl⟩

lemma DantiPQ_subset (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (hab : Even (a + b)) :
    DantiPQ p q a b ⊆ (p ^ a * q ^ b).properDivisors := by
  intro x hx
  obtain ⟨i, hi, j, hj, hodd, rfl⟩ := mem_DantiPQ_iff.mp hx
  rw [Nat.mem_properDivisors]
  have hdvd : p ^ i * q ^ j ∣ p ^ a * q ^ b := (pq_dvd_iff hp hq hpq).mpr ⟨hi, hj⟩
  have hpos : 0 < p ^ a * q ^ b := by
    have := hp.pos
    have := hq.pos
    positivity
  refine ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) ?_⟩
  intro h
  obtain ⟨rfl, rfl⟩ := (pq_inj hp hq hpq).mp h
  exact (Nat.not_even_iff_odd.mpr hodd) hab

/-! ### The two-row energy formula -/

lemma Tent_one (x : ℝ) :
    Tent x 1 0 0 = -(x - 1) ∧ Tent x 1 0 1 = x - 1 ∧ Tent x 1 1 0 = x - 1 ∧ Tent x 1 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Tent, phiX, ramX]

lemma Mentry_row0 (p q : ℝ) (m : ℕ) (Y : ℕ → ℕ → ℝ) (v : ℕ) :
    Mentry p q 1 m Y 0 v = -((p - 1) * Tv q m (w1 (Y 0) (Y 1)) v) := by
  rw [Mentry_eq]
  unfold Tv
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  obtain ⟨h00, h01, -, -⟩ := Tent_one p
  rw [h00, h01]
  unfold w1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma Mentry_row1 (p q : ℝ) (m : ℕ) (Y : ℕ → ℕ → ℝ) (v : ℕ) :
    Mentry p q 1 m Y 1 v = Tv q m (w2 (p - 1) (Y 0) (Y 1)) v := by
  rw [Mentry_eq]
  unfold Tv
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  obtain ⟨-, -, h10, h11⟩ := Tent_one p
  rw [h10, h11]
  unfold w2
  rw [Finset.mul_sum, one_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- `2 E = (p-1)‖T w1‖ + ‖T w2‖ - 2 q^m max(0, -Z_0(w2)) + p q^m` for two rows. -/
theorem two_L1mat_rows {p q : ℝ} (hp : 1 ≤ p) (hq : 1 < q) (m : ℕ) (X : ℕ → ℕ → ℝ)
    (hX : ∀ i ≤ 1, ∀ l ≤ m, X i l = 0 ∨ X i l = 1) :
    2 * L1mat p q 1 m X =
      (p - 1) * L1 q m (w1 (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) +
        L1 q m (w2 (p - 1) (fun l => 2 * X 0 l - 1) (fun l => 2 * X 1 l - 1)) -
        2 * q ^ m * max 0 (-(Zp q m (w2 (p - 1) (fun l => 2 * X 0 l - 1)
          (fun l => 2 * X 1 l - 1)) 0)) + p * q ^ m := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  set Y : ℕ → ℕ → ℝ := fun c e => 2 * X c e - 1 with hY
  have hY0 : (fun l => 2 * X 0 l - 1) = Y 0 := rfl
  have hY1 : (fun l => 2 * X 1 l - 1) = Y 1 := rfl
  rw [hY0, hY1, two_L1mat]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  -- row 0
  have hrow0 : ∑ v ∈ range (m + 1), |Mentry p q 1 m Y 0 v + Mentry p q 1 m (fun _ _ => 1) 0 v| =
      (p - 1) * L1 q m (w1 (Y 0) (Y 1)) := by
    unfold L1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_range] at hv
    rw [Mentry_ones hp0.ne' hq0.ne' 1 m (by norm_num) (by omega), if_neg (by omega), add_zero,
      Mentry_row0, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ p - 1)]
  -- row 1
  have hw2bound : ∀ l ≤ m, |w2 (p - 1) (Y 0) (Y 1) l| ≤ p := by
    intro l hl
    unfold w2
    rw [hY]
    rcases hX 0 (by norm_num) l hl with a | a <;> rcases hX 1 le_rfl l hl with b | b <;>
      simp only [a, b] <;> rw [abs_le] <;> constructor <;> linarith
  have hZ0 : |Zp q m (w2 (p - 1) (Y 0) (Y 1)) 0| ≤ p :=
    Zp_abs_le_C (by linarith) hw2bound 0 (Nat.zero_le _)
  have hrow1 : ∑ v ∈ range (m + 1), |Mentry p q 1 m Y 1 v + Mentry p q 1 m (fun _ _ => 1) 1 v| =
      L1 q m (w2 (p - 1) (Y 0) (Y 1)) -
        2 * q ^ m * max 0 (-(Zp q m (w2 (p - 1) (Y 0) (Y 1)) 0)) + p * q ^ m := by
    unfold L1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hrest : ∑ v ∈ range m, |Mentry p q 1 m Y 1 v + Mentry p q 1 m (fun _ _ => 1) 1 v| =
        ∑ v ∈ range m, |Tv q m (w2 (p - 1) (Y 0) (Y 1)) v| := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_range] at hv
      rw [Mentry_ones hp0.ne' hq0.ne' 1 m le_rfl (by omega), if_neg (by omega), add_zero,
        Mentry_row1]
    rw [hrest, Mentry_ones hp0.ne' hq0.ne' 1 m le_rfl le_rfl, if_pos ⟨rfl, rfl⟩, Mentry_row1,
      Tv_last hq0.ne', pow_one]
    set Z := Zp q m (w2 (p - 1) (Y 0) (Y 1)) 0 with hZ
    have hqm := pow_pos hq0 m
    have hnn : 0 ≤ q ^ m * Z + p * q ^ m := by
      have : -p ≤ Z := by linarith [neg_abs_le Z]
      nlinarith
    rw [abs_of_nonneg hnn, abs_mul, abs_of_pos hqm]
    rcases le_or_gt 0 Z with hz | hz
    · rw [max_eq_left (by linarith), abs_of_nonneg hz]
      ring
    · rw [max_eq_right (by linarith), abs_of_neg hz]
      ring
  rw [hrow0, hrow1]
  ring

/-! ### Corollary A -/

theorem paramOK_of_primes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) :
    ParamOK (q : ℝ) ((p : ℝ) - 1) := by
  rcases Nat.lt_or_ge q 5 with hq5 | hq5
  · -- q = 3 (q = 4 is not prime)
    have hq3' : q = 3 := by
      interval_cases q
      · rfl
      · exact absurd hq (by norm_num)
    subst hq3'
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hpq
        · exact absurd hp (by norm_num)
      · exact h
    right
    refine ⟨by norm_num, ?_⟩
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  · left
    refine ⟨by exact_mod_cast hq5, ?_⟩
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith

/-- The anti-checkerboard sign rows: `Y_{0l} = -s_l`, `Y_{1l} = s_l`. -/
lemma anti_rows (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {m : ℕ} :
    (∀ l ≤ m, 2 * (if p ^ 0 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1 = -sgnv l) ∧
      (∀ l ≤ m, 2 * (if p ^ 1 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1 = sgnv l) := by
  constructor
  · intro l hl
    unfold sgnv
    rcases Nat.even_or_odd l with he | ho
    · rw [if_neg (fun h => (Nat.not_odd_iff_even.mpr (by simpa using he))
        ((pq_mem_DantiPQ hp hq hpq (by norm_num) hl).mp h)), he.neg_one_pow]
      norm_num
    · rw [if_pos ((pq_mem_DantiPQ hp hq hpq (by norm_num) hl).mpr (by simpa using ho)),
        ho.neg_one_pow]
      norm_num
  · intro l hl
    unfold sgnv
    rcases Nat.even_or_odd l with he | ho
    · rw [if_pos ((pq_mem_DantiPQ hp hq hpq le_rfl hl).mpr (by rw [add_comm]; exact he.add_one)),
        he.neg_one_pow]
      norm_num
    · rw [if_neg (fun h => (Nat.not_odd_iff_even.mpr (by rw [add_comm]; exact ho.add_one))
        ((pq_mem_DantiPQ hp hq hpq le_rfl hl).mp h)), ho.neg_one_pow]
      norm_num

/-- **Value** of the anti-checkerboard energy: `2E = n + (3p-4) d_m(q) - 2(p-2) δ_m(q)`. -/
theorem energy_anti (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) :
    2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
        (ICGBridge.icgAdj_isHermitian _ _) =
      (p : ℝ) * (q : ℝ) ^ m + (3 * (p : ℝ) - 4) * L1 q m sgnv -
        2 * ((p : ℝ) - 2) * Tv q m sgnv m := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq2 : (2 : ℝ) < q := by linarith
  rw [energy_icgAdj_pq p q 1 m hp hq hpq]
  rw [two_L1mat_rows (by linarith) (by linarith) m _ (by intro i _ l _; split_ifs <;> simp)]
  obtain ⟨h0, h1⟩ := anti_rows hp hq hpq (m := m)
  have hw1 : L1 q m (w1 (fun l => 2 * (if p ^ 0 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)
      (fun l => 2 * (if p ^ 1 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)) =
      2 * L1 q m sgnv := by
    rw [L1_congr q m (w' := fun l => (-2) * sgnv l) (fun l hl => by unfold w1; dsimp only; rw [h0 l hl, h1 l hl]; ring),
      L1_smul]
    norm_num
  have hw2 : L1 q m (w2 ((p : ℝ) - 1)
      (fun l => 2 * (if p ^ 0 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)
      (fun l => 2 * (if p ^ 1 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)) =
      ((p : ℝ) - 2) * L1 q m sgnv := by
    rw [L1_congr q m (w' := fun l => (-((p : ℝ) - 2)) * sgnv l)
      (fun l hl => by unfold w2; dsimp only; rw [h0 l hl, h1 l hl]; ring), L1_smul, abs_neg,
      abs_of_nonneg (by linarith)]
  have hz2 : Zp q m (w2 ((p : ℝ) - 1)
      (fun l => 2 * (if p ^ 0 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)
      (fun l => 2 * (if p ^ 1 * q ^ l ∈ DantiPQ p q 1 m then (1 : ℝ) else 0) - 1)) 0 =
      -((p : ℝ) - 2) * nu q m := by
    rw [Zp_congr q m (w' := fun l => (-((p : ℝ) - 2)) * sgnv l + 0 * sgnv l)
      (fun l hl => by unfold w2; dsimp only; rw [h0 l hl, h1 l hl]; ring), Zp_linear, Zp_sgnv_zero hq2]
    ring
  rw [hw1, hw2, hz2, Tv_last (by linarith : (q : ℝ) ≠ 0), Zp_sgnv_zero hq2]
  have hnu := nu_pos hq2 m
  have hmax : max 0 (-(-((p : ℝ) - 2) * nu (q : ℝ) m)) = ((p : ℝ) - 2) * nu q m := by
    rw [max_eq_right (by nlinarith)]
    ring
  rw [hmax]
  ring

/-- **Corollary A** (maximality): for distinct odd primes `p, q`, odd `m`, and every set `D` of
proper divisors of `p q^m`, `E(ICG(p q^m, D)) ≤ E(ICG(p q^m, D⁻))`. -/
theorem energy_le_anti (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p)
    (hq3 : 3 ≤ q) (hm : Odd m) (D : Finset ℕ) (hD : D ⊆ (p ^ 1 * q ^ m).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D) (ICGBridge.icgAdj_isHermitian _ _) ≤
      ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) (DantiPQ p q 1 m))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hanti := energy_anti p q m hp hq hpq hp3 hq3
  set X : ℕ → ℕ → ℝ := fun c e => if p ^ c * q ^ e ∈ D then 1 else 0 with hX
  have hE : 2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ 1 * q ^ m) D)
      (ICGBridge.icgAdj_isHermitian _ _) = 2 * L1mat p q 1 m X := by
    rw [energy_icgAdj_pq p q 1 m hp hq hpq]
  rw [two_L1mat_rows (by linarith) (by linarith) m X (by intro i _ l _; simp only [hX]; split_ifs <;> simp)] at hE
  have hu : IsSign m (fun l => 2 * X 0 l - 1) := by
    intro l _; simp only [hX]; split_ifs
    · left; norm_num
    · right; norm_num
  have hv : IsSign m (fun l => 2 * X 1 l - 1) := by
    intro l _; simp only [hX]; split_ifs
    · left; norm_num
    · right; norm_num
  have hvm : (fun l => 2 * X 1 l - 1) m = -1 := by
    simp only [hX]
    have hnot : p ^ 1 * q ^ m ∉ D := by
      intro hmem
      exact lt_irrefl _ (Nat.mem_properDivisors.mp (hD hmem)).2
    rw [if_neg hnot]
    norm_num
  have hA := thmA_le (paramOK_of_primes hp hq hpq hp3 hq3) hm hu hv hvm
  have e1 : (3 * ((p : ℝ) - 1) - 1) = 3 * (p : ℝ) - 4 := by ring
  have e2 : ((p : ℝ) - 1 - 1) = (p : ℝ) - 2 := by ring
  rw [e1, e2] at hA
  nlinarith

end ICGEqualParity

#print axioms ICGEqualParity.energy_le_anti
#print axioms ICGEqualParity.energy_anti
#print axioms ICGEqualParity.thmA_le
