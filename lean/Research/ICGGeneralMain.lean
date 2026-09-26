import Mathlib
import Research.ICGGeneralBridge

/-!
# The checkerboard maximises the energy of `ICG(p^a q^b)` when `a + b` is odd

Main results (all about the genuine graph energy `ICGBridge.energy (ICGBridge.icgAdj n D) _`,
i.e. the sum of the absolute values of the Hermitian eigenvalues of the adjacency matrix):

* `checkerboard_unique_max` : for primes `p ≥ 5`, `q ≥ 3`, `p ≠ q`, exponents with `a + b` odd,
  and every `D ⊆ properDivisors (p^a q^b)` with `D ≠ D* = {p^i q^j : i + j even}`,
  `energy(ICG(p^a q^b, D)) < energy(ICG(p^a q^b, D*))`.
* `energy_DstarPQ` : `2 · energy(ICG(p^a q^b, D*)) = p^a q^b + d_a(p) d_b(q)`,
  `d_m(x) = ‖T_m(x) s‖₁`.
* `jiang_yang_q3` : the case `q = 3`, `n = p^(2r) 3^(2s+1)` (Jiang–Yang Theorem A for `q = 3`).
-/

noncomputable section

namespace ICGGeneral

open Finset

variable {p q : ℕ}

/-! ### The checkerboard set -/

/-- The checkerboard connection set `D* = {p^i q^j : i ≤ a, j ≤ b, i + j even}`. -/
def DstarPQ (p q a b : ℕ) : Finset ℕ :=
  (((range (a + 1)) ×ˢ (range (b + 1))).filter (fun ij => Even (ij.1 + ij.2))).image
    (fun ij => p ^ ij.1 * q ^ ij.2)

lemma mem_DstarPQ_iff {a b x : ℕ} :
    x ∈ DstarPQ p q a b ↔ ∃ i ≤ a, ∃ j ≤ b, Even (i + j) ∧ p ^ i * q ^ j = x := by
  unfold DstarPQ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨hi, hj⟩, he⟩, rfl⟩
    exact ⟨i, by omega, j, by omega, he, rfl⟩
  · rintro ⟨i, hi, j, hj, he, rfl⟩
    exact ⟨i, j, ⟨⟨by omega, by omega⟩, he⟩, rfl⟩

lemma pq_mem_DstarPQ (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b c e : ℕ} (hc : c ≤ a)
    (he : e ≤ b) : p ^ c * q ^ e ∈ DstarPQ p q a b ↔ Even (c + e) := by
  rw [mem_DstarPQ_iff]
  constructor
  · rintro ⟨i, _, j, _, hev, h⟩
    obtain ⟨rfl, rfl⟩ := (pq_inj hp hq hpq).mp h
    exact hev
  · intro hev
    exact ⟨c, hc, e, he, hev, rfl⟩

lemma DstarPQ_subset (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (hab : Odd (a + b)) :
    DstarPQ p q a b ⊆ (p ^ a * q ^ b).properDivisors := by
  intro x hx
  obtain ⟨i, hi, j, hj, hev, rfl⟩ := mem_DstarPQ_iff.mp hx
  rw [Nat.mem_properDivisors]
  have hdvd : p ^ i * q ^ j ∣ p ^ a * q ^ b := (pq_dvd_iff hp hq hpq).mpr ⟨hi, hj⟩
  have hpos : 0 < p ^ a * q ^ b := by
    have := hp.pos
    have := hq.pos
    positivity
  refine ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) ?_⟩
  intro h
  obtain ⟨rfl, rfl⟩ := (pq_inj hp hq hpq).mp h
  exact (Nat.not_even_iff_odd.mpr hab) hev

/-! ### The `Y = 2X - J` reduction -/

lemma sgnv_mul (c e : ℕ) : sgnv c * sgnv e = if Even (c + e) then 1 else -1 := by
  unfold sgnv
  rw [← pow_add]
  rcases Nat.even_or_odd (c + e) with h | h
  · rw [if_pos h, h.neg_one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]

lemma Mentry_lin (p q : ℝ) (a b : ℕ) (X : ℕ → ℕ → ℝ) (α β : ℝ) (u v : ℕ) :
    Mentry p q a b (fun c e => α * X c e + β) u v =
      α * Mentry p q a b X u v + β * Mentry p q a b (fun _ _ => 1) u v := by
  unfold Mentry
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma Mentry_ones {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (a b : ℕ) {u v : ℕ} (hu : u ≤ a)
    (hv : v ≤ b) :
    Mentry p q a b (fun _ _ => 1) u v = if a = u ∧ b = v then p ^ a * q ^ b else 0 := by
  rw [Mentry_prod p q a b (e := fun _ => 1) (f := fun _ => 1) (fun _ _ _ _ => by ring),
    Tv_one hp a u hu, Tv_one hq b v hv]
  by_cases h1 : u = a
  · by_cases h2 : v = b
    · rw [if_pos h1, if_pos h2, if_pos (show a = u ∧ b = v from ⟨h1.symm, h2.symm⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (show ¬ (a = u ∧ b = v) from fun h => h2 h.2.symm),
        mul_zero]
  · rw [if_neg h1, if_neg (show ¬ (a = u ∧ b = v) from fun h => h1 h.1.symm), zero_mul]

lemma two_L1mat (p q : ℝ) (a b : ℕ) (X : ℕ → ℕ → ℝ) :
    2 * L1mat p q a b X = ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
      |Mentry p q a b (fun c e => 2 * X c e - 1) u v + Mentry p q a b (fun _ _ => 1) u v| := by
  unfold L1mat
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have h := Mentry_lin p q a b X 2 (-1) u v
  have e : (fun c e => 2 * X c e + -1) = (fun c e => 2 * X c e - 1) := by
    funext c e
    ring
  rw [e] at h
  rw [h, show 2 * Mentry p q a b X u v + -1 * Mentry p q a b (fun _ _ => 1) u v +
      Mentry p q a b (fun _ _ => 1) u v = 2 * Mentry p q a b X u v by ring, abs_mul, abs_two]

lemma sum_corner {p q : ℝ} (a b : ℕ) :
    ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
      (if a = u ∧ b = v then p ^ a * q ^ b else 0) = p ^ a * q ^ b :=
  double_sum_ite (F := fun _ _ => p ^ a * q ^ b) (by omega) (by omega)

/-- `2 ‖T X Tᵀ‖₁ ≤ ‖T Y Tᵀ‖₁ + n` with `Y = 2X - J`. -/
lemma two_L1mat_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (a b : ℕ) (X : ℕ → ℕ → ℝ) :
    2 * L1mat p q a b X ≤ L1mat p q a b (fun c e => 2 * X c e - 1) + p ^ a * q ^ b := by
  rw [two_L1mat]
  have hterm : ∀ u ∈ range (a + 1), ∀ v ∈ range (b + 1),
      |Mentry p q a b (fun c e => 2 * X c e - 1) u v + Mentry p q a b (fun _ _ => 1) u v| ≤
        |Mentry p q a b (fun c e => 2 * X c e - 1) u v| +
          (if a = u ∧ b = v then p ^ a * q ^ b else 0) := by
    intro u hu v hv
    rw [Finset.mem_range] at hu hv
    rw [Mentry_ones hp.ne' hq.ne' a b (by omega) (by omega)]
    split_ifs
    · have hpos : (0 : ℝ) < p ^ a * q ^ b := by positivity
      calc _ ≤ _ := abs_add_le _ _
        _ = _ := by rw [abs_of_pos hpos]
    · rw [add_zero, add_zero]
  calc ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        |Mentry p q a b (fun c e => 2 * X c e - 1) u v + Mentry p q a b (fun _ _ => 1) u v|
      ≤ ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        (|Mentry p q a b (fun c e => 2 * X c e - 1) u v| +
          (if a = u ∧ b = v then p ^ a * q ^ b else 0)) :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hterm u hu v hv))
    _ = L1mat p q a b (fun c e => 2 * X c e - 1) + p ^ a * q ^ b := by
        simp only [Finset.sum_add_distrib]
        rw [sum_corner]
        rfl

/-! ### Energy of the checkerboard -/

lemma Xstar_sign (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} :
    ∀ c ≤ a, ∀ e ≤ b,
      2 * (if p ^ c * q ^ e ∈ DstarPQ p q a b then (1 : ℝ) else 0) - 1 = sgnv c * sgnv e := by
  intro c hc e he
  rw [sgnv_mul]
  by_cases h : Even (c + e)
  · rw [if_pos ((pq_mem_DstarPQ hp hq hpq hc he).mpr h), if_pos h]
    norm_num
  · rw [if_neg (fun h' => h ((pq_mem_DstarPQ hp hq hpq hc he).mp h')), if_neg h]
    norm_num

/-- **Energy of the checkerboard**: `2 E(D*) = p^a q^b + d_a(p) d_b(q)`. -/
theorem energy_DstarPQ (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q)
    (a b : ℕ) :
    2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (DstarPQ p q a b))
        (ICGBridge.icgAdj_isHermitian _ _) =
      (p : ℝ) ^ a * (q : ℝ) ^ b + L1 p a sgnv * L1 q b sgnv := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  rw [energy_icgAdj_pq p q a b hp hq hpq, two_L1mat]
  have hY := Xstar_sign hp hq hpq (a := a) (b := b)
  have hM : ∀ u v, Mentry p q a b
      (fun c e => 2 * (if p ^ c * q ^ e ∈ DstarPQ p q a b then (1 : ℝ) else 0) - 1) u v =
        Tv p a sgnv u * Tv q b sgnv v := fun u v => Mentry_prod p q a b hY u v
  have hterm : ∀ u ∈ range (a + 1), ∀ v ∈ range (b + 1),
      |Mentry p q a b
          (fun c e => 2 * (if p ^ c * q ^ e ∈ DstarPQ p q a b then (1 : ℝ) else 0) - 1) u v +
        Mentry p q a b (fun _ _ => 1) u v| =
      |Tv p a sgnv u * Tv q b sgnv v| + (if a = u ∧ b = v then (p : ℝ) ^ a * (q : ℝ) ^ b else 0) := by
    intro u hu v hv
    rw [Finset.mem_range] at hu hv
    rw [hM, Mentry_ones hp0.ne' hq0.ne' a b (by omega) (by omega)]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have h1 := Tv_sgnv_last_pos hpR a
      have h2 := Tv_sgnv_last_pos hqR b
      have hpos : (0 : ℝ) < (p : ℝ) ^ a * (q : ℝ) ^ b := by positivity
      rw [abs_of_pos (add_pos (mul_pos h1 h2) hpos), abs_of_pos (mul_pos h1 h2)]
    · rw [add_zero, add_zero]
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => hterm u hu v hv))]
  simp only [Finset.sum_add_distrib]
  rw [sum_corner]
  have hprod : ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1), |Tv p a sgnv u * Tv q b sgnv v| =
      L1 p a sgnv * L1 q b sgnv := by
    unfold L1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [abs_mul]
  rw [hprod]
  ring

/-! ### Uniqueness -/

/-- **The checkerboard is the unique maximiser** (`a + b` odd, `p ≥ 5`, `q ≥ 3`). -/
theorem checkerboard_unique_max (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q) (hab : Odd (a + b)) (D : Finset ℕ)
    (hD : D ⊆ (p ^ a * q ^ b).properDivisors) (hne : D ≠ DstarPQ p q a b) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (DstarPQ p q a b))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set X : ℕ → ℕ → ℝ := fun c e => if p ^ c * q ^ e ∈ D then 1 else 0 with hX
  have hYsign : ∀ i ≤ a, IsSign b (fun l => 2 * X i l - 1) := by
    intro i _ l _
    simp only [hX]
    split_ifs
    · left; norm_num
    · right; norm_num
  have hE := energy_icgAdj_pq p q a b hp hq hpq D
  have hEstar := energy_DstarPQ hp hq hpq (by omega) hq3 a b
  have hup := two_L1mat_le hp0 hq0 a b X
  have h5 := thm5_le hpR hqR hYsign
  by_contra hcon0
  have hcon := not_lt.mp hcon0
  rw [hE] at hcon
  have hNcast : ((p ^ a * q ^ b : ℕ) : ℝ) = (p : ℝ) ^ a * (q : ℝ) ^ b := by push_cast; ring
  have hge : L1mat p q a b (fun c e => 2 * X c e - 1) = L1 p a sgnv * L1 q b sgnv := by
    have : L1 p a sgnv * L1 q b sgnv ≤ L1mat p q a b (fun c e => 2 * X c e - 1) := by
      linarith
    linarith
  have hNotN : p ^ a * q ^ b ∉ D := by
    intro hmem
    exact lt_irrefl _ (Nat.mem_properDivisors.mp (hD hmem)).2
  have hcorner : 2 * X a b - 1 = -1 := by
    simp only [hX, if_neg hNotN]
    norm_num
  have hsab : sgnv a * sgnv b = -1 := by
    rw [sgnv_mul, if_neg (Nat.not_even_iff_odd.mpr hab)]
  rcases thm5_eq hpR hqR hYsign hge with hY | hY
  · apply hne
    have hiff : ∀ c ≤ a, ∀ e ≤ b, p ^ c * q ^ e ∈ D ↔ Even (c + e) := by
      intro c hc e he
      have h := hY c hc e he
      simp only [hX] at h
      rw [sgnv_mul] at h
      constructor
      · intro hm
        rw [if_pos hm] at h
        by_contra hev
        rw [if_neg hev] at h
        norm_num at h
      · intro hev
        rw [if_pos hev] at h
        by_contra hm
        rw [if_neg hm] at h
        norm_num at h
    ext x
    constructor
    · intro hx
      have hdvd := (Nat.mem_properDivisors.mp (hD hx)).1
      obtain ⟨c, hc, e, he, rfl⟩ := pq_dvd_rep hp hq hdvd
      exact (pq_mem_DstarPQ hp hq hpq hc he).mpr ((hiff c hc e he).mp hx)
    · intro hx
      obtain ⟨i, hi, j, hj, hev, rfl⟩ := mem_DstarPQ_iff.mp hx
      exact (hiff i hi j hj).mpr hev
  · have h := hY a le_rfl b le_rfl
    rw [hcorner, hsab] at h
    norm_num at h

/-! ### Jiang–Yang Theorem A for `q = 3` -/

/-- **Theorem A of Jiang–Yang for `q = 3`**: for every prime `p ≥ 5` and all `r, s`, the
checkerboard `D* = {p^i 3^j : i + j even}` is the unique maximiser of the energy of
`ICG(p^(2r) 3^(2s+1), D)` over all sets `D` of proper divisors. -/
theorem jiang_yang_q3 (p r s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (D : Finset ℕ)
    (hD : D ⊆ (p ^ (2 * r) * 3 ^ (2 * s + 1)).properDivisors)
    (hne : D ≠ DstarPQ p 3 (2 * r) (2 * s + 1)) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ (2 * r) * 3 ^ (2 * s + 1)) D)
        (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ (2 * r) * 3 ^ (2 * s + 1))
        (DstarPQ p 3 (2 * r) (2 * s + 1))) (ICGBridge.icgAdj_isHermitian _ _) :=
  checkerboard_unique_max p 3 (2 * r) (2 * s + 1) hp Nat.prime_three (by omega) hp5 le_rfl
    ⟨r + s, by ring⟩ D hD hne

/-- The maximal energy for `q = 3`: `2 E_max = n + d_{2r}(p) d_{2s+1}(3)`. -/
theorem jiang_yang_q3_value (p r s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 * ICGBridge.energy (ICGBridge.icgAdj (p ^ (2 * r) * 3 ^ (2 * s + 1))
        (DstarPQ p 3 (2 * r) (2 * s + 1))) (ICGBridge.icgAdj_isHermitian _ _) =
      (p : ℝ) ^ (2 * r) * (3 : ℝ) ^ (2 * s + 1) + L1 p (2 * r) sgnv * L1 3 (2 * s + 1) sgnv := by
  have := energy_DstarPQ hp Nat.prime_three (by omega) (by omega) le_rfl (2 * r) (2 * s + 1)
  push_cast at this
  exact this

/-- `D*` is an admissible (nonempty, proper-divisor) connection set. -/
theorem DstarPQ_admissible (p r s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    DstarPQ p 3 (2 * r) (2 * s + 1) ⊆ (p ^ (2 * r) * 3 ^ (2 * s + 1)).properDivisors ∧
      1 ∈ DstarPQ p 3 (2 * r) (2 * s + 1) := by
  refine ⟨DstarPQ_subset hp Nat.prime_three (by omega) ⟨r + s, by ring⟩, ?_⟩
  rw [mem_DstarPQ_iff]
  exact ⟨0, Nat.zero_le _, 0, Nat.zero_le _, ⟨0, rfl⟩, by simp⟩

end ICGGeneral

#print axioms ICGGeneral.checkerboard_unique_max
#print axioms ICGGeneral.jiang_yang_q3
#print axioms ICGGeneral.jiang_yang_q3_value
#print axioms ICGGeneral.energy_DstarPQ
