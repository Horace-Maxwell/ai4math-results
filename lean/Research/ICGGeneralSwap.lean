import Mathlib
import Research.ICGGeneralMain

/-!
# Swapped Theorem 5 and the opposite-parity case for all distinct odd primes

Since `‖T_a(p) Y T_b(q)ᵀ‖₁ = ‖T_b(q) Yᵀ T_a(p)ᵀ‖₁`, Theorem 5 also holds for `p ≥ 3`, `q ≥ 5`
(`thm5_le_swap`, `thm5_eq_swap`).  Consequently (`checkerboard_unique_max_odd`): for all distinct
odd primes `p, q` and all `a, b` with `a + b` odd, the checkerboard `D*` is the unique energy
maximiser among the subsets of the proper divisors of `p^a q^b`.  This contains Jiang–Yang
Theorem A (`q ≥ 5`, `n = p^(2r) q^(2s+1)`, `p = 3` allowed) and its `q = 3` case.
-/

noncomputable section

namespace ICGGeneral

open Finset

lemma Mentry_transpose (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) :
    Mentry p q a b Y u v = Mentry q p b a (fun l i => Y i l) v u := by
  unfold Mentry
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma L1mat_transpose (p q : ℝ) (a b : ℕ) (Y : ℕ → ℕ → ℝ) :
    L1mat p q a b Y = L1mat q p b a (fun l i => Y i l) := by
  unfold L1mat
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  rw [Mentry_transpose]

/-- **Theorem 5, swapped roles** (`p ≥ 3`, `q ≥ 5`). -/
theorem thm5_le_swap {p q : ℝ} (hp : 3 ≤ p) (hq : 5 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) : L1mat p q a b Y ≤ L1 p a sgnv * L1 q b sgnv := by
  rw [L1mat_transpose, mul_comm]
  exact thm5_le hq hp (fun l hl i hi => hY i hi l hl)

theorem thm5_eq_swap {p q : ℝ} (hp : 3 ≤ p) (hq : 5 ≤ q) {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hY : ∀ i ≤ a, IsSign b (Y i)) (h : L1mat p q a b Y = L1 p a sgnv * L1 q b sgnv) :
    (∀ i ≤ a, ∀ l ≤ b, Y i l = sgnv i * sgnv l) ∨
      (∀ i ≤ a, ∀ l ≤ b, Y i l = -(sgnv i * sgnv l)) := by
  rw [L1mat_transpose, mul_comm] at h
  rcases thm5_eq hq hp (fun l hl i hi => hY i hi l hl) h with h' | h'
  · left
    intro i hi l hl
    exact (h' l hl i hi).trans (mul_comm _ _)
  · right
    intro i hi l hl
    exact (h' l hl i hi).trans (by ring)

/-- The uniqueness argument, assuming the two halves of Theorem 5 for `(p, q, a, b)`. -/
theorem checkerboard_unique_max_of (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hab : Odd (a + b))
    (hT : ∀ Y : ℕ → ℕ → ℝ, (∀ i ≤ a, IsSign b (Y i)) →
      L1mat p q a b Y ≤ L1 p a sgnv * L1 q b sgnv)
    (hTeq : ∀ Y : ℕ → ℕ → ℝ, (∀ i ≤ a, IsSign b (Y i)) →
      L1mat p q a b Y = L1 p a sgnv * L1 q b sgnv →
        (∀ i ≤ a, ∀ l ≤ b, Y i l = sgnv i * sgnv l) ∨
          (∀ i ≤ a, ∀ l ≤ b, Y i l = -(sgnv i * sgnv l)))
    (D : Finset ℕ) (hD : D ⊆ (p ^ a * q ^ b).properDivisors) (hne : D ≠ DstarPQ p q a b) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (DstarPQ p q a b))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hp0 : (0 : ℝ) < p := by have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                               linarith
  have hq0 : (0 : ℝ) < q := by have : (3 : ℝ) ≤ q := by exact_mod_cast hq3
                               linarith
  set X : ℕ → ℕ → ℝ := fun c e => if p ^ c * q ^ e ∈ D then 1 else 0 with hX
  have hYsign : ∀ i ≤ a, IsSign b (fun l => 2 * X i l - 1) := by
    intro i _ l _
    simp only [hX]
    split_ifs
    · left; norm_num
    · right; norm_num
  have hE := energy_icgAdj_pq p q a b hp hq hpq D
  have hEstar := energy_DstarPQ hp hq hpq hp3 hq3 a b
  have hup := two_L1mat_le hp0 hq0 a b X
  have h5 := hT _ hYsign
  by_contra hcon0
  have hcon := not_lt.mp hcon0
  rw [hE] at hcon
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
  rcases hTeq _ hYsign hge with hY | hY
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

/-- **Opposite-parity maximal energy for all distinct odd primes.** For distinct odd primes
`p, q` and `a + b` odd, the checkerboard `D* = {p^i q^j : i + j even}` is the unique maximiser of
`energy(ICG(p^a q^b, D))` over `D ⊆ properDivisors(p^a q^b)`. -/
theorem checkerboard_unique_max_odd (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hab : Odd (a + b)) (D : Finset ℕ)
    (hD : D ⊆ (p ^ a * q ^ b).properDivisors) (hne : D ≠ DstarPQ p q a b) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (DstarPQ p q a b))
        (ICGBridge.icgAdj_isHermitian _ _) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have h4 : ∀ r : ℕ, r.Prime → r ≠ 4 := by
    intro r hr h
    subst h
    norm_num at hr
  by_cases h5 : 5 ≤ p
  · exact checkerboard_unique_max p q a b hp hq hpq h5 hq3 hab D hD hne
  · have hp_eq : p = 3 := by have := h4 p hp; omega
    have hq5 : 5 ≤ q := by have := h4 q hq; omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq5
    exact checkerboard_unique_max_of p q a b hp hq hpq hp3 hq3 hab
      (fun Y hY => thm5_le_swap hpR hqR hY) (fun Y hY h => thm5_eq_swap hpR hqR hY h) D hD hne

/-- **Jiang–Yang Theorem A** (their range `q ≥ 5`, `p ≠ q` any odd prime, including `p = 3`),
together with the `q = 3` case: `n = p^(2r) q^(2s+1)`. -/
theorem jiang_yang_thmA (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (D : Finset ℕ)
    (hD : D ⊆ (p ^ (2 * r) * q ^ (2 * s + 1)).properDivisors)
    (hne : D ≠ DstarPQ p q (2 * r) (2 * s + 1)) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ (2 * r) * q ^ (2 * s + 1)) D)
        (ICGBridge.icgAdj_isHermitian _ _) <
      ICGBridge.energy (ICGBridge.icgAdj (p ^ (2 * r) * q ^ (2 * s + 1))
        (DstarPQ p q (2 * r) (2 * s + 1))) (ICGBridge.icgAdj_isHermitian _ _) :=
  checkerboard_unique_max_odd p q (2 * r) (2 * s + 1) hp hq hpq hp2 hq2 ⟨r + s, by ring⟩ D hD hne

/-- Consistency with the round-3 bridge: for `r = s = 1`, `q = 3`, `D*` is Roldán's set
`{1, p², 3p, 9, 9p², 27p}`. -/
theorem DstarPQ_roldan (p : ℕ) :
    DstarPQ p 3 2 3 = ICGBridge.Dstar p := by
  ext x
  rw [mem_DstarPQ_iff]
  simp only [ICGBridge.Dstar, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, j, hj, hev, rfl⟩
    interval_cases i <;> interval_cases j <;> simp_all (config := { decide := true }) <;>
      (try ring_nf) <;> (try simp)
  · rintro (h | h | h | h | h | h) <;> subst h
    · exact ⟨0, by omega, 0, by omega, ⟨0, rfl⟩, by ring⟩
    · exact ⟨2, by omega, 0, by omega, ⟨1, rfl⟩, by ring⟩
    · exact ⟨1, by omega, 1, by omega, ⟨1, rfl⟩, by ring⟩
    · exact ⟨0, by omega, 2, by omega, ⟨1, rfl⟩, by ring⟩
    · exact ⟨2, by omega, 2, by omega, ⟨2, rfl⟩, by ring⟩
    · exact ⟨1, by omega, 3, by omega, ⟨2, rfl⟩, by ring⟩

end ICGGeneral

#print axioms ICGGeneral.checkerboard_unique_max_odd
#print axioms ICGGeneral.jiang_yang_thmA
#print axioms ICGGeneral.thm5_le_swap
#print axioms ICGGeneral.DstarPQ_roldan
