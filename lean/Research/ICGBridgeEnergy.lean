import Mathlib
import Research.ICGBridgeRamanujan

/-!
# Spectral bridge, part 3: DFT of the ICG connection function and class counting

For `N = p² 3³` and a set `D` of naturals with `N ∉ D`, the connection function
`connFun N D s = [gcd(s.val, N) ∈ D]` on `ZMod N` has DFT, at any `k` with
`gcd(k.val, N) = p^a 3^b`, equal to `lamD p (bitsOf p D) a b`, where
`bitsOf p D j = decide (p^(j/4) 3^(j%4) ∈ D)` (`j : Fin 11`) encodes `D` by exponent pairs.
Grouping the `k` by gcd-class gives
`∑ k, ‖𝓕 connFun k‖ = ∑_{r : Fin 12} φ(N / p^(r/4) 3^(r%4)) * |lamD p bits (r/4) (r%4)|`.
-/

namespace ICGBridge

open ZMod Finset

variable {p : ℕ}

/-- Divisor encoded by `j : Fin 11`: `p^(j/4) 3^(j%4)` (these are the proper divisors of
`p² 3³`). -/
def ej (p : ℕ) (j : Fin 11) : ℕ := p ^ (j.val / 4) * 3 ^ (j.val % 4)

/-- Divisor encoded by `r : Fin 12`: `p^(r/4) 3^(r%4)` (all divisors of `p² 3³`). -/
def er (p : ℕ) (r : Fin 12) : ℕ := p ^ (r.val / 4) * 3 ^ (r.val % 4)

/-- Bit pattern of a connection set `D`. -/
def bitsOf (p : ℕ) (D : Finset ℕ) (j : Fin 11) : Bool := decide (ej p j ∈ D)

/-- Eigenvalue (Ramanujan-sum combination) attached to a bit pattern and a gcd-class. -/
def lamD (P : ℤ) (bits : Fin 11 → Bool) (a b : ℕ) : ℤ :=
  ∑ j : Fin 11, if bits j then Lam P (j.val / 4) (j.val % 4) a b else 0

/-- Connection function of `ICG(N, D)` on `ZMod N`. -/
def connFun (N : ℕ) (D : Finset ℕ) (s : ZMod N) : ℝ :=
  if Nat.gcd s.val N ∈ D then 1 else 0

lemma ej_eq_iff (hp : p.Prime) (hp3 : p ≠ 3) {a b : ℕ} (j : Fin 11) :
    p ^ a * 3 ^ b = ej p j ↔ j.val = 4 * a + b ∧ b ≤ 3 := by
  unfold ej
  rw [pow_mul_pow_inj hp hp3]
  omega

lemma er_eq_iff (hp : p.Prime) (hp3 : p ≠ 3) {a b : ℕ} (r : Fin 12) :
    p ^ a * 3 ^ b = er p r ↔ r.val = 4 * a + b ∧ b ≤ 3 := by
  unfold er
  rw [pow_mul_pow_inj hp hp3]
  omega

/-- Decomposition of the connection function along the gcd classes. -/
lemma conn_decomp (hp : p.Prime) (hp3 : p ≠ 3) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3)
    (D : Finset ℕ) (hND : N ∉ D) (v : ℕ) :
    (if Nat.gcd v N ∈ D then (1 : ℂ) else 0) =
      ∑ j : Fin 11, if ej p j ∈ D then (if Nat.gcd v N = ej p j then (1 : ℂ) else 0) else 0 := by
  obtain ⟨a, ha, b, hb, hg⟩ := gcd_rep hp N hN v
  rw [hg]
  simp only [ej_eq_iff hp hp3]
  by_cases hab : 4 * a + b < 11
  · set j0 : Fin 11 := ⟨4 * a + b, hab⟩ with hj0
    have hej : ej p j0 = p ^ a * 3 ^ b := ((ej_eq_iff hp hp3 j0).mpr ⟨rfl, hb⟩).symm
    have h1 : ∀ j : Fin 11, (if ej p j ∈ D then
        (if j.val = 4 * a + b ∧ b ≤ 3 then (1 : ℂ) else 0) else 0) =
        if j0 = j then (if ej p j0 ∈ D then (1 : ℂ) else 0) else 0 := by
      intro j
      by_cases hj : j0 = j
      · subst hj
        simp [hj0, hb]
      · have : ¬ (j.val = 4 * a + b ∧ b ≤ 3) := by
          intro h
          exact hj (Fin.ext (by simp [hj0, h.1]))
        simp [this, hj]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_ite_eq]
    simp [hej]
  · -- then `a = 2`, `b = 3`, i.e. the gcd is `N` itself
    have ha2 : a = 2 := by omega
    have hb3 : b = 3 := by omega
    have hNmem : p ^ a * 3 ^ b ∉ D := by rw [ha2, hb3, ← hN]; exact hND
    rw [if_neg hNmem]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have : ¬ (j.val = 4 * a + b ∧ b ≤ 3) := by omega
    simp [this]

/-- **Eigenvalues of `ICG(N, D)`**: the DFT of the connection function at `k` depends only on
the gcd-class `gcd(k, N) = p^a 3^b` and equals `lamD p (bitsOf p D) a b`. -/
theorem dft_connFun (hp : p.Prime) (hp3 : p ≠ 3) {N : ℕ} [NeZero N] (hN : N = p ^ 2 * 3 ^ 3)
    (D : Finset ℕ) (hND : N ∉ D) (k : ZMod N) {a b : ℕ}
    (hk : Nat.gcd k.val N = p ^ a * 3 ^ b) :
    𝓕 (fun s : ZMod N => ((connFun N D s : ℝ) : ℂ)) k =
      ((lamD p (bitsOf p D) a b : ℤ) : ℂ) := by
  rw [dft_apply]
  have h1 : ∀ s : ZMod N, ((connFun N D s : ℝ) : ℂ) =
      ∑ j : Fin 11, if ej p j ∈ D then
        (if Nat.gcd s.val N = ej p j then (1 : ℂ) else 0) else 0 := by
    intro s
    rw [← conn_decomp hp hp3 N hN D hND s.val]
    unfold connFun
    split_ifs <;> simp
  simp_rw [h1, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold lamD
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hj := j.isLt
  by_cases hjD : ej p j ∈ D
  · have hb : bitsOf p D j = true := by simp [bitsOf, hjD]
    simp only [hjD, if_true, hb]
    exact dft_gcd_class hp hp3 hN k hk (j.val / 4) (j.val % 4) (by omega) (by omega)
  · have hb : bitsOf p D j = false := by simp [bitsOf, hjD]
    simp [hjD, hb]

lemma er_dvd (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3) (r : Fin 12) :
    er p r ∣ N := by
  have hr := r.isLt
  rw [hN]
  unfold er
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) (Nat.pow_dvd_pow 3 (by omega))

/-- **Class counting.** -/
theorem sum_norm_dft_connFun (hp : p.Prime) (hp3 : p ≠ 3) {N : ℕ} [NeZero N]
    (hN : N = p ^ 2 * 3 ^ 3) (D : Finset ℕ) (hND : N ∉ D) :
    ∑ k : ZMod N, ‖𝓕 (fun s : ZMod N => ((connFun N D s : ℝ) : ℂ)) k‖ =
      ∑ r : Fin 12, (Nat.totient (N / er p r) : ℝ) *
        |((lamD p (bitsOf p D) (r.val / 4) (r.val % 4) : ℤ) : ℝ)| := by
  set Λ : Fin 12 → ℝ := fun r => |((lamD p (bitsOf p D) (r.val / 4) (r.val % 4) : ℤ) : ℝ)|
    with hΛ
  set Φ : ℕ → ℝ := fun d => ∑ r : Fin 12, if d = er p r then Λ r else 0 with hΦ
  have hk : ∀ k : ZMod N, ‖𝓕 (fun s : ZMod N => ((connFun N D s : ℝ) : ℂ)) k‖ =
      Φ (Nat.gcd k.val N) := by
    intro k
    obtain ⟨a, ha, b, hb, hg⟩ := gcd_rep hp N hN k.val
    rw [dft_connFun hp hp3 hN D hND k hg, Complex.norm_intCast, hg]
    have hab : 4 * a + b < 12 := by omega
    set r0 : Fin 12 := ⟨4 * a + b, hab⟩ with hr0
    have h1 : ∀ r : Fin 12, (if p ^ a * 3 ^ b = er p r then Λ r else 0) =
        if r0 = r then Λ r0 else 0 := by
      intro r
      simp only [er_eq_iff hp hp3]
      by_cases hr : r0 = r
      · subst hr
        simp [hr0, hb]
      · have : ¬ (r.val = 4 * a + b ∧ b ≤ 3) := by
          intro h
          exact hr (Fin.ext (by simp [hr0, h.1]))
        simp [this, hr]
    simp only [hΦ]
    rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, hΛ, hr0]
    have e1 : (4 * a + b) / 4 = a := by omega
    have e2 : (4 * a + b) % 4 = b := by omega
    simp [e1, e2]
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [sum_zmod_val (N := N) (fun v => Φ (Nat.gcd v N))]
  simp only [hΦ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hsplit : ∀ v : ℕ, (if Nat.gcd v N = er p r then Λ r else 0) =
      (if N.gcd v = er p r then (1 : ℝ) else 0) * Λ r := by
    intro v
    rw [Nat.gcd_comm]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun v _ => hsplit v), ← Finset.sum_mul, Finset.sum_boole,
    ← Nat.totient_div_of_dvd (er_dvd N hN r)]

end ICGBridge

#print axioms ICGBridge.sum_norm_dft_connFun
