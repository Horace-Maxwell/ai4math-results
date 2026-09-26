import Mathlib
import Research.ICGBridgeMain
import Research.ICGGeneralThm5

/-!
# General spectral bridge: `energy(ICG(p^a q^b, D)) = ‖T_a(p) X T_b(q)ᵀ‖₁`

For distinct primes `p, q`, exponents `a, b` and any finite set `D` of naturals, the energy of
the integral circulant graph `ICG(p^a q^b, D)` (adjacency matrix `ICGBridge.icgAdj`, energy
`ICGBridge.energy` = sum of absolute values of the Hermitian eigenvalues) equals the entrywise
`ℓ¹` norm of `T_a(p) X T_b(q)ᵀ`, where `X c e = [p^c q^e ∈ D]` is the divisor-exponent matrix
(`energy_icgAdj_pq`).

The chain generalises `Research/ICGBridge*.lean` (which treated `27 p²`):
circulant spectrum = DFT (`ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft`, general);
DFT of gcd-class indicators = products of prime-power Ramanujan sums (`dft_gcd_classG`);
class sizes `φ(n / p^u q^v)` (`Nat.totient_div_of_dvd`).
-/

noncomputable section

namespace ICGGeneral

open Finset ZMod

variable {p q : ℕ}

/-! ### Divisors of `p^a q^b` -/

lemma coprime_pq (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).mpr hpq

lemma pq_dvd_iff (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {x y c d : ℕ} :
    p ^ x * q ^ y ∣ p ^ c * q ^ d ↔ x ≤ c ∧ y ≤ d := by
  constructor
  · intro h
    have hc : Nat.Coprime (p ^ x) (q ^ d) := Nat.Coprime.pow _ _ (coprime_pq hp hq hpq)
    have hc' : Nat.Coprime (q ^ y) (p ^ c) := Nat.Coprime.pow _ _ (coprime_pq hp hq hpq).symm
    have h1 : p ^ x ∣ p ^ c := hc.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) h)
    have h2 : q ^ y ∣ q ^ d := hc'.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) h)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1,
      (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p h1) (Nat.pow_dvd_pow q h2)

lemma pq_inj (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {x y c d : ℕ} :
    p ^ x * q ^ y = p ^ c * q ^ d ↔ x = c ∧ y = d := by
  constructor
  · intro h
    have h1 : p ^ x * q ^ y ∣ p ^ c * q ^ d := by rw [h]
    have h2 : p ^ c * q ^ d ∣ p ^ x * q ^ y := by rw [h]
    rw [pq_dvd_iff hp hq hpq] at h1 h2
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

lemma pq_dvd_rep (hp : p.Prime) (hq : q.Prime) {a b d : ℕ} (hd : d ∣ p ^ a * q ^ b) :
    ∃ c ≤ a, ∃ e ≤ b, d = p ^ c * q ^ e := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨c, hc, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hq).mp hz
  exact ⟨c, hc, e, he, rfl⟩

lemma pq_gcd_rep (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (N : ℕ) (hN : N = p ^ a * q ^ b)
    (v : ℕ) : ∃ c ≤ a, ∃ e ≤ b, Nat.gcd v N = p ^ c * q ^ e := by
  subst hN
  exact pq_dvd_rep hp hq (Nat.gcd_dvd_right v _)

lemma pq_dvd_iff_of_gcd (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (N : ℕ)
    (hN : N = p ^ a * q ^ b) {v c e x y : ℕ} (hx : x ≤ a) (hy : y ≤ b)
    (h : Nat.gcd v N = p ^ c * q ^ e) : p ^ x * q ^ y ∣ v ↔ x ≤ c ∧ y ≤ e := by
  subst hN
  rw [← pq_dvd_iff hp hq hpq, ← h]
  constructor
  · intro hv
    exact Nat.dvd_gcd hv ((pq_dvd_iff hp hq hpq).mpr ⟨hx, hy⟩)
  · intro hv
    exact dvd_trans hv (Nat.gcd_dvd_left _ _)

/-! ### Divisibility indicators and their DFT -/

/-- `[x ≤ a ∧ y ≤ b ∧ p^x q^y ∣ v]`. -/
def indG (p q a b v x y : ℕ) : ℤ := if x ≤ a ∧ y ≤ b ∧ p ^ x * q ^ y ∣ v then 1 else 0

lemma indG_eq (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (N : ℕ)
    (hN : N = p ^ a * q ^ b) {v c e : ℕ} (h : Nat.gcd v N = p ^ c * q ^ e) (x y : ℕ) :
    indG p q a b v x y = if x ≤ a ∧ y ≤ b ∧ x ≤ c ∧ y ≤ e then 1 else 0 := by
  unfold indG
  have key : (x ≤ a ∧ y ≤ b ∧ p ^ x * q ^ y ∣ v) ↔ (x ≤ a ∧ y ≤ b ∧ x ≤ c ∧ y ≤ e) := by
    constructor
    · rintro ⟨hx, hy, hd⟩
      exact ⟨hx, hy, (pq_dvd_iff_of_gcd hp hq hpq N hN hx hy h).mp hd⟩
    · rintro ⟨hx, hy, hd⟩
      exact ⟨hx, hy, (pq_dvd_iff_of_gcd hp hq hpq N hN hx hy h).mpr hd⟩
  exact if_congr key rfl rfl

/-- Inclusion–exclusion for the indicator of `gcd(v, N) = p^c q^e`. -/
lemma gcd_classG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (N : ℕ)
    (hN : N = p ^ a * q ^ b) (v c e : ℕ) (hc : c ≤ a) (he : e ≤ b) :
    (if Nat.gcd v N = p ^ c * q ^ e then (1 : ℤ) else 0) =
      indG p q a b v c e - indG p q a b v (c + 1) e - indG p q a b v c (e + 1) +
        indG p q a b v (c + 1) (e + 1) := by
  obtain ⟨c0, hc0, e0, he0, hg⟩ := pq_gcd_rep hp hq N hN v
  simp only [indG_eq hp hq hpq N hN hg, hg, pq_inj hp hq hpq]
  split_ifs <;> omega

/-- `S(x, u) = [x ≤ a ∧ a - x ≤ u] P^(a-x)`. -/
def Spow (P : ℤ) (a x u : ℕ) : ℤ := if x ≤ a ∧ a - x ≤ u then P ^ (a - x) else 0

lemma dft_indG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b N : ℕ} [NeZero N]
    (hN : N = p ^ a * q ^ b) (k : ZMod N) {u v : ℕ} (hk : Nat.gcd k.val N = p ^ u * q ^ v)
    (x y : ℕ) :
    ∑ s : ZMod N, stdAddChar (-(s * k)) * ((indG p q a b s.val x y : ℤ) : ℂ) =
      ((Spow p a x u * Spow q b y v : ℤ) : ℂ) := by
  by_cases hxy : x ≤ a ∧ y ≤ b
  · have hmL : (p ^ x * q ^ y) * (p ^ (a - x) * q ^ (b - y)) = N := by
      rw [hN, mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hxy.1,
        Nat.add_sub_cancel' hxy.2]
    have h1 := ICGBridge.sum_dvd_stdAddChar (p ^ x * q ^ y) (p ^ (a - x) * q ^ (b - y)) hmL k
    have h2 : ∀ s : ZMod N, stdAddChar (-(s * k)) * ((indG p q a b s.val x y : ℤ) : ℂ) =
        if p ^ x * q ^ y ∣ s.val then stdAddChar (-(s * k)) else 0 := by
      intro s
      unfold indG
      by_cases hd : p ^ x * q ^ y ∣ s.val
      · simp [hd, hxy.1, hxy.2]
      · simp [hd]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), h1]
    have hiff := pq_dvd_iff_of_gcd hp hq hpq N hN (x := a - x) (y := b - y) (by omega) (by omega) hk
    unfold Spow
    by_cases hc : a - x ≤ u ∧ b - y ≤ v
    · rw [if_pos (hiff.mpr hc), if_pos ⟨hxy.1, hc.1⟩, if_pos ⟨hxy.2, hc.2⟩]
      push_cast
      ring
    · rw [if_neg (fun h => hc (hiff.mp h))]
      by_cases hc1 : a - x ≤ u
      · rw [if_neg (fun h => hc ⟨hc1, h.2⟩ : ¬ (y ≤ b ∧ b - y ≤ v))]
        simp
      · rw [if_neg (fun h => hc1 h.2 : ¬ (x ≤ a ∧ a - x ≤ u))]
        simp
  · have h0 : ∀ s : ZMod N, indG p q a b s.val x y = 0 := by
      intro s
      unfold indG
      rw [if_neg (fun h => hxy ⟨h.1, h.2.1⟩)]
    simp only [h0, Int.cast_zero, mul_zero, Finset.sum_const_zero]
    unfold Spow
    by_cases hx : x ≤ a
    · have hy : ¬ y ≤ b := fun hy => hxy ⟨hx, hy⟩
      rw [if_neg (fun h => hy h.1 : ¬ (y ≤ b ∧ b - y ≤ v))]
      simp
    · rw [if_neg (fun h => hx h.1 : ¬ (x ≤ a ∧ a - x ≤ u))]
      simp

/-- DFT of a gcd-class indicator: a product of two prime-power Ramanujan sums. -/
theorem dft_gcd_classG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b N : ℕ} [NeZero N]
    (hN : N = p ^ a * q ^ b) (k : ZMod N) {u v : ℕ} (hk : Nat.gcd k.val N = p ^ u * q ^ v)
    (c e : ℕ) (hc : c ≤ a) (he : e ≤ b) :
    ∑ s : ZMod N, stdAddChar (-(s * k)) *
        (if Nat.gcd s.val N = p ^ c * q ^ e then (1 : ℂ) else 0) =
      (((Spow p a c u - Spow p a (c + 1) u) * (Spow q b e v - Spow q b (e + 1) v) : ℤ) : ℂ) := by
  have h1 : ∀ s : ZMod N, (if Nat.gcd s.val N = p ^ c * q ^ e then (1 : ℂ) else 0) =
      ((indG p q a b s.val c e : ℤ) : ℂ) - ((indG p q a b s.val (c + 1) e : ℤ) : ℂ) -
        ((indG p q a b s.val c (e + 1) : ℤ) : ℂ) +
          ((indG p q a b s.val (c + 1) (e + 1) : ℤ) : ℂ) := by
    intro s
    have h := congrArg (fun z : ℤ => (z : ℂ)) (gcd_classG hp hq hpq N hN s.val c e hc he)
    push_cast at h
    exact h
  simp_rw [h1, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    dft_indG hp hq hpq hN k hk]
  push_cast
  ring

/-! ### The connection function -/

lemma double_sum_ite {M : Type*} [AddCommMonoid M] {A B u0 v0 : ℕ} (hu : u0 < A) (hv : v0 < B)
    (F : ℕ → ℕ → M) :
    ∑ u ∈ range A, ∑ v ∈ range B, (if u0 = u ∧ v0 = v then F u v else 0) = F u0 v0 := by
  rw [Finset.sum_eq_single_of_mem u0 (Finset.mem_range.mpr hu)]
  · simp only [true_and]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hv)]
  · intro u _ hu'
    apply Finset.sum_eq_zero
    intro v _
    rw [if_neg (fun h => hu' h.1.symm)]

lemma conn_decompG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (N : ℕ)
    (hN : N = p ^ a * q ^ b) (D : Finset ℕ) (w : ℕ) :
    (if Nat.gcd w N ∈ D then (1 : ℂ) else 0) =
      ∑ c ∈ range (a + 1), ∑ e ∈ range (b + 1),
        (if p ^ c * q ^ e ∈ D then (if Nat.gcd w N = p ^ c * q ^ e then (1 : ℂ) else 0)
          else 0) := by
  obtain ⟨c0, hc0, e0, he0, hg⟩ := pq_gcd_rep hp hq N hN w
  rw [hg]
  have h : ∀ c e, (if p ^ c * q ^ e ∈ D then
      (if p ^ c0 * q ^ e0 = p ^ c * q ^ e then (1 : ℂ) else 0) else 0) =
      if c0 = c ∧ e0 = e then (if p ^ c0 * q ^ e0 ∈ D then (1 : ℂ) else 0) else 0 := by
    intro c e
    by_cases h : c0 = c ∧ e0 = e
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, if_neg (fun h' => h ((pq_inj hp hq hpq).mp h'))]
      simp
  simp_rw [h]
  rw [double_sum_ite (by omega) (by omega)]

/-- The eigenvalue attached to the gcd-class `(u, v)`. -/
def LamG (p q a b : ℕ) (D : Finset ℕ) (u v : ℕ) : ℤ :=
  ∑ c ∈ range (a + 1), ∑ e ∈ range (b + 1),
    (if p ^ c * q ^ e ∈ D then
      (Spow p a c u - Spow p a (c + 1) u) * (Spow q b e v - Spow q b (e + 1) v) else 0)

theorem dft_connFunG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b N : ℕ} [NeZero N]
    (hN : N = p ^ a * q ^ b) (D : Finset ℕ) (k : ZMod N) {u v : ℕ}
    (hk : Nat.gcd k.val N = p ^ u * q ^ v) :
    𝓕 (fun s : ZMod N => ((ICGBridge.connFun N D s : ℝ) : ℂ)) k = ((LamG p q a b D u v : ℤ) : ℂ) := by
  rw [dft_apply]
  have h1 : ∀ s : ZMod N, ((ICGBridge.connFun N D s : ℝ) : ℂ) =
      ∑ c ∈ range (a + 1), ∑ e ∈ range (b + 1),
        (if p ^ c * q ^ e ∈ D then (if Nat.gcd s.val N = p ^ c * q ^ e then (1 : ℂ) else 0)
          else 0) := by
    intro s
    rw [← conn_decompG hp hq hpq N hN D s.val]
    unfold ICGBridge.connFun
    split_ifs <;> simp
  simp_rw [h1, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold LamG
  push_cast
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_range] at hc he
  by_cases hD : p ^ c * q ^ e ∈ D
  · simp only [hD, if_true]
    have := dft_gcd_classG hp hq hpq hN k hk c e (by omega) (by omega)
    push_cast at this
    exact this
  · simp [hD]

/-! ### Class counting -/

lemma totient_prime_pow_cast (hp : p.Prime) (e : ℕ) :
    ((Nat.totient (p ^ e) : ℕ) : ℝ) = phiX p e := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.totient_prime_pow hp (by omega : 0 < e' + 1), phiX_succ, Nat.add_sub_cancel]
    push_cast [Nat.cast_sub hp.one_le]
    ring

lemma totient_pq (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b u v : ℕ} (hu : u ≤ a)
    (hv : v ≤ b) :
    ((Nat.totient (p ^ a * q ^ b / (p ^ u * q ^ v)) : ℕ) : ℝ) =
      phiX p (a - u) * phiX q (b - v) := by
  have hpos : 0 < p ^ u * q ^ v := by
    have := hp.pos
    have := hq.pos
    positivity
  have hdiv : p ^ a * q ^ b / (p ^ u * q ^ v) = p ^ (a - u) * q ^ (b - v) := by
    have hmul : p ^ a * q ^ b = p ^ u * q ^ v * (p ^ (a - u) * q ^ (b - v)) := by
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hu, Nat.add_sub_cancel' hv]
    rw [hmul, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv, Nat.totient_mul (Nat.Coprime.pow _ _ (coprime_pq hp hq hpq))]
  push_cast
  rw [totient_prime_pow_cast hp, totient_prime_pow_cast hq]

lemma pq_dvd_N (N : ℕ) {a b : ℕ} (hN : N = p ^ a * q ^ b) {u v : ℕ} (hu : u ≤ a) (hv : v ≤ b) :
    p ^ u * q ^ v ∣ N := by
  rw [hN]
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p hu) (Nat.pow_dvd_pow q hv)

theorem sum_norm_dft_connFunG (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b N : ℕ} [NeZero N]
    (hN : N = p ^ a * q ^ b) (D : Finset ℕ) :
    ∑ k : ZMod N, ‖𝓕 (fun s : ZMod N => ((ICGBridge.connFun N D s : ℝ) : ℂ)) k‖ =
      ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        (Nat.totient (N / (p ^ u * q ^ v)) : ℝ) * |((LamG p q a b D u v : ℤ) : ℝ)| := by
  set Λ : ℕ → ℕ → ℝ := fun u v => |((LamG p q a b D u v : ℤ) : ℝ)| with hΛ
  set Φ : ℕ → ℝ := fun d => ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
    (if d = p ^ u * q ^ v then Λ u v else 0) with hΦ
  have hk : ∀ k : ZMod N, ‖𝓕 (fun s : ZMod N => ((ICGBridge.connFun N D s : ℝ) : ℂ)) k‖ =
      Φ (Nat.gcd k.val N) := by
    intro k
    obtain ⟨u0, hu0, v0, hv0, hg⟩ := pq_gcd_rep hp hq N hN k.val
    rw [dft_connFunG hp hq hpq hN D k hg, Complex.norm_intCast, hg]
    simp only [hΦ]
    have h1 : ∀ u v, (if p ^ u0 * q ^ v0 = p ^ u * q ^ v then Λ u v else 0) =
        if u0 = u ∧ v0 = v then Λ u v else 0 := by
      intro u v
      simp only [pq_inj hp hq hpq]
    simp_rw [h1]
    rw [double_sum_ite (by omega) (by omega)]
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [ICGBridge.sum_zmod_val (N := N) (fun w => Φ (Nat.gcd w N))]
  simp only [hΦ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hu hv
  have hsplit : ∀ w : ℕ, (if Nat.gcd w N = p ^ u * q ^ v then Λ u v else 0) =
      (if N.gcd w = p ^ u * q ^ v then (1 : ℝ) else 0) * Λ u v := by
    intro w
    rw [Nat.gcd_comm]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun w _ => hsplit w), ← Finset.sum_mul, Finset.sum_boole,
    ← Nat.totient_div_of_dvd (pq_dvd_N N hN (by omega) (by omega))]

/-! ### Identification with `‖T_a(p) X T_b(q)ᵀ‖₁` -/

lemma ramX_eq_Spow (p : ℕ) {a c : ℕ} (hc : c ≤ a) (u : ℕ) :
    ramX (p : ℝ) (a - c) u = ((Spow p a c u : ℤ) : ℝ) - ((Spow p a (c + 1) u : ℤ) : ℝ) := by
  unfold ramX Spow
  by_cases h0 : a - c = 0
  · have hca : c = a := by omega
    subst hca
    simp
  · have h1 : c + 1 ≤ a := by omega
    have h2 : a - (c + 1) = a - c - 1 := by omega
    rw [if_neg h0]
    by_cases h3 : a - c ≤ u
    · rw [if_pos h3, if_pos (show c ≤ a ∧ a - c ≤ u from ⟨hc, h3⟩),
        if_pos (show c + 1 ≤ a ∧ a - (c + 1) ≤ u from ⟨h1, by omega⟩), h2]
      obtain ⟨k, hk⟩ : ∃ k, a - c = k + 1 := ⟨a - c - 1, by omega⟩
      rw [hk, phiX_succ, show k + 1 - 1 = k by omega]
      push_cast
      ring
    · rw [if_neg h3, if_neg (show ¬ (c ≤ a ∧ a - c ≤ u) from fun h => h3 h.2)]
      by_cases h4 : a - c = u + 1
      · rw [if_pos h4, if_pos (show c + 1 ≤ a ∧ a - (c + 1) ≤ u from ⟨h1, by omega⟩), h2, h4,
          show u + 1 - 1 = u by omega]
        push_cast
        ring
      · rw [if_neg h4, if_neg (show ¬ (c + 1 ≤ a ∧ a - (c + 1) ≤ u) from fun h => by omega)]
        simp

lemma phiX_nonneg {x : ℝ} (hx : 1 ≤ x) (e : ℕ) : 0 ≤ phiX x e := by
  unfold phiX
  split_ifs
  · norm_num
  · have : 0 ≤ x - 1 := by linarith
    positivity

lemma class_term (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (D : Finset ℕ) {u v : ℕ}
    (hu : u ≤ a) (hv : v ≤ b) :
    ((Nat.totient (p ^ a * q ^ b / (p ^ u * q ^ v)) : ℕ) : ℝ) * |((LamG p q a b D u v : ℤ) : ℝ)| =
      |Mentry p q a b (fun c e => if p ^ c * q ^ e ∈ D then 1 else 0) u v| := by
  rw [totient_pq hp hq hpq hu hv]
  have hφ : 0 ≤ phiX (p : ℝ) (a - u) * phiX (q : ℝ) (b - v) :=
    mul_nonneg (phiX_nonneg (by exact_mod_cast hp.one_le) _)
      (phiX_nonneg (by exact_mod_cast hq.one_le) _)
  rw [← abs_of_nonneg hφ, ← abs_mul]
  congr 1
  unfold LamG Mentry
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_range] at hc he
  unfold Tent
  rw [ramX_eq_Spow p (by omega : c ≤ a) u, ramX_eq_Spow q (by omega : e ≤ b) v]
  split_ifs
  · ring
  · ring

/-- **General spectral bridge.** -/
theorem energy_icgAdj_pq (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (D : Finset ℕ) :
    ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) D) (ICGBridge.icgAdj_isHermitian _ _) =
      L1mat p q a b (fun c e => if p ^ c * q ^ e ∈ D then 1 else 0) := by
  have : NeZero (p ^ a * q ^ b) := ⟨by have := hp.pos; have := hq.pos; positivity⟩
  unfold ICGBridge.energy
  rw [ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft (ICGBridge.icgAdj (p ^ a * q ^ b) D) _
      (ZMod.finEquiv (p ^ a * q ^ b)).toEquiv (ICGBridge.connFun (p ^ a * q ^ b) D)
      (ICGBridge.icgAdj_eq_connFun (p ^ a * q ^ b) D),
    sum_norm_dft_connFunG hp hq hpq rfl D]
  unfold L1mat
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hu hv
  exact class_term hp hq hpq D (by omega) (by omega)

end ICGGeneral

#print axioms ICGGeneral.energy_icgAdj_pq
