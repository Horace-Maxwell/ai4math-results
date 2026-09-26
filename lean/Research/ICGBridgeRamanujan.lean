import Mathlib
import Research.ICGBridgeSpectral

/-!
# Spectral bridge, part 2: DFT of gcd-class indicators on `ZMod N`, `N = 27 p²`

General facts (any `N`):
* `sum_zmod_val` : sums over `ZMod N` of functions of `val` are sums over `range N`;
* `sum_dvd_stdAddChar` : for `m * L = N`,
  `∑_{s : ZMod N, m ∣ s.val} ψ(-(s k)) = if L ∣ k.val then L else 0`.

Specific to `N = p² · 3³` (`p` prime, `p ≠ 3`):
* every divisor of `N` is `p^a 3^b` (`a ≤ 2`, `b ≤ 3`), uniquely;
* inclusion–exclusion for the indicator of `gcd(v, N) = p^c 3^e` (`gcd_class_eq`);
* the DFT of that indicator at `k` with `gcd(k.val, N) = p^a 3^b` equals `Lam p c e a b`
  (a Ramanujan sum `c_{N/(p^c 3^e)}(k)`, written via inclusion–exclusion).
-/

namespace ICGBridge

open ZMod Finset

section General

variable {N : ℕ} [NeZero N]

lemma sum_zmod_val {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ k : ZMod N, F k.val = ∑ v ∈ range N, F v := by
  refine Finset.sum_nbij' (fun k => k.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro k _
    simpa using ZMod.val_lt k
  · intro v _
    simp
  · intro k _
    simp
  · intro v hv
    simp only [Finset.mem_range] at hv
    simp [ZMod.val_natCast_of_lt hv]
  · intro k _
    rfl

lemma sum_range_dvd {M : Type*} [AddCommMonoid M] (m L n : ℕ) (hmL : m * L = n) (hm : 0 < m)
    (G : ℕ → M) :
    ∑ v ∈ range n, (if m ∣ v then G v else 0) = ∑ t ∈ range L, G (m * t) := by
  subst hmL
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun t => m * t) (fun v => v / m) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by nlinarith, dvd_mul_right m t⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    simp only [Finset.mem_range]
    exact Nat.div_lt_of_lt_mul hv.1
  · intro t _
    simp [Nat.mul_div_cancel_left t hm]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    exact Nat.mul_div_cancel' hv.2
  · intro t _
    rfl

lemma stdAddChar_mul_cast (m L t kv : ℕ) [NeZero L] (hmL : m * L = N) :
    (stdAddChar (-(((m * t : ℕ) : ZMod N) * (kv : ZMod N))) : ℂ) =
      stdAddChar (-((t : ZMod L) * (kv : ZMod L))) := by
  have h1 : (-(((m * t : ℕ) : ZMod N) * (kv : ZMod N))) =
      (((-((m : ℤ) * t * kv)) : ℤ) : ZMod N) := by
    push_cast; ring
  have h2 : (-((t : ZMod L) * (kv : ZMod L))) = (((-((t : ℤ) * kv)) : ℤ) : ZMod L) := by
    push_cast; ring
  rw [h1, h2, stdAddChar_coe, stdAddChar_coe]
  congr 1
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hN : (N : ℂ) = (m : ℂ) * L := by rw [← hmL]; push_cast; ring
  have hm : (m : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    exact NeZero.ne N (by exact_mod_cast hN)
  rw [hN]
  push_cast
  field_simp

/-- Character sum over the multiples of `m` in `ZMod N`, `m * L = N`. -/
theorem sum_dvd_stdAddChar (m L : ℕ) (hmL : m * L = N) (k : ZMod N) :
    ∑ s : ZMod N, (if m ∣ s.val then stdAddChar (-(s * k)) else 0) =
      if L ∣ k.val then (L : ℂ) else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hpos : 0 < m * L := by rw [hmL]; exact Nat.pos_of_ne_zero hN
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hL : 0 < L := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have : NeZero L := ⟨hL.ne'⟩
  have step1 : ∑ s : ZMod N, (if m ∣ s.val then stdAddChar (-(s * k)) else 0) =
      ∑ v ∈ range N, (if m ∣ v then stdAddChar (-((v : ZMod N) * (k.val : ZMod N))) else 0) := by
    rw [← sum_zmod_val (N := N)
      (fun v => if m ∣ v then stdAddChar (-((v : ZMod N) * (k.val : ZMod N))) else (0 : ℂ))]
    simp only [ZMod.natCast_zmod_val]
  rw [step1, sum_range_dvd m L N hmL hm]
  simp_rw [stdAddChar_mul_cast m L _ k.val hmL]
  rw [← sum_zmod_val (N := L) (fun t => stdAddChar (-((t : ZMod L) * (k.val : ZMod L))))]
  simp only [ZMod.natCast_zmod_val]
  have h3 : ∀ t : ZMod L, -(t * (k.val : ZMod L)) = (-(k.val : ZMod L)) * t := fun t => by ring
  simp_rw [h3, sum_stdAddChar_mul, neg_eq_zero, ZMod.natCast_eq_zero_iff]

end General

section Q3

variable {p : ℕ}

lemma coprime_p_three (hp : p.Prime) (hp3 : p ≠ 3) : Nat.Coprime p 3 :=
  (Nat.coprime_primes hp Nat.prime_three).mpr hp3

lemma pow_mul_pow_dvd_iff (hp : p.Prime) (hp3 : p ≠ 3) {x y a b : ℕ} :
    p ^ x * 3 ^ y ∣ p ^ a * 3 ^ b ↔ x ≤ a ∧ y ≤ b := by
  constructor
  · intro h
    have hc : Nat.Coprime (p ^ x) (3 ^ b) := Nat.Coprime.pow _ _ (coprime_p_three hp hp3)
    have hc' : Nat.Coprime (3 ^ y) (p ^ a) := Nat.Coprime.pow _ _ (coprime_p_three hp hp3).symm
    have h1 : p ^ x ∣ p ^ a := hc.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) h)
    have h2 : 3 ^ y ∣ 3 ^ b := hc'.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) h)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1,
      (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p h1) (Nat.pow_dvd_pow 3 h2)

lemma pow_mul_pow_inj (hp : p.Prime) (hp3 : p ≠ 3) {x y a b : ℕ} :
    p ^ x * 3 ^ y = p ^ a * 3 ^ b ↔ x = a ∧ y = b := by
  constructor
  · intro h
    have h1 : p ^ x * 3 ^ y ∣ p ^ a * 3 ^ b := by rw [h]
    have h2 : p ^ a * 3 ^ b ∣ p ^ x * 3 ^ y := by rw [h]
    rw [pow_mul_pow_dvd_iff hp hp3] at h1 h2
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

lemma dvd_rep (hp : p.Prime) {d : ℕ} (hd : d ∣ p ^ 2 * 3 ^ 3) :
    ∃ a ≤ 2, ∃ b ≤ 3, d = p ^ a * 3 ^ b := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  exact ⟨a, ha, b, hb, rfl⟩

lemma gcd_rep (hp : p.Prime) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3) (v : ℕ) :
    ∃ a ≤ 2, ∃ b ≤ 3, Nat.gcd v N = p ^ a * 3 ^ b := by
  subst hN
  exact dvd_rep hp (Nat.gcd_dvd_right v _)

lemma dvd_iff_of_gcd (hp : p.Prime) (hp3 : p ≠ 3) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3)
    {v a b x y : ℕ} (hx : x ≤ 2) (hy : y ≤ 3) (h : Nat.gcd v N = p ^ a * 3 ^ b) :
    p ^ x * 3 ^ y ∣ v ↔ x ≤ a ∧ y ≤ b := by
  subst hN
  rw [← pow_mul_pow_dvd_iff hp hp3, ← h]
  constructor
  · intro hv
    exact Nat.dvd_gcd hv ((pow_mul_pow_dvd_iff hp hp3).mpr ⟨hx, hy⟩)
  · intro hv
    exact dvd_trans hv (Nat.gcd_dvd_left _ _)

/-- `ind p v x y = 1` iff `x ≤ 2`, `y ≤ 3` and `p^x 3^y ∣ v` (else `0`). -/
def ind (p v x y : ℕ) : ℤ := if x ≤ 2 ∧ y ≤ 3 ∧ p ^ x * 3 ^ y ∣ v then 1 else 0

lemma ind_eq (hp : p.Prime) (hp3 : p ≠ 3) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3) {v a b : ℕ}
    (h : Nat.gcd v N = p ^ a * 3 ^ b) (x y : ℕ) :
    ind p v x y = if x ≤ 2 ∧ y ≤ 3 ∧ x ≤ a ∧ y ≤ b then 1 else 0 := by
  unfold ind
  have key : (x ≤ 2 ∧ y ≤ 3 ∧ p ^ x * 3 ^ y ∣ v) ↔ (x ≤ 2 ∧ y ≤ 3 ∧ x ≤ a ∧ y ≤ b) := by
    constructor
    · rintro ⟨hx, hy, hd⟩
      exact ⟨hx, hy, (dvd_iff_of_gcd hp hp3 N hN hx hy h).mp hd⟩
    · rintro ⟨hx, hy, hd⟩
      exact ⟨hx, hy, (dvd_iff_of_gcd hp hp3 N hN hx hy h).mpr hd⟩
  exact if_congr key rfl rfl

/-- Inclusion–exclusion: the indicator of `gcd(v, N) = p^c 3^e`. -/
lemma gcd_class_eq (hp : p.Prime) (hp3 : p ≠ 3) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3)
    (v c e : ℕ) (hc : c ≤ 2) (he : e ≤ 3) :
    (if Nat.gcd v N = p ^ c * 3 ^ e then (1 : ℤ) else 0) =
      ind p v c e - ind p v (c + 1) e - ind p v c (e + 1) + ind p v (c + 1) (e + 1) := by
  obtain ⟨a, ha, b, hb, hg⟩ := gcd_rep hp N hN v
  simp only [ind_eq hp hp3 N hN hg, hg, pow_mul_pow_inj hp hp3]
  split_ifs <;> omega

/-- DFT value of a divisibility indicator (`P` stands for `p`). -/
def Sval (P : ℤ) (x y a b : ℕ) : ℤ :=
  if x ≤ 2 ∧ y ≤ 3 ∧ 2 - x ≤ a ∧ 3 - y ≤ b then P ^ (2 - x) * 3 ^ (3 - y) else 0

/-- DFT value of the gcd-class indicator of `p^c 3^e` at a point of gcd-class `p^a 3^b`
(the Ramanujan sum `c_{N/(p^c 3^e)}(p^a 3^b)`). -/
def Lam (P : ℤ) (c e a b : ℕ) : ℤ :=
  Sval P c e a b - Sval P (c + 1) e a b - Sval P c (e + 1) a b + Sval P (c + 1) (e + 1) a b

variable {N : ℕ} [NeZero N]

lemma dft_ind (hp : p.Prime) (hp3 : p ≠ 3) (hN : N = p ^ 2 * 3 ^ 3) (k : ZMod N) {a b : ℕ}
    (hk : Nat.gcd k.val N = p ^ a * 3 ^ b) (x y : ℕ) :
    ∑ s : ZMod N, stdAddChar (-(s * k)) * ((ind p s.val x y : ℤ) : ℂ) = (Sval p x y a b : ℂ) := by
  by_cases hxy : x ≤ 2 ∧ y ≤ 3
  · have hmL : (p ^ x * 3 ^ y) * (p ^ (2 - x) * 3 ^ (3 - y)) = N := by
      rw [hN, mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hxy.1,
        Nat.add_sub_cancel' hxy.2]
    have h1 := sum_dvd_stdAddChar (p ^ x * 3 ^ y) (p ^ (2 - x) * 3 ^ (3 - y)) hmL k
    have h2 : ∀ s : ZMod N, stdAddChar (-(s * k)) * ((ind p s.val x y : ℤ) : ℂ) =
        if p ^ x * 3 ^ y ∣ s.val then stdAddChar (-(s * k)) else 0 := by
      intro s
      unfold ind
      by_cases hd : p ^ x * 3 ^ y ∣ s.val
      · simp [hd, hxy.1, hxy.2]
      · simp [hd]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), h1]
    have hiff := dvd_iff_of_gcd hp hp3 N hN (x := 2 - x) (y := 3 - y) (by omega) (by omega) hk
    unfold Sval
    by_cases hc : 2 - x ≤ a ∧ 3 - y ≤ b
    · rw [if_pos (hiff.mpr hc), if_pos ⟨hxy.1, hxy.2, hc⟩]
      push_cast
      ring
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg (fun h => hc ⟨h.2.2.1, h.2.2.2⟩)]
      simp
  · have h0 : ∀ s : ZMod N, (ind p s.val x y) = 0 := by
      intro s
      unfold ind
      rw [if_neg (fun h => hxy ⟨h.1, h.2.1⟩)]
    simp only [h0, Int.cast_zero, mul_zero, Finset.sum_const_zero]
    unfold Sval
    rw [if_neg (fun h => hxy ⟨h.1, h.2.1⟩)]
    simp

/-- DFT of the gcd-class indicator: a Ramanujan sum, in closed form. -/
theorem dft_gcd_class (hp : p.Prime) (hp3 : p ≠ 3) (hN : N = p ^ 2 * 3 ^ 3) (k : ZMod N)
    {a b : ℕ} (hk : Nat.gcd k.val N = p ^ a * 3 ^ b) (c e : ℕ) (hc : c ≤ 2) (he : e ≤ 3) :
    ∑ s : ZMod N, stdAddChar (-(s * k)) *
        (if Nat.gcd s.val N = p ^ c * 3 ^ e then (1 : ℂ) else 0) = (Lam p c e a b : ℂ) := by
  have h1 : ∀ s : ZMod N, (if Nat.gcd s.val N = p ^ c * 3 ^ e then (1 : ℂ) else 0) =
      ((ind p s.val c e : ℤ) : ℂ) - ((ind p s.val (c + 1) e : ℤ) : ℂ) -
        ((ind p s.val c (e + 1) : ℤ) : ℂ) + ((ind p s.val (c + 1) (e + 1) : ℤ) : ℂ) := by
    intro s
    have h := congrArg (fun z : ℤ => (z : ℂ)) (gcd_class_eq hp hp3 N hN s.val c e hc he)
    push_cast at h
    exact h
  simp_rw [h1, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    dft_ind hp hp3 hN k hk]
  unfold Lam
  push_cast
  ring

end Q3

end ICGBridge

#print axioms ICGBridge.dft_gcd_class
#print axioms ICGBridge.sum_dvd_stdAddChar
