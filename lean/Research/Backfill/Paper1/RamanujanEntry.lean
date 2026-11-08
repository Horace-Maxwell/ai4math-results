import Research.Backfill.Paper1.Additional
import Research.Backfill.Paper1.SupplementStatements
import Research.ICGGeneralBridge

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral ZMod
namespace NarrowRamanujan

lemma char_re (N u : ℕ) [NeZero N] (s : ZMod N) :
    (stdAddChar (-(s * (u : ZMod N)))).re =
      Real.cos (2 * Real.pi * ((s.val * u : ℕ) : ℝ) / (N : ℝ)) := by
  have hcast : -(s * (u : ZMod N)) = ((-((s.val : ℤ) * u) : ℤ) : ZMod N) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hcast, stdAddChar_coe]
  have he : (2 * (Real.pi : ℂ) * Complex.I * ((-((s.val : ℤ) * u) : ℤ) : ℂ) / N) =
      (((-(2 * Real.pi * ((s.val * u : ℕ) : ℝ) / (N : ℝ))) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

lemma real_eq_character (N u : ℕ) [NeZero N] :
    NarrowSupplement.ramanujanReal N u =
      (∑ s : ZMod N, if Nat.Coprime s.val N then
        stdAddChar (-(s * (u : ZMod N))) else 0).re := by
  rw [Complex.re_sum]
  simp only [apply_ite Complex.re, Complex.zero_re, char_re]
  exact (ICGBridge.sum_zmod_val (fun l => if Nat.Coprime l N then
    Real.cos (2 * Real.pi * ((l * u : ℕ) : ℝ) / (N : ℝ)) else 0)).symm

lemma real_prime_power (p : ℕ) (hp : p.Prime) (m i : ℕ) :
    NarrowSupplement.ramanujanReal (p ^ m) (p ^ i) = ramX p m i := by
  by_cases hm0 : m = 0
  · subst m
    norm_num [NarrowSupplement.ramanujanReal, ramX]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  let : NeZero (p ^ m) := ⟨pow_ne_zero m hp.ne_zero⟩
  let k : ZMod (p ^ m) := (p ^ i : ℕ)
  have hfactor : p * p ^ (m - 1) = p ^ m := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  have hcop (s : ZMod (p ^ m)) : Nat.Coprime s.val (p ^ m) ↔ ¬ p ∣ s.val := by
    rw [Nat.coprime_pow_right_iff hm, Nat.coprime_comm, hp.coprime_iff_not_dvd]
  have hsum : (∑ s : ZMod (p ^ m), if Nat.Coprime s.val (p ^ m) then
      stdAddChar (-(s * k)) else 0) =
      (if p ^ m ∣ k.val then ((p ^ m : ℕ) : ℂ) else 0) -
      (if p ^ (m - 1) ∣ k.val then ((p ^ (m - 1) : ℕ) : ℂ) else 0) := by
    rw [← ICGBridge.sum_dvd_stdAddChar 1 (p ^ m) (by simp) k,
      ← ICGBridge.sum_dvd_stdAddChar p (p ^ (m - 1)) hfactor k, ← sum_sub_distrib]
    apply sum_congr rfl
    intro s _hs
    by_cases hd : p ∣ s.val <;> simp [hcop, hd]
  have hd (d : ℕ) (hdN : d ∣ p ^ m) : d ∣ k.val ↔ d ∣ p ^ i := by
    dsimp [k]
    rw [ZMod.val_natCast, Nat.dvd_mod_iff hdN]
  rw [real_eq_character]
  change (∑ s : ZMod (p ^ m), if Nat.Coprime s.val (p ^ m) then
    stdAddChar (-(s * k)) else 0).re = _
  have hr := ramX_eq_Spow p (a := m) (c := 0) (by omega) i
  simp only [Nat.sub_zero] at hr
  rw [hsum, hr]
  simp only [Complex.sub_re, apply_ite Complex.re, Complex.natCast_re, Complex.zero_re,
    hd (p ^ m) dvd_rfl, hd (p ^ (m - 1)) (Nat.pow_dvd_pow p (by omega)),
    Nat.pow_dvd_pow_iff_le_right hp.one_lt, Spow, Nat.zero_le,
    Nat.sub_zero, zero_add, show 1 ≤ m by omega, true_and]
  push_cast
  rfl

lemma phi_prime_power (p : ℕ) (hp : p.Prime) (m : ℕ) :
    (Nat.totient (p ^ m) : ℝ) = phiX p m := by
  by_cases hm : m = 0
  · subst m; norm_num [phiX]
  · rw [Nat.totient_prime_pow hp (Nat.pos_of_ne_zero hm), phiX, ite_eq_right hm]
    push_cast [Nat.cast_sub hp.one_le]
    rfl

end NarrowRamanujan

theorem check_RamanujanEntry : NarrowSupplement.RamanujanEntry := by
  intro p k i j hp _hk hi hj
  rw [Additional.tEntry_eq_Tent p k i j hi hj]
  unfold Tent
  rw [NarrowRamanujan.real_prime_power p hp (k - j) i,
    NarrowRamanujan.phi_prime_power p hp (k - i)]

#print axioms check_RamanujanEntry
end CodexPaper1
