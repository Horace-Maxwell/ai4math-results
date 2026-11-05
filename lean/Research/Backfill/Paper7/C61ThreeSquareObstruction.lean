import Mathlib

/-!
Source-only draft. No Lean compilation, checker run, or axiom output has been
obtained for this file. The declarations below have complete proof bodies and
are pending kernel validation.

The obstruction is divisibility: if 11 divides three times the second moment
minus the square of the first moment of three integers, then 121 divides it.
The three required discriminants, 572, 506 and 704, violate this implication.
-/

namespace Paper7C61ThreeSquareObstruction

/-- The Eisenstein quadratic form has no nonzero isotropic vector modulo 11.
The proof uses Frobenius and polynomial identities, with no residue enumeration. -/
theorem eisenstein_norm_zero_zmod_eleven (u v : ZMod 11)
    (h : u ^ 2 + u * v + v ^ 2 = 0) : u = 0 ∧ v = 0 := by
  let : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hc : u ^ 3 = v ^ 3 := by
    linear_combination (u - v) * h
  have h12 : u ^ 12 = v ^ 12 := by
    have h4 := congrArg (fun w : ZMod 11 => w ^ 4) hc
    simpa only [← pow_mul] using h4
  have hs : u ^ 2 = v ^ 2 := by
    calc
      u ^ 2 = u ^ 11 * u := by rw [ZMod.pow_card]; ring
      _ = u ^ 12 := by ring
      _ = v ^ 12 := h12
      _ = v ^ 11 * v := by ring
      _ = v ^ 2 := by rw [ZMod.pow_card]; ring
  have hf : (u - v) * (u + v) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hf with huv | huv
  · have ht : (3 : ZMod 11) * v ^ 2 = 0 := by
      linear_combination h - (u + 2 * v) * huv
    have hv2 : v ^ 2 = 0 :=
      (mul_eq_zero.mp ht).resolve_left (by decide : (3 : ZMod 11) ≠ 0)
    have hv : v = 0 := sq_eq_zero_iff.mp hv2
    have hu : u = 0 := by simpa [hv] using huv
    exact ⟨hu, hv⟩
  · have hv2 : v ^ 2 = 0 := by
      linear_combination h - u * huv
    have hv : v = 0 := sq_eq_zero_iff.mp hv2
    have hu : u = 0 := by simpa [hv] using huv
    exact ⟨hu, hv⟩

/-- Vanishing of the three-variable discriminant modulo 11 forces both
independent coordinate differences to vanish modulo 11. -/
theorem eleven_dvd_discriminant_forces_differences (x y z : ℤ)
    (h : (11 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2) :
    (11 : ℤ) ∣ x - z ∧ (11 : ℤ) ∣ z - y := by
  let : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hc :
      ((3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 : ℤ) : ZMod 11) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).2 h
  push_cast at hc
  have hn : (2 : ZMod 11) *
      (((x : ZMod 11) - z) ^ 2 +
        ((x : ZMod 11) - z) * ((z : ZMod 11) - y) +
        ((z : ZMod 11) - y) ^ 2) = 0 := by
    linear_combination hc
  have hn0 :
      ((x : ZMod 11) - z) ^ 2 +
        ((x : ZMod 11) - z) * ((z : ZMod 11) - y) +
        ((z : ZMod 11) - y) ^ 2 = 0 :=
    (mul_eq_zero.mp hn).resolve_left (by decide : (2 : ZMod 11) ≠ 0)
  obtain ⟨hx, hy⟩ :=
    eisenstein_norm_zero_zmod_eleven ((x : ZMod 11) - z) ((z : ZMod 11) - y) hn0
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x - z) 11).1
    simpa only [Int.cast_sub] using hx
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd (z - y) 11).1
    simpa only [Int.cast_sub] using hy

/-- A factor of 11 in this three-variable discriminant always occurs at least
twice. This statement has no sign or size hypotheses on the integers. -/
theorem eleven_square_dvd_discriminant (x y z : ℤ)
    (h : (11 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2) :
    (121 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by
  obtain ⟨hx, hy⟩ := eleven_dvd_discriminant_forces_differences x y z h
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨2 * (a ^ 2 + a * b + b ^ 2), ?_⟩
  calc
    3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 =
        2 * ((x - z) ^ 2 + (x - z) * (z - y) + (z - y) ^ 2) := by ring
    _ = 121 * (2 * (a ^ 2 + a * b + b ^ 2)) := by rw [ha, hb]; ring

/-- There are no three integers of sum 34 and squared sum 576. -/
theorem not_sum34_squares576 (x y z : ℤ)
    (hs : x + y + z = 34) (hq : x ^ 2 + y ^ 2 + z ^ 2 = 576) : False := by
  have hd : (11 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by
    rw [hs, hq]
    norm_num
  have h121 := eleven_square_dvd_discriminant x y z hd
  rw [hs, hq] at h121
  norm_num at h121

/-- There are no three integers of sum 35 and squared sum 577. -/
theorem not_sum35_squares577 (x y z : ℤ)
    (hs : x + y + z = 35) (hq : x ^ 2 + y ^ 2 + z ^ 2 = 577) : False := by
  have hd : (11 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by
    rw [hs, hq]
    norm_num
  have h121 := eleven_square_dvd_discriminant x y z hd
  rw [hs, hq] at h121
  norm_num at h121

/-- There are no three integers of sum 32 and squared sum 576. -/
theorem not_sum32_squares576 (x y z : ℤ)
    (hs : x + y + z = 32) (hq : x ^ 2 + y ^ 2 + z ^ 2 = 576) : False := by
  have hd : (11 : ℤ) ∣ 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by
    rw [hs, hq]
    norm_num
  have h121 := eleven_square_dvd_discriminant x y z hd
  rw [hs, hq] at h121
  norm_num at h121

end Paper7C61ThreeSquareObstruction

#print axioms Paper7C61ThreeSquareObstruction.eisenstein_norm_zero_zmod_eleven
#print axioms Paper7C61ThreeSquareObstruction.eleven_dvd_discriminant_forces_differences
#print axioms Paper7C61ThreeSquareObstruction.eleven_square_dvd_discriminant
#print axioms Paper7C61ThreeSquareObstruction.not_sum34_squares576
#print axioms Paper7C61ThreeSquareObstruction.not_sum35_squares577
#print axioms Paper7C61ThreeSquareObstruction.not_sum32_squares576
