import Research.TaskP.PrimeMedialRacks.Challenge

namespace TaskP.PrimeMedialRacks

open Challenge

def affine {p : ℕ} (k : ZMod p) : Operation (ZMod p) :=
  fun x y => (1 - k) * x + k * y

variable {p : ℕ} [Fact p.Prime]

theorem affine_isRack {k : ZMod p} (hk : k ≠ 0) : IsRack (affine k) := by
  constructor
  · intro x
    constructor
    · intro y z h
      exact mul_left_cancel₀ hk (add_left_cancel h)
    · intro y
      refine ⟨(y - (1-k)*x) / k, ?_⟩
      unfold affine
      field_simp
      ring
  · intro x y z
    unfold affine
    ring

theorem affine_idempotent (k : ZMod p) : Idempotent (affine k) := by
  intro x
  unfold affine
  ring

theorem affine_medial (k : ZMod p) : Medial (affine k) := by
  intro x u v y
  unfold affine
  ring

theorem affine_nonreductive {k : ZMod p} (hk : k ≠ 1) : ¬ TwoReductive (affine k) := by
  intro h
  have htest := h 1 0 0 0
  simp [affine] at htest
  exact (sub_ne_zero.mpr hk.symm) htest

/-- An isomorphism intertwines the two affine operations. After subtracting its value at
zero, it is additive, since the two nonzero weights at the source are surjective. -/
theorem affine_parameter_unique {k l : ZMod p} (hk₀ : k ≠ 0) (hk₁ : k ≠ 1)
    (h : Isomorphic (affine k) (affine l)) : k = l := by
  obtain ⟨e, he⟩ := h
  have he' (x y : ZMod p) :
      e ((1-k)*x + k*y) = (1-l)*e x + l*e y := he x y
  have left (x : ZMod p) : e ((1-k)*x) = (1-l)*e x + l*e 0 := by
    simpa using he' x 0
  have right (y : ZMod p) : e (k*y) = (1-l)*e 0 + l*e y := by
    simpa using he' 0 y
  have hweight : 1 - k ≠ 0 := sub_ne_zero.mpr hk₁.symm
  have add (a b : ZMod p) : e (a+b) - e 0 = (e a-e 0) + (e b-e 0) := by
    obtain ⟨x, rfl⟩ := mul_left_surjective₀ hweight a
    obtain ⟨y, rfl⟩ := mul_left_surjective₀ hk₀ b
    rw [he', left, right]
    ring
  let f : ZMod p →+ ZMod p := {
    toFun := fun x => e x - e 0
    map_zero' := sub_self _
    map_add' := add }
  have scalar (x : ZMod p) : f x = x * f 1 := by
    conv_lhs => rw [← x.intCast_zmod_cast, ← zsmul_one (x.cast : ℤ), map_zsmul]
    rw [zsmul_eq_mul, x.intCast_zmod_cast]
  have hne : f 1 ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => one_ne_zero (e.injective h))
  apply mul_right_cancel₀ hne
  rw [← scalar k]
  change e k - e 0 = l * (e 1 - e 0)
  have hk := right 1
  rw [mul_one] at hk
  rw [hk]
  ring

end TaskP.PrimeMedialRacks
