import Research.TaskU.H5.TraceWords
import Mathlib.Algebra.Field.ZMod

namespace TaskU.H5.TraceWords
noncomputable section
open Finset Matrix
local instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

def moment (q : Word) : K := ∑ j, (j * (q j).c + (j^2/2) * (q j).b)

theorem moment_translate (t : K) (q : Word) :
    moment (translate t q) = moment q - t*phase q + t^2/2 * mass q := by
  unfold moment translate phase mass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [← Equiv.sum_comp (Equiv.addRight t)
    (fun j => j*(q j).c + j^2/2*(q j).b - t*((q j).c+(q j).b*j) + (t^2/2)*(q j).b)]
  apply sum_congr rfl
  intro j _
  change j*(q (j+t)).c+j^2/2*(q (j+t)).b =
    (j+t)*(q (j+t)).c + (j+t)^2/2*(q (j+t)).b -
    t*((q (j+t)).c+(q (j+t)).b*(j+t)) + (t^2/2)*(q (j+t)).b
  have h2 : (2:K) ≠ 0 := by decide
  field_simp
  ring

def spin (t : K) : Word ≃ Word where
  toFun := translate t
  invFun := translate (-t)
  left_inv q := by funext j; simp [translate, add_assoc]
  right_inv q := by funext j; simp [translate, add_assoc]

private theorem orthogonal (b : K) : ∑ t : K, χ (b*t) = if b=0 then 5 else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 5 h)

def integerAverage (f : H → ℤ) : ℤ :=
  ∑ q : Word, if mass q=0 then weight f q else 0

theorem average_eq (f : H → ℤ) :
    ∑ v : K, (wordMatrix f v 0).det = 5*(integerAverage f : ℂ) := by
  classical
  simp only [word_expansion, zero_mul, add_zero]
  rw [Finset.sum_comm]
  simp only [integerAverage, Int.cast_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro q _
  simp_rw [mul_comm _ (mass q)]
  rw [← Finset.mul_sum, orthogonal]
  by_cases h : mass q=0 <;> simp [h]
  all_goals ring

theorem projected_expansion (f : H → ℤ) :
    (wordMatrix f 0 1).det =
    ∑ q : Word, if mass q=0 then (weight f q:ℂ)*χ (phase q) else 0 := by
  classical
  rw [word_expansion]
  simp only [zero_mul, one_mul, zero_add]
  have spun (t : K) :
      ∑ q : Word, (weight f (translate t q):ℂ)*χ (phase (translate t q)) =
      ∑ q : Word, (weight f q:ℂ)*χ (phase q) :=
    Equiv.sum_comp (spin t) (fun q => (weight f q:ℂ)*χ (phase q))
  have evalsum (q : Word) :
    ∑ t : K, (weight f q:ℂ)*χ (phase q - t*mass q) =
      5*(if mass q=0 then (weight f q:ℂ)*χ (phase q) else 0) := by
    have point (t : K) : χ (phase q - t * mass q) = χ (phase q) * χ ((-mass q)*t) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    simp only [point, ← mul_assoc, ← Finset.mul_sum, orthogonal]
    by_cases h : mass q=0 <;> simp [h]
    all_goals ring
  have iden' : ∑ q : Word, ∑ t : K, (weight f q:ℂ)*χ (phase q-t*mass q) =
        ∑ _ : K, ∑ q : Word, (weight f q:ℂ)*χ (phase q) := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro t _
    simpa only [weight_translate, phase_translate] using spun t
  simp_rw [evalsum] at iden'
  rw [← Finset.mul_sum] at iden'
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat] at iden'
  linear_combination -iden'/5

def binWeight (f : H → ℤ) (e : K) : ℤ :=
  ∑ q : Word, if mass q=0 ∧ phase q=e then weight f q else 0

def anchoredWeight (f : H → ℤ) (e : K) : ℤ :=
  ∑ q : Word, if mass q=0 ∧ phase q=e ∧ moment q=0 then weight f q else 0

theorem binWeight_eq_five (f : H → ℤ) {e : K} (he : e ≠ 0) :
    binWeight f e = 5*anchoredWeight f e := by
  classical
  let v (q : Word) := if mass q=0 ∧ phase q=e ∧ moment q=0 then weight f q else 0
  have proj (q : Word) : ∑ t : K, v (translate t q) =
      if mass q=0 ∧ phase q=e then weight f q else 0 := by
    by_cases hb : mass q=0
    · by_cases hE : phase q=e
      · have point (t : K) :
          (moment q - t*e = 0) ↔ t = moment q/e := by
          rw [eq_div_iff he]; constructor <;> intro h <;> linear_combination (norm := ring) -h
        simp [v, mass_translate, phase_translate, moment_translate, weight_translate,
          hb, hE, point]
      · simp [v, mass_translate, phase_translate, moment_translate, hb, hE]
    · simp [v, mass_translate, hb]
  unfold binWeight
  simp_rw [← proj]
  rw [Finset.sum_comm]
  have hs (t : K) : ∑ q : Word, v (translate t q) = ∑ q : Word, v q :=
    Equiv.sum_comp (spin t) v
  simp_rw [hs]
  simp [anchoredWeight, v, ZMod.card]

end
end TaskU.H5.TraceWords
