import Research.TaskU.H5.Challenge
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

namespace TaskU.H5.TraceWords
noncomputable section
open Finset Matrix
abbrev K := ZMod 5
abbrev χ : AddChar K ℂ := ZMod.stdAddChar
abbrev Word := K → H

def translate (t : K) (q : Word) : Word := fun j => q (j + t)

def mass (q : Word) : K := ∑ j, (q j).b

def phase (q : Word) : K := ∑ j, ((q j).c + (q j).b * j)

def selector (q : Word) : Matrix K K ℤ :=
  Matrix.of fun i j => if i = (q j).a + j then 1 else 0

def weight (f : H → ℤ) (q : Word) : ℤ := (∏ j, f (q j)) * (selector q).det

def wordMatrix (f : H → ℤ) (v w : K) : Matrix K K ℂ :=
  Matrix.of fun i j => ∑ g : H,
    if i = g.a+j then (f g : ℂ) * χ (v*g.b+w*(g.c+g.b*j)) else 0

theorem mass_translate (t : K) (q : Word) : mass (translate t q) = mass q :=
  Equiv.sum_comp (Equiv.addRight t) (fun j => (q j).b)

theorem phase_translate (t : K) (q : Word) :
    phase (translate t q) = phase q - t * mass q := by
  unfold phase mass translate
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← Equiv.sum_comp (Equiv.addRight t)
    (fun j => (q j).c + (q j).b * j - t * (q j).b)]
  apply sum_congr rfl
  intro j _
  change (q (j+t)).c + (q (j+t)).b * j =
    (q (j+t)).c + (q (j+t)).b * (j+t) - t*(q (j+t)).b
  ring

theorem weight_translate (t : K) (f : H → ℤ) (q : Word) :
    weight f (translate t q) = weight f q := by
  unfold weight
  rw [show (∏ j, f (translate t q j)) = ∏ j, f (q j) from
    Equiv.prod_comp (Equiv.addRight t) (fun j => f (q j))]
  congr 1
  rw [← Matrix.det_reindex_self (Equiv.addRight t).symm (selector q)]
  congr 1
  ext i j
  change (if i = (q (j+t)).a + j then (1:ℤ) else 0) =
    (if i+t = (q (j+t)).a + (j+t) then 1 else 0)
  simp [← add_assoc]

theorem word_expansion (f : H → ℤ) (v w : K) :
    (wordMatrix f v w).det = ∑ q : Word, (weight f q : ℂ) * χ (v*mass q+w*phase q) := by
  classical
  have single (i j : K) (g : H) :
      (if i=g.a+j then (f g:ℂ) * χ (v*g.b+w*(g.c+g.b*j)) else 0) =
      ((if i=g.a+j then 1 else 0) : ℤ) * ((f g : ℂ) * χ (v*g.b+w*(g.c+g.b*j))) := by
    split_ifs <;> simp
  simp only [Matrix.det_apply', wordMatrix, Matrix.of_apply, single, Finset.prod_univ_sum,
    Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro q _
  have addchar_prod (s : Finset K) (a : K → K) : ∏ i ∈ s, χ (a i) = χ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, AddChar.map_add_eq_mul]
  have phase_sum : (∑ j, (v*(q j).b+w*((q j).c+(q j).b*j))) = v*mass q+w*phase q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  simp only [weight, Int.cast_mul, Int.cast_prod, Matrix.det_apply', Int.cast_sum,
    Int.cast_mul, selector, Matrix.of_apply, Int.cast_prod, Finset.prod_mul_distrib,
    addchar_prod, phase_sum, Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro s _
  push_cast
  ring

end
end TaskU.H5.TraceWords
