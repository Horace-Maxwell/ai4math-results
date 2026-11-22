import Research.TaskU.H5.Challenge
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators
abbrev F := ZMod 5
abbrev ch : AddChar F ℂ := ZMod.stdAddChar

def coords : H ≃ F × (F × F) where
  toFun g := (g.a, (g.b, g.c))
  invFun v := ⟨v.1, v.2.1, v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sumH {R : Type*} [AddCommMonoid R] (f : H → R) :
    ∑ g, f g = ∑ a : F, ∑ b : F, ∑ c : F, f ⟨a,b,c⟩ := by
  rw [← coords.symm.sum_comp f]
  simp [Fintype.sum_prod_type, coords]

theorem orthog (u : F) : ∑ b : F, ch (u*b) = if u=0 then 5 else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 5 h)

def T (i h : H) : ℂ :=
  if h.a=i.a then ch (i.b*h.b+i.c*h.c) else 0

def U (g j : H) : ℂ :=
  if g.a=j.a then ch (-(j.b*g.b+j.c*g.c)) else 0

theorem inverseFourier :
    (Matrix.of U : Matrix H H ℂ) * Matrix.of T = 25 • (1 : Matrix H H ℂ) := by
  ext g h : 1
  rw [Matrix.mul_apply, sumH]
  simp only [Matrix.of_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.one_apply]
  rw [Finset.sum_eq_single g.a]
  · by_cases ha : g.a = h.a
    · have eqc (b c : F) :
          ch (-(b*g.b+c*g.c)) * ch (b*h.b+c*h.c) =
            ch ((h.b-g.b)*b) * ch ((h.c-g.c)*c) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
      simp only [T, U, ha, eq_self, ite_true, eqc]
      simp_rw [← Finset.mul_sum, orthog, ← Finset.sum_mul, orthog]
      have he : g = h ↔ h.b=g.b ∧ h.c=g.c := by
        cases g; cases h
        simp_all only [H.mk.injEq, true_and, eq_comm]
      simp only [he]
      by_cases hb : h.b=g.b <;> by_cases hc : h.c=g.c <;>
        simp [sub_eq_zero, hb, hc]
      all_goals norm_num
    · have hn : g ≠ h := fun he => ha (congrArg H.a he)
      simp [T, U, hn, Ne.symm ha]
  · intro a _ hne
    simp [U, Ne.symm hne]
  · simp

/-- The block on horizontal and central frequencies v and w. -/
def frequencyBlock (f : H → ℤ) (v w : F) : Matrix F F ℂ :=
  Matrix.of fun i j => ∑ g : H,
    if i = g.a+j then (f g : ℂ) * ch (v*g.b+w*(g.c+g.b*j)) else 0

def blocks (f : H → ℤ) : Matrix H H ℂ :=
  Matrix.of fun i j =>
    if (i.b,i.c)=(j.b,j.c) then frequencyBlock f i.b i.c i.a j.a else 0

end
end TaskU.H5
