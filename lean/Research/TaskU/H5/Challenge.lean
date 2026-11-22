import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

namespace TaskU.H5

/-- Coordinates of x^a y^b z^c, with yx = xyz. -/
structure H where
  a : ZMod 5
  b : ZMod 5
  c : ZMod 5
  deriving DecidableEq, Fintype

private theorem ext_coord {g h : H} (ha : g.a = h.a) (hb : g.b = h.b)
    (hc : g.c = h.c) : g = h := by cases g; cases h; simp_all

instance : Mul H where
  mul g h := ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.b * h.a⟩
instance : One H where
  one := ⟨0, 0, 0⟩
instance : Inv H where
  inv g := ⟨-g.a, -g.b, -g.c + g.b * g.a⟩
private theorem a_mul (g h : H) : (g*h).a = g.a+h.a := rfl
private theorem b_mul (g h : H) : (g*h).b = g.b+h.b := rfl
private theorem c_mul (g h : H) : (g*h).c = g.c+h.c+g.b*h.a := rfl

instance : Group H where
  mul_assoc g h k := by
    apply ext_coord <;> simp only [a_mul, b_mul, c_mul] <;> ring
  one_mul g := by
    apply ext_coord
    · change 0 + g.a = g.a; simp
    · change 0 + g.b = g.b; simp
    · change 0 + g.c + 0 * g.a = g.c; simp
  mul_one g := by
    apply ext_coord
    · change g.a + 0 = g.a; simp
    · change g.b + 0 = g.b; simp
    · change g.c + 0 + g.b * 0 = g.c; simp
  inv_mul_cancel g := by
    apply ext_coord
    · change -g.a + g.a = 0; simp
    · change -g.b + g.b = 0; simp
    · change -g.c + g.b*g.a + g.c + -g.b*g.a = 0; ring

def x : H := ⟨1, 0, 0⟩
def y : H := ⟨0, 1, 0⟩

/-- The integer coefficients of 1 + x + y + y² + xy². -/
def witness (g : H) : ℤ :=
  (if g = 1 then 1 else 0) + (if g = x then 1 else 0) +
  (if g = y then 1 else 0) + (if g = y ^ 2 then 1 else 0) +
  (if g = x * y ^ 2 then 1 else 0)

/-- Integer group determinant, with one unrestricted coefficient per group element. -/
noncomputable def groupDet (f : H → ℤ) : ℤ :=
  Matrix.det (Matrix.of fun g h : H => f (g * h⁻¹))

namespace Challenge

def witnessValue : Prop := groupDet witness = 11 * 5 ^ 28

def leastPositiveMultiple : Prop :=
  IsLeast {m : ℤ | 0 < m ∧ 5 ∣ m ∧ ∃ f : H → ℤ, groupDet f = m} (11 * 5 ^ 28)

end Challenge
end TaskU.H5
