import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

namespace TaskU.H5.Cyc5

@[ext] structure V where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def scalar (n : ℤ) : V := ⟨n,0,0,0⟩
def pi : V := ⟨1,-1,0,0⟩
def root : V := ⟨0,1,0,0⟩
def add (v w : V) : V := ⟨v.a+w.a,v.b+w.b,v.c+w.c,v.d+w.d⟩
def neg (v : V) : V := ⟨-v.a,-v.b,-v.c,-v.d⟩
def sumCoeff (v : V) : ℤ := v.a + v.b + v.c + v.d

/-- Multiplication in the basis 1,z,z²,z³ with Φ₅(z)=0. -/
def mul (v w : V) : V :=
  let e := v.b*w.d + v.c*w.c + v.d*w.b
  ⟨v.a*w.a+v.c*w.d+v.d*w.c-e, v.b*w.a+v.a*w.b+v.d*w.d-e,
   v.a*w.c+v.b*w.b+v.c*w.a-e, v.a*w.d+v.b*w.c+v.c*w.b+v.d*w.a-e⟩

def conj (v : V) : V := ⟨v.a-v.b,-v.b,v.d-v.b,v.c-v.b⟩
def sigma2 (v : V) : V := ⟨v.a-v.c,v.d-v.c,v.b-v.c,-v.c⟩
def sigma3 (v : V) : V := conj (sigma2 v)

/-- The quadratic norm of the absolute square in the real subfield. -/
def normForm {R : Type*} [CommRing R] (a b c d : R) : R :=
  let s := a*c + b*d + a*d
  let A := a^2 + b^2 + c^2 + d^2 - s
  let B := a*b + b*c + c*d - s
  A^2 - A*B - B^2

def norm (v : V) : ℤ := normForm v.a v.b v.c v.d

def val (v : V) (z : ℂ) : ℂ := v.a + v.b*z + v.c*z^2 + v.d*z^3

noncomputable def zeta : ℂ := ZMod.stdAddChar (1 : ZMod 5)

lemma zeta_pow (n : ℕ) : zeta ^ n = ZMod.stdAddChar (n : ZMod 5) := by
  rw [zeta, ← AddChar.map_nsmul_eq_pow]
  simp

lemma zeta_rel : 1 + zeta + zeta^2 + zeta^3 + zeta^4 = 0 := by
  have hp : zeta^5 = 1 := by
    rw [zeta_pow, show ((5 : ℕ) : ZMod 5) = 0 by decide, AddChar.map_zero_eq_one]
  have hn : zeta ≠ 1 := by
    intro h
    have hx : ZMod.stdAddChar (1 : ZMod 5) = ZMod.stdAddChar (0 : ZMod 5) := by
      simpa [zeta] using h
    exact (by decide : (1 : ZMod 5) ≠ 0) ((ZMod.injective_stdAddChar (N := 5)) hx)
  have h := show (zeta-1)*(1+zeta+zeta^2+zeta^3+zeta^4)=0 by linear_combination hp
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)

lemma mul_comm (v w : V) : mul v w = mul w v := by
  ext <;> simp [mul] <;> ring

lemma mul_assoc (u v w : V) : mul (mul u v) w = mul u (mul v w) := by
  ext <;> simp [mul] <;> ring

@[simp] lemma mul_scalar_one (v : V) : mul v (scalar 1) = v := by
  ext <;> simp [mul,scalar]

lemma conj_conj (v : V) : conj (conj v) = v := by
  ext <;> simp [conj]

lemma conj_mul (v w : V) : conj (mul v w) = mul (conj v) (conj w) := by
  ext <;> simp [conj,mul] <;> ring

lemma norm_prod (v : V) :
    mul (mul v (conj v)) (mul (sigma2 v) (sigma3 v)) = scalar (norm v) := by
  ext <;> simp [norm,normForm,mul,conj,sigma2,sigma3,scalar] <;> ring

lemma norm_mul (v w : V) : norm (mul v w) = norm v * norm w := by
  simp [norm, normForm, mul]
  ring

lemma norm_pi : norm pi = 5 := by decide

lemma pi_dvd_iff (v : V) : (∃ w, v = mul pi w) ↔ 5 ∣ sumCoeff v := by
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w.d, by simp [pi,mul,sumCoeff]; ring⟩
  · rintro ⟨k,h⟩
    refine ⟨⟨v.a-k, v.a+v.b-2*k, v.a+v.b+v.c-3*k, k⟩, ?_⟩
    ext <;> simp [pi,mul] <;> simp [sumCoeff] at h <;> omega

end TaskU.H5.Cyc5
