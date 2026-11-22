import Research.TaskU.H5.CycRoots
import Mathlib.Algebra.Group.TransferInstance

namespace TaskU.H5.Cyc5

private def coordEquiv : V ≃ ℤ × ℤ × ℤ × ℤ where
  toFun x := (x.a,x.b,x.c,x.d)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup V := coordEquiv.addCommGroup

instance : CommRing V where
  mul := mul
  one := scalar 1
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_scalar_one
  one_mul a := by change mul (scalar 1) a = a; rw [mul_comm]; exact mul_scalar_one a
  left_distrib := by intro x y z; change mul x (add y z) = add (mul x y) (mul x z); ext <;> simp [mul,add] <;> ring
  right_distrib := by intro x y z; change mul (add x y) z = add (mul x z) (mul y z); ext <;> simp [mul,add] <;> ring
  zero_mul := by intro x; change mul (scalar 0) x = scalar 0; ext <;> simp [scalar,mul]
  mul_zero := by intro x; change mul x (scalar 0) = scalar 0; ext <;> simp [scalar,mul]
  natCast n := scalar (n : ℤ)
  natCast_zero := rfl
  natCast_succ n := by change scalar _ = add (scalar _) (scalar 1); ext <;> simp [scalar,add]
  intCast := scalar
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

@[simp] theorem cast_eq_scalar (n : ℤ) : (n:V)=scalar n := rfl
theorem add_def (x y : V) : x+y=add x y := rfl
theorem mul_def (x y : V) : x*y=mul x y := rfl
theorem neg_def (x : V) : -x=neg x := rfl

def valueHom (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) : V →+* ℂ where
  toFun x := val x z
  map_zero' := by change val (scalar 0) z = 0; simpa using val_scalar 0 z
  map_one' := by change val (scalar 1) z = 1; simpa using val_scalar 1 z
  map_mul' x y := val_mul x y z hz
  map_add' x y := by simp [add_def,val,add]; ring

end TaskU.H5.Cyc5
