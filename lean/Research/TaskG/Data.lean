import Research.TaskG.Challenge

set_option autoImplicit false
namespace TaskG.Proof
open AxialMSZ.Challenge
abbrev K := ZMod 11
abbrev V := Fin 4 → K

def e (i : Fin 4) : V := Pi.single i 1

def T : Fin 4 → Fin 4 → V :=
  ![ ![ ![1,0,0,0], ![0,0,1,1], ![0,-1,0,-1], ![0,1,1,0]],
     ![ ![0,0,1,1], ![0,1,0,0], ![1,0,0,1], ![-1,0,-1,0]],
     ![ ![0,-1,0,-1], ![1,0,0,1], ![0,0,1,0], ![1,1,0,0]],
     ![ ![0,1,1,0], ![-1,0,-1,0], ![1,1,0,0], ![0,0,0,1]] ]

def μ : V →ₗ[K] V →ₗ[K] V := structProduct T

def β : V →ₗ[K] V →ₗ[K] K where
  toFun u :=
    { toFun := fun v => u 0 * v 0 - u 1 * v 1 + u 2 * v 2 - u 3 * v 3
      map_add' := by intro v w; simp only [Pi.add_apply]; ring
      map_smul' := by intro c v; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change (u 0 + v 0) * w 0 - (u 1 + v 1) * w 1 +
      (u 2 + v 2) * w 2 - (u 3 + v 3) * w 3 =
      (u 0*w 0-u 1*w 1+u 2*w 2-u 3*w 3) +
      (v 0*w 0-v 1*w 1+v 2*w 2-v 3*w 3)
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change (c*u 0)*v 0-(c*u 1)*v 1+(c*u 2)*v 2-(c*u 3)*v 3 =
      c*(u 0*v 0-u 1*v 1+u 2*v 2-u 3*v 3)
    ring

def perm (i : Fin 4) : Fin 4 := ![1,0,3,2] i

def g : V ≃ₗ[K] V where
  toFun u := fun i => u (perm i)
  invFun u := fun i => u (perm i)
  left_inv := by intro u; ext i; fin_cases i <;> rfl
  right_inv := by intro u; ext i; fin_cases i <;> rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def F : FusionLaw K where
  carrier := {1,5,7,10}
  star l m := if l = 1 then {m} else if m = 1 then {l} else
    if l = 10 then (if m = 10 then {1,5,7} else {10}) else
    if m = 10 then {10} else if l = m then {1,5,7} else {5,7}

def X : Set V := Set.range e

def ev (r : Fin 4) : K := ![1,5,7,10] r

def eig (i r : Fin 4) : V :=
  ![ ![ ![1,0,0,0], ![0,1,7,1], ![0,1,5,1], ![0,-1,0,1]],
     ![ ![0,1,0,0], ![8,0,8,1], ![9,0,9,1], ![-1,0,1,0]],
     ![ ![0,0,1,0], ![7,1,0,1], ![5,1,0,1], ![0,-1,0,1]],
     ![ ![0,0,0,1], ![1,7,1,0], ![1,5,1,0], ![-1,0,1,0]] ] i r

@[simp] theorem e_apply (i j : Fin 4) : e i j = if j = i then 1 else 0 := by
  simp [e, Pi.single_apply, eq_comm]

@[simp] theorem β_apply (u v : V) : β u v =
    u 0 * v 0 - u 1 * v 1 + u 2 * v 2 - u 3 * v 3 := rfl

theorem μ_apply (u v : V) : μ u v =
  ![ u 0*v 0 + u 1*v 2 - u 1*v 3 + u 2*v 1 + u 2*v 3 - u 3*v 1 + u 3*v 2,
     -u 0*v 2 + u 0*v 3 + u 1*v 1 - u 2*v 0 + u 2*v 3 + u 3*v 0 + u 3*v 2,
     u 0*v 1 + u 0*v 3 + u 1*v 0 - u 1*v 3 + u 2*v 2 + u 3*v 0 - u 3*v 1,
     u 0*v 1 - u 0*v 2 + u 1*v 0 + u 1*v 2 - u 2*v 0 + u 2*v 1 + u 3*v 3 ] := by
  ext k; fin_cases k <;> simp [μ, structProduct, T, Fin.sum_univ_succ] <;> ring

@[simp] theorem μ_e (i j : Fin 4) : μ (e i) (e j) = T i j := by
  ext k; fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [μ_apply, T, e, Pi.single_apply]

theorem basis_sum (u : V) : (∑ i : Fin 4, u i • e i) = u := by
  ext k; fin_cases k <;> simp [e, Pi.single_apply]

theorem μ_comm : IsCommutative μ := by
  intro u v; rw [μ_apply, μ_apply]; ext k; fin_cases k <;> simp <;> ring

end TaskG.Proof
