import Research.TaskG.Data

set_option autoImplicit false
namespace TaskG.Proof
open AxialMSZ.Challenge TaskG.Challenge

theorem g_mul : IsAlgebraAutomorphism μ g := by
  intro u v
  ext i
  fin_cases i <;> simp [g, perm, μ_apply] <;> ring

theorem g_involutive (u : V) : g (g u) = u := by
  ext i; fin_cases i <;> rfl

theorem g_scales (u v : V) : β (g u) (g v) = (-1 : K) * β u v := by
  simp [β_apply, g, perm]
  ring

theorem scale_nonzero : (-1 : K) ≠ 0 := by norm_num

theorem scale_nontrivial : (-1 : K) ≠ 1 := by decide +kernel

theorem X_finite : X.Finite := Set.finite_range e

theorem X_nonempty : X.Nonempty := ⟨e 0, ⟨0, rfl⟩⟩

example : μ (e 0) (e 1) = e 2 + e 3 := by
  rw [μ_e]; ext k; fin_cases k <;> norm_num [T, e, Pi.single_apply]

example : β (e 0) (e 0) = 1 := by norm_num [e, Pi.single_apply]
example : β (g (e 0)) (g (e 0)) = -1 := by
  rw [g_scales]; norm_num [e, Pi.single_apply]

#print axioms TaskG.Proof.g_mul
#print axioms TaskG.Proof.g_involutive
#print axioms TaskG.Proof.g_scales
end TaskG.Proof
