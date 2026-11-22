import Research.TaskP.PrimeMedialRacks.DisplacementData

namespace TaskP.PrimeMedialRacks

open Challenge

variable {α : Type*} {op : Operation α} (hr : IsRack op)

def rackAutomorphisms (op : Operation α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x y, g (op x y) = op (g x) (g y)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (congrArg g (hh x y)).trans (hg _ _)
  inv_mem' := by
    intro g hg x y
    apply g.injective
    change g (g.symm _) = g (op (g.symm x) (g.symm y))
    rw [hg (g.symm x) (g.symm y)]
    simp

theorem leftPerm_mem_aut (x : α) : leftPerm hr x ∈ rackAutomorphisms op :=
  hr.2 x

theorem conjugate_leftPerm {g : Equiv.Perm α} (hg : g ∈ rackAutomorphisms op) (x : α) :
    MulAut.conj g (leftPerm hr x) = leftPerm hr (g x) := by
  ext y
  change g (op x (g.symm y)) = op (g x) y
  rw [hg, g.apply_symm_apply]

noncomputable def displacement (base : α) : Subgroup (Equiv.Perm α) :=
  Subgroup.closure (Set.range (fun u => leftPerm hr u * (leftPerm hr base)⁻¹))

theorem displacement_generator (base u : α) :
    leftPerm hr u * (leftPerm hr base)⁻¹ ∈ displacement hr base :=
  Subgroup.subset_closure ⟨u, rfl⟩

theorem difference_mem (base u v : α) :
    leftPerm hr u * (leftPerm hr v)⁻¹ ∈ displacement hr base := by
  have h := (displacement hr base).mul_mem (displacement_generator hr base u)
    ((displacement hr base).inv_mem (displacement_generator hr base v))
  simpa [mul_assoc] using h

theorem displacement_acts (base : α) : displacement hr base ≤ rackAutomorphisms op := by
  rw [displacement, Subgroup.closure_le]
  rintro _ ⟨u, rfl⟩
  exact (rackAutomorphisms op).mul_mem (leftPerm_mem_aut hr u)
    ((rackAutomorphisms op).inv_mem (leftPerm_mem_aut hr base))

theorem displacement_normalizes (base x : α) {d : Equiv.Perm α} (hd : d ∈ displacement hr base) :
    leftPerm hr x * d * (leftPerm hr x)⁻¹ ∈ displacement hr base := by
  let c := MulAut.conj (leftPerm hr x)
  have hc : displacement hr base ≤ (displacement hr base).comap c.toMonoidHom := by
    rw [displacement, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    change MulAut.conj (leftPerm hr x) (leftPerm hr u * (leftPerm hr base)⁻¹) ∈ displacement hr base
    rw [map_mul, map_inv, conjugate_leftPerm hr (leftPerm_mem_aut hr x),
      conjugate_leftPerm hr (leftPerm_mem_aut hr x)]
    exact difference_mem hr _ _ _
  exact hc hd

theorem displacement_commutes (hm : Medial op) (base : α) :
    ∀ d ∈ displacement hr base, ∀ e ∈ displacement hr base, Commute d e := by
  let T := leftPerm hr base
  have generators (u v : α) :
      Commute (leftPerm hr u * T⁻¹) (leftPerm hr v * T⁻¹) := by
    have h : leftPerm hr (op base u) * leftPerm hr v =
        leftPerm hr (op base v) * leftPerm hr u := by
      ext y
      exact hm base u v y
    have hu := conjugate_leftPerm hr (leftPerm_mem_aut hr base) u
    have hv := conjugate_leftPerm hr (leftPerm_mem_aut hr base) v
    change T * leftPerm hr u * T⁻¹ = leftPerm hr (op base u) at hu
    change T * leftPerm hr v * T⁻¹ = leftPerm hr (op base v) at hv
    rw [← hu, ← hv] at h
    have := congrArg (fun z => T⁻¹ * z * T⁻¹) h
    simpa [Commute, SemiconjBy, mul_assoc] using this
  have : IsMulCommutative (displacement hr base) :=
    Subgroup.isMulCommutative_closure (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _
      exact generators u v)
  intro d hd e he
  exact setLike_mul_comm hd he

end TaskP.PrimeMedialRacks
