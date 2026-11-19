import Research.TaskJ.Rank.Extension.OrbitStructure

namespace TaskJ.Rank.Extension.Family

noncomputable section
open scoped Classical

variable {n : ℕ} (D : Family n)

/-- A translation amount independently chosen on each orbit. -/
def fiberPerm (t : ∀ i, D.Fiber i) : Equiv.Perm D.Point :=
  Equiv.sigmaCongrRight (fun i => Equiv.mulLeft (t i))

@[simp] theorem fiberPerm_mk (t : ∀ i, D.Fiber i) (i : Fin n) (x : D.Fiber i) :
    D.fiberPerm t ⟨i,x⟩ = ⟨i,t i*x⟩ := rfl

def fiberTranslations : (∀ i, D.Fiber i) →* D.automorphisms where
  toFun t := ⟨D.fiberPerm t,by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨g,rfl⟩
    apply Equiv.ext
    rintro ⟨i,x⟩
    change (Sigma.mk i (D.projection i g * (t i * x)) : D.Point) = ⟨i,t i * (D.projection i g * x)⟩
    rw [mul_left_comm]⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change (Sigma.mk i (1*x) : D.Point) = ⟨i,x⟩
    rw [one_mul]
  map_mul' t u := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change (Sigma.mk i ((t i*u i)*x) : D.Point) = ⟨i,t i*(u i*x)⟩
    rw [mul_assoc]

theorem equivariant_apply (c : D.automorphisms) (g : D.Actor) (x : D.Point) :
    c.val (D.action g x) = D.action g (c.val x) :=
  (DFunLike.congr_fun (Subgroup.mem_centralizer_iff.mp c.property _ ⟨g,rfl⟩) x).symm

theorem automorphism_preserves_stabilizer (c : D.automorphisms) (x : D.Point) :
    D.stabilizer (c.val x) = D.stabilizer x := by
  ext g
  change D.action g (c.val x) = c.val x ↔ D.action g x = x
  rw [← D.equivariant_apply]
  exact c.val.injective.eq_iff

theorem automorphism_preserves_index (hw : Function.Injective D.width)
    (c : D.automorphisms) (x : D.Point) : (c.val x).1 = x.1 := by
  apply D.box_injective hw
  rw [← D.stabilizer_box, ← D.stabilizer_box, D.automorphism_preserves_stabilizer]

private theorem value_at_identity (hw : Function.Injective D.width) (c : D.automorphisms)
    (i : Fin n) : ∃ t : D.Fiber i, c.val ⟨i,1⟩ = ⟨i,t⟩ := by
  have hi := D.automorphism_preserves_index hw c ⟨i,1⟩
  generalize c.val (⟨i,1⟩ : D.Point) = y at hi ⊢
  obtain ⟨j,z⟩ := y
  change j=i at hi
  subst j
  exact ⟨z,rfl⟩

theorem fiberTranslations_bijective (hw : Function.Injective D.width) :
    Function.Bijective D.fiberTranslations := by
  constructor
  · intro u v h
    funext i
    have he := congrArg (fun t : D.automorphisms => t.val (⟨i,1⟩ : D.Point)) h
    change (Sigma.mk i (u i*1) : D.Point) = ⟨i,v i*1⟩ at he
    simpa using he
  · intro c
    choose t ht using D.value_at_identity hw c
    refine ⟨t,Subtype.ext (Equiv.ext ?_)⟩
    rintro ⟨i,x⟩
    obtain ⟨g,hg⟩ := D.projection_surjective i x
    have he := D.equivariant_apply c g (⟨i,1⟩ : D.Point)
    rw [ht,action_point,action_point,hg,mul_one] at he
    change (Sigma.mk i (t i * x) : D.Point) = _
    rw [he,mul_comm]

/-- Equivariant automorphisms of this family are precisely the independent translations. -/
def automorphismsEquivProduct (hw : Function.Injective D.width) :
    D.automorphisms ≃* (∀ i, D.Fiber i) :=
  (MulEquiv.ofBijective D.fiberTranslations (D.fiberTranslations_bijective hw)).symm

end
end TaskJ.Rank.Extension.Family
