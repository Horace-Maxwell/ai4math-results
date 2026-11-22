import Research.TaskP.PrimeMedialRacks.DisplacementGroup
import Research.TaskP.PrimeMedialRacks.PrimeAction

namespace TaskP.PrimeMedialRacks

open Challenge

variable {α : Type*} {op : Operation α} (hr : IsRack op)

/-- The common centralizer, taken inside the displacement group. -/
noncomputable def fixedDisplacements (base : α) : Subgroup (displacement hr base) where
  carrier := {d | Commute d.val (leftPerm hr base)}
  one_mem' := Commute.one_left _
  mul_mem' := fun hd he => hd.mul_left he
  inv_mem' := fun hd => hd.inv_left

theorem stabilizer_le_fixed (hm : Medial op) (base x : α) :
    MulAction.stabilizer (displacement hr base) x ≤ fixedDisplacements hr base := by
  intro d hd
  change d.val x = x at hd
  change Commute d.val (leftPerm hr base)
  have hconj := conjugate_leftPerm hr (displacement_acts hr base d.property) x
  rw [hd] at hconj
  have hcomm : Commute d.val (leftPerm hr x) := mul_inv_eq_iff_eq_mul.mp hconj
  let g := leftPerm hr x * (leftPerm hr base)⁻¹
  have hg := displacement_commutes hr hm base _ d.property g (displacement_generator hr base x)
  have h := hg.inv_right.mul_right hcomm
  simpa [g, mul_assoc] using h

theorem fixed_ne_top (hm : Medial op) (hn : ¬ TwoReductive op) (base : α) :
    fixedDisplacements hr base ≠ ⊤ := by
  intro ht
  apply hn
  let T := leftPerm hr base
  let diff := fun x => leftPerm hr x * T⁻¹
  have hmem (x : α) : diff x ∈ displacement hr base := displacement_generator hr base x
  have fixed (x : α) : Commute (diff x) T := by
    have h : (⟨diff x, hmem x⟩ : displacement hr base) ∈ fixedDisplacements hr base := by
      rw [ht]
      trivial
    exact h
  have commute (x y : α) : Commute (leftPerm hr x) (leftPerm hr y) := by
    have hxy := displacement_commutes hr hm base _ (hmem x) _ (hmem y)
    have h := (hxy.mul_right (fixed x)).mul_left ((fixed y).symm.mul_right (Commute.refl T))
    simpa [diff, mul_assoc] using h
  have row (x u : α) : leftPerm hr (op x u) = leftPerm hr u := by
    have h := conjugate_leftPerm hr (leftPerm_mem_aut hr x) u
    change leftPerm hr x * leftPerm hr u * (leftPerm hr x)⁻¹ = leftPerm hr (op x u) at h
    rw [(commute x u).eq] at h
    simpa [mul_assoc] using h.symm
  intro x y u v
  exact congrArg (fun t : Equiv.Perm α => t v) ((row x u).trans (row y u).symm)

theorem nonempty_regularDisplacements {p : ℕ} (hp : p.Prime) (op : Operation (Fin p))
    (hr : IsRack op) (hm : Medial op) (hn : ¬ TwoReductive op) :
    Nonempty (RegularDisplacements op hr) := by
  let base : Fin p := ⟨0, hp.pos⟩
  let D := displacement hr base
  have comm := displacement_commutes hr hm base
  have tr := prime_action_transitive hp D (fixedDisplacements hr base)
    (fixed_ne_top hr hm hn base) (stabilizer_le_fixed hr hm base)
  exact ⟨{
    group := D
    commutes := comm
    acts := fun _ hd => displacement_acts hr base hd
    normalizes := fun x _ hd => displacement_normalizes hr base x hd
    regular := abelian_transitive_regular D comm tr }⟩

end TaskP.PrimeMedialRacks
