import Research.TaskP.PrimeMedialRacks.Challenge

namespace TaskP.PrimeMedialRacks

open Challenge

noncomputable def leftPerm {α : Type*} {op : Operation α} (hr : IsRack op) (x : α) :
    Equiv.Perm α := Equiv.ofBijective (op x) (hr.1 x)

structure RegularDisplacements {α : Type*} (op : Operation α) (hr : IsRack op) where
  group : Subgroup (Equiv.Perm α)
  commutes : ∀ d ∈ group, ∀ e ∈ group, Commute d e
  acts : ∀ d ∈ group, ∀ x y, d (op x y) = op (d x) (d y)
  normalizes : ∀ x d, d ∈ group → leftPerm hr x * d * (leftPerm hr x)⁻¹ ∈ group
  regular : ∀ x : α, Function.Bijective (fun d : group => d.1 x)

end TaskP.PrimeMedialRacks
