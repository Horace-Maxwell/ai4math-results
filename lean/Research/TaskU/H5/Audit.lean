import Research.TaskU.H5.Challenge

namespace TaskU.H5.Audit

theorem order_check : Fintype.card H = 125 := by decide +kernel

theorem relation_check : y*x = x*y*⟨0,0,1⟩ := by decide +kernel

theorem noncommuting : y*x ≠ x*y := by decide +kernel

theorem witness_support :
    ∀ g : H, witness g = if g ∈ ({1,x,y,y^2,x*y^2} : Finset H) then 1 else 0 := by
  decide +kernel

#print axioms order_check
#print axioms relation_check
#print axioms noncommuting
#print axioms witness_support
end TaskU.H5.Audit
