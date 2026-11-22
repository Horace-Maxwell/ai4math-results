import Research.TaskU.H5.CycPhase

namespace TaskU.H5.Cyc5

/-- Coefficients of π and π² upon writing z=1−π, read modulo five. -/
def first (v : V) : ZMod 5 := (-(v.b + 2*v.c + 3*v.d) : ℤ)
def second (v : V) : ZMod 5 := (v.c + 3*v.d : ℤ)

lemma phase_moment (v : V) (k : ZMod 5) (h0 : 5 ∣ sumCoeff v)
    (hk : conj v = neg (mul (rootAt k) v)) : first v * k = 2 * second v - first v := by
  have hA := congrArg V.a hk
  have hB := congrArg V.b hk
  have hC := congrArg V.c hk
  have hD := congrArg V.d hk
  have hint : (5:ℤ) ∣ -(v.b+2*v.c+3*v.d)*(k.val:ℤ) - 2*(v.c+3*v.d) -(v.b+2*v.c+3*v.d) := by
    obtain ⟨t,ht⟩ := h0
    simp only [sumCoeff] at ht
    fin_cases k <;>
      norm_num [rootAt,root,scalar,conj,neg,mul,ZMod.val] at hA hB hC hD ⊢ <;> omega
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hint
  push_cast at h
  simp only [ZMod.natCast_zmod_val] at h
  simp only [first,second,Int.cast_neg,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  linear_combination h

end TaskU.H5.Cyc5
