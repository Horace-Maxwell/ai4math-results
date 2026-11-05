import Research.Backfill.Paper7.EightHalfOppositeIdentity

/-! NEW SOURCE ONLY repair after development 429. The four original
declarations keep their exact hypotheses. Each finite certificate quantifies
over every coordinate of its stated Fin 3 or Fin 2 domain; no list of
accepted tuples or external calculation is supplied. Kernel decisions below
have not been executed. Default budgets and all linters are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightHalf

theorem half_opposite_case_a_finite :
    let v : Fin 3 → ℤ := ![-2,1,2]
    ∀ a b c d e f : Fin 3,
      [v a,v b,v c,v d,v e,v f].sum = ([-2,1,1,2,2,2] : List ℤ).sum →
      (-2 : ℤ) ∈ [v a,v b,v c,v d,v e,v f] →
      (v a*v b*v c-v a-v c)+(v d*v e*v f-v d-v f) = 0 →
      (-6)*(v a*v b*v c-v a-v c) =
        2*(v a*v b+v b*v c-v d*v e-v e*v f) → False := by
  decide +kernel
#print axioms Paper7EightHalf.half_opposite_case_a_finite

theorem half_opposite_case_b_finite :
    let v : Fin 2 → ℤ := ![-1,2]
    ∀ a b c d e f : Fin 2,
      [v a,v b,v c,v d,v e,v f].sum = ([-1,-1,2,2,2,2] : List ℤ).sum →
      (v a*v b*v c-v a-v c)+(v d*v e*v f-v d-v f) = 0 → False := by
  decide +kernel
#print axioms Paper7EightHalf.half_opposite_case_b_finite

theorem half_opposite_case_c_finite :
    let v : Fin 3 → ℤ := ![-4,0,2]
    ∀ a b c d e f : Fin 3,
      [v a,v b,v c,v d,v e,v f].sum = ([-4,0,2,2,2,2] : List ℤ).sum →
      (-4 : ℤ) ∈ [v a,v b,v c,v d,v e,v f] →
      (v a*v b*v c-v a-v c)+(v d*v e*v f-v d-v f) = 0 → False := by
  decide +kernel
#print axioms Paper7EightHalf.half_opposite_case_c_finite

theorem half_opposite_case_d_finite :
    let v : Fin 2 → ℤ := ![-4,2]
    ∀ a b c d e f : Fin 2,
      [v a,v b,v c,v d,v e,v f].sum = ([-4,2,2,2,2,2] : List ℤ).sum →
      (v a*v b*v c-v a-v c)+(v d*v e*v f-v d-v f) = 0 → False := by
  decide +kernel
#print axioms Paper7EightHalf.half_opposite_case_d_finite

theorem half_opposite_case_a (h k a b c d e f : ℤ)
    (hhk : h+k = -6) (hp : [a,b,c,d,e,f].Perm [-2,1,1,2,2,2]) :
    halfOppositeProduct h k a b c d e f ≠ 1 := by
  intro hid
  obtain ⟨hS,hH,hK⟩ := half_opposite_identity_data h k a b c d e f hid
  have hHK : (-6)*(a*b*c-a-c) = 2*(a*b+b*c-d*e-e*f) := by
    calc
      _ = (h+k)*(a*b*c-a-c) := by rw [hhk]
      _ = h*(a*b*c-a-c)+k*(a*b*c-a-c) := by ring
      _ = 2*(a*b+b*c-d*e-e*f) := by rw [hH,hK]; ring
  have hsum := hp.sum_eq
  have hn : (-2 : ℤ) ∈ [a,b,c,d,e,f] := hp.mem_iff.mpr (by simp)
  have hv (x : ℤ) (hx : x ∈ [a,b,c,d,e,f]) :
      ∃ i : Fin 3, x = (![-2,1,2] : Fin 3 → ℤ) i := by
    have hh : x = -2 ∨ x = 1 ∨ x = 2 := by
      simpa using hp.mem_iff.mp hx
    rcases hh with hh | hh | hh
    · exact ⟨0,hh⟩
    · exact ⟨1,hh⟩
    · exact ⟨2,hh⟩
  obtain ⟨ia,rfl⟩ := hv a (by simp)
  obtain ⟨ib,rfl⟩ := hv b (by simp)
  obtain ⟨ic,rfl⟩ := hv c (by simp)
  obtain ⟨id,rfl⟩ := hv d (by simp)
  obtain ⟨ie,rfl⟩ := hv e (by simp)
  obtain ⟨i_f,rfl⟩ := hv f (by simp)
  exact half_opposite_case_a_finite ia ib ic id ie i_f hsum hn hS hHK
#print axioms Paper7EightHalf.half_opposite_case_a

theorem half_opposite_case_b (h k a b c d e f : ℤ)
    (hp : [a,b,c,d,e,f].Perm [-1,-1,2,2,2,2]) :
    halfOppositeProduct h k a b c d e f ≠ 1 := by
  intro hid
  have hS := (half_opposite_identity_data h k a b c d e f hid).1
  have hsum := hp.sum_eq
  have hv (x : ℤ) (hx : x ∈ [a,b,c,d,e,f]) :
      ∃ i : Fin 2, x = (![-1,2] : Fin 2 → ℤ) i := by
    have hh : x = -1 ∨ x = 2 := by
      simpa using hp.mem_iff.mp hx
    rcases hh with hh | hh
    · exact ⟨0,hh⟩
    · exact ⟨1,hh⟩
  obtain ⟨ia,rfl⟩ := hv a (by simp)
  obtain ⟨ib,rfl⟩ := hv b (by simp)
  obtain ⟨ic,rfl⟩ := hv c (by simp)
  obtain ⟨id,rfl⟩ := hv d (by simp)
  obtain ⟨ie,rfl⟩ := hv e (by simp)
  obtain ⟨i_f,rfl⟩ := hv f (by simp)
  exact half_opposite_case_b_finite ia ib ic id ie i_f hsum hS
#print axioms Paper7EightHalf.half_opposite_case_b

theorem half_opposite_case_c (h k a b c d e f : ℤ)
    (hp : [a,b,c,d,e,f].Perm [-4,0,2,2,2,2]) :
    halfOppositeProduct h k a b c d e f ≠ 1 := by
  intro hid
  have hS := (half_opposite_identity_data h k a b c d e f hid).1
  have hsum := hp.sum_eq
  have hn : (-4 : ℤ) ∈ [a,b,c,d,e,f] := hp.mem_iff.mpr (by simp)
  have hv (x : ℤ) (hx : x ∈ [a,b,c,d,e,f]) :
      ∃ i : Fin 3, x = (![-4,0,2] : Fin 3 → ℤ) i := by
    have hh : x = -4 ∨ x = 0 ∨ x = 2 := by
      simpa using hp.mem_iff.mp hx
    rcases hh with hh | hh | hh
    · exact ⟨0,hh⟩
    · exact ⟨1,hh⟩
    · exact ⟨2,hh⟩
  obtain ⟨ia,rfl⟩ := hv a (by simp)
  obtain ⟨ib,rfl⟩ := hv b (by simp)
  obtain ⟨ic,rfl⟩ := hv c (by simp)
  obtain ⟨id,rfl⟩ := hv d (by simp)
  obtain ⟨ie,rfl⟩ := hv e (by simp)
  obtain ⟨i_f,rfl⟩ := hv f (by simp)
  exact half_opposite_case_c_finite ia ib ic id ie i_f hsum hn hS
#print axioms Paper7EightHalf.half_opposite_case_c

theorem half_opposite_case_d (h k a b c d e f : ℤ)
    (hp : [a,b,c,d,e,f].Perm [-4,2,2,2,2,2]) :
    halfOppositeProduct h k a b c d e f ≠ 1 := by
  intro hid
  have hS := (half_opposite_identity_data h k a b c d e f hid).1
  have hsum := hp.sum_eq
  have hv (x : ℤ) (hx : x ∈ [a,b,c,d,e,f]) :
      ∃ i : Fin 2, x = (![-4,2] : Fin 2 → ℤ) i := by
    have hh : x = -4 ∨ x = 2 := by
      simpa using hp.mem_iff.mp hx
    rcases hh with hh | hh
    · exact ⟨0,hh⟩
    · exact ⟨1,hh⟩
  obtain ⟨ia,rfl⟩ := hv a (by simp)
  obtain ⟨ib,rfl⟩ := hv b (by simp)
  obtain ⟨ic,rfl⟩ := hv c (by simp)
  obtain ⟨id,rfl⟩ := hv d (by simp)
  obtain ⟨ie,rfl⟩ := hv e (by simp)
  obtain ⟨i_f,rfl⟩ := hv f (by simp)
  exact half_opposite_case_d_finite ia ib ic id ie i_f hsum hS
#print axioms Paper7EightHalf.half_opposite_case_d

end Paper7EightHalf
