import Research.AxialMSZ.Proof.ExP
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

section General
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem gen_isSubalgebra (μ : V →ₗ[ℚ] V →ₗ[ℚ] V) (X : Set V) :
    IsSubalgebra μ (gen μ X) := by
  intro u hu v hv
  exact Submodule.mem_sInf.mpr fun S hS =>
    hS.2 u (Submodule.mem_sInf.mp hu S hS) v (Submodule.mem_sInf.mp hv S hS)

theorem mul_span_axis_eigen {μ : V →ₗ[ℚ] V →ₗ[ℚ] V} {a u v : V} {l : ℚ}
    (hu : u ∈ Submodule.span ℚ {a}) (hv : v ∈ eigsp μ a l) : μ u v ∈ eigsp μ a l := by
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hu
  have he := (Module.End.mem_eigenspace_iff.mp hv)
  simpa [he] using (eigsp μ a l).smul_mem s ((eigsp μ a l).smul_mem l hv)

theorem mul_span_axis_zero {μ : V →ₗ[ℚ] V →ₗ[ℚ] V} {a u v : V}
    (hu : u ∈ Submodule.span ℚ {a}) (hv : v ∈ eigsp μ a 0) : μ u v = 0 := by
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hu
  have he := Module.End.mem_eigenspace_iff.mp hv
  simpa using congrArg (fun z => s • z) he

/-- The only nonautomatic fusion check for the enlarged Jordan law is η times η. -/
theorem primitive_jplus {μ : V →ₗ[ℚ] V →ₗ[ℚ] V} {a : V} {η : ℚ}
    (hη0 : η ≠ 0) (hη1 : η ≠ 1) (hc : IsCommutative μ) (ha : a ≠ 0)
    (hid : μ a a = a) (ht : eigspSet μ a (JPlus η).carrier = ⊤)
    (h1 : eigsp μ a 1 = Submodule.span ℚ {a})
    (hsq : ∀ u ∈ eigsp μ a η, ∀ v ∈ eigsp μ a η,
      μ u v ∈ eigspSet μ a {1,0}) : IsPrimitiveAxis (JPlus η) μ a := by
  change eigspSet μ a {1,0,η} = ⊤ at ht
  refine ⟨⟨ha, hid, ht, ?_⟩, h1⟩
  intro l hl m hm u hu v hv
  simp only [JPlus, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
  rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · simpa [JPlus] using mul_span_axis_eigen (h1 ▸ hu) hv
  · simpa [JPlus] using mul_span_axis_zero (h1 ▸ hu) hv
  · simpa [JPlus,hη0] using mul_span_axis_eigen (h1 ▸ hu) hv
  · simpa [JPlus,hc u v] using mul_span_axis_zero (h1 ▸ hv) hu
  · simp [JPlus,ht]
  · simp [JPlus,hη1,ht]
  · simpa [JPlus,hη0,hη1,hc u v] using mul_span_axis_eigen (h1 ▸ hv) hu
  · simp [JPlus,hη1,ht]
  · simpa [JPlus,hη0,hη1] using hsq u hu v hv
end General

namespace SimpleExample
abbrev A := Fin 4 → ℚ
abbrev a : A := e 0
abbrev b : A := e 1
abbrev x : A := e 2
abbrev c : A := e 3
abbrev za : A := ![-1/2,1,1,0]
abbrev ha : A := ![0,-1,1,0]
abbrev zb : A := ![1,-1/2,1,0]
abbrev hb : A := ![-1,0,1,0]
abbrev w : A := ![-2,-2,2,1]
abbrev F := JPlus (1/2 : ℚ)

theorem mul_apply (u v : A) (k : Fin 4) :
    ExS.μ u v k = ∑ i, ∑ j, u i * v j * ExS.T i j k := by
  simp [ExS.μ, structProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem commutative : IsCommutative ExS.μ := by
  intro u v
  funext k
  rw [mul_apply,mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExS.T] <;> ring

theorem a_mul (u : A) : ExS.μ a u =
    ![u 0 + u 1/4 + u 2/4, u 1/4-u 2/4, -u 1/4+u 2/4, 0] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExS.T,a,e,Pi.single_apply] <;> ring

theorem b_mul (u : A) : ExS.μ b u =
    ![u 0/4-u 2/4, u 0/4+u 1+u 2/4, -u 0/4+u 2/4, 0] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExS.T,b,e,Pi.single_apply] <;> ring

theorem c_mul (u : A) : ExS.μ c u =
    ![-u 2/2, -u 2/2, u 2/2, -u 2/4+u 3] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExS.T,c,e,Pi.single_apply] <;> ring

theorem eig_a_one : eigsp ExS.μ a 1 = Submodule.span ℚ {a} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,a_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 0, ?_⟩
    funext k
    fin_cases k <;> simp [a,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [a,e]

theorem eig_b_one : eigsp ExS.μ b 1 = Submodule.span ℚ {b} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,b_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 1, ?_⟩
    funext k
    fin_cases k <;> simp [b,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [b,e]

theorem eig_c_one : eigsp ExS.μ c 1 = Submodule.span ℚ {c} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,c_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 3, ?_⟩
    funext k
    fin_cases k <;> simp [c,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [c,e]

theorem eig_a_half : eigsp ExS.μ a (1/2) = Submodule.span ℚ {ha} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,a_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 2, ?_⟩
    funext k
    fin_cases k <;> simp [ha] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [ha] <;> ring

theorem eig_b_half : eigsp ExS.μ b (1/2) = Submodule.span ℚ {hb} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,b_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 2, ?_⟩
    funext k
    fin_cases k <;> simp [hb] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [hb] <;> ring

theorem eig_c_half : eigsp ExS.μ c (1/2) = Submodule.span ℚ {w} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,c_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    refine ⟨u 2/2, ?_⟩
    funext k
    fin_cases k <;> simp [w] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [w] <;> ring

theorem za_zero : za ∈ eigsp ExS.μ a 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul]
  funext k
  fin_cases k <;> norm_num [za]

theorem zb_zero : zb ∈ eigsp ExS.μ b 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul]
  funext k
  fin_cases k <;> norm_num [zb]

theorem c_zero_a : c ∈ eigsp ExS.μ a 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul]
  funext k
  fin_cases k <;> norm_num [c,e,Pi.single_apply]

theorem c_zero_b : c ∈ eigsp ExS.μ b 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul]
  funext k
  fin_cases k <;> norm_num [c,e,Pi.single_apply]

theorem a_zero_c : a ∈ eigsp ExS.μ c 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul]
  funext k
  fin_cases k <;> norm_num [a,e,Pi.single_apply]

theorem b_zero_c : b ∈ eigsp ExS.μ c 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul]
  funext k
  fin_cases k <;> norm_num [b,e,Pi.single_apply]

theorem a_top : eigspSet ExS.μ a F.carrier = ⊤ := by
  let S := eigspSet ExS.μ a F.carrier
  have h1 : a ∈ S := mem_eigspSet (l := 1) (by simp [F,JPlus])
    (by rw [eig_a_one]; exact Submodule.subset_span rfl)
  have h0 : za ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) za_zero
  have hh : ha ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JPlus])
    (by rw [eig_a_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) c_zero_a
  rw [eq_top_iff]
  intro u _
  have hd : u = (u 0+(u 1+u 2)/4) • a + ((u 1+u 2)/2) • za +
      ((u 2-u 1)/2) • ha + u 3 • c := by
    funext k
    fin_cases k <;> simp [a,c,e,za,ha,Matrix.vecHead,Matrix.vecTail] <;> ring
  rw [hd]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h0))
    (S.smul_mem _ hh)) (S.smul_mem _ hc)

theorem b_top : eigspSet ExS.μ b F.carrier = ⊤ := by
  let S := eigspSet ExS.μ b F.carrier
  have h1 : b ∈ S := mem_eigspSet (l := 1) (by simp [F,JPlus])
    (by rw [eig_b_one]; exact Submodule.subset_span rfl)
  have h0 : zb ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) zb_zero
  have hh : hb ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JPlus])
    (by rw [eig_b_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) c_zero_b
  rw [eq_top_iff]
  intro u _
  have hd : u = (u 1+(u 0+u 2)/4) • b + ((u 0+u 2)/2) • zb +
      ((u 2-u 0)/2) • hb + u 3 • c := by
    funext k
    fin_cases k <;> simp [b,c,e,zb,hb,Matrix.vecHead,Matrix.vecTail] <;> ring
  rw [hd]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h0))
    (S.smul_mem _ hh)) (S.smul_mem _ hc)

theorem c_top : eigspSet ExS.μ c F.carrier = ⊤ := by
  let S := eigspSet ExS.μ c F.carrier
  have h1 : c ∈ S := mem_eigspSet (l := 1) (by simp [F,JPlus])
    (by rw [eig_c_one]; exact Submodule.subset_span rfl)
  have h0a : a ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) a_zero_c
  have h0b : b ∈ S := mem_eigspSet (l := 0) (by simp [F,JPlus]) b_zero_c
  have hh : w ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JPlus])
    (by rw [eig_c_half]; exact Submodule.subset_span rfl)
  rw [eq_top_iff]
  intro u _
  have hd : u = (u 0+u 2) • a + (u 1+u 2) • b + (u 2/2) • w + (u 3-u 2/2) • c := by
    funext k
    fin_cases k <;> simp [a,b,c,e,w,Matrix.vecHead,Matrix.vecTail]
  rw [hd]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h0a) (S.smul_mem _ h0b))
    (S.smul_mem _ hh)) (S.smul_mem _ h1)

theorem a_half_sq : ExS.μ ha ha = (3/4 : ℚ) • a + (1/2 : ℚ) • za := by
  funext k
  rw [mul_apply]
  fin_cases k <;> norm_num [Fin.sum_univ_four,ExS.T,ha,za,a,e,Pi.single_apply]

theorem b_half_sq : ExS.μ hb hb = (3/4 : ℚ) • b + (1/2 : ℚ) • zb := by
  funext k
  rw [mul_apply]
  fin_cases k <;> norm_num [Fin.sum_univ_four,ExS.T,hb,zb,b,e,Pi.single_apply]

theorem c_half_sq : ExS.μ w w = (4 : ℚ) • a + (4 : ℚ) • b := by
  funext k
  rw [mul_apply]
  fin_cases k <;> norm_num [Fin.sum_univ_four,ExS.T,w,a,b,e,Pi.single_apply]

theorem primitive_a : IsPrimitiveAxis F ExS.μ a := by
  apply primitive_jplus (by norm_num) (by norm_num) commutative
  · intro h; have hh := congrFun h 0; norm_num [a,e,Pi.single_apply] at hh
  · rw [a_mul]; funext k; fin_cases k <;> norm_num [a,e,Pi.single_apply]
  · exact a_top
  · exact eig_a_one
  · intro u hu v hv
    rw [eig_a_half] at hu hv
    apply mul_mem_of_spans ?_ hu hv
    rw [a_half_sq]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (mem_eigspSet (l := 1) (by simp)
        (by rw [eig_a_one]; exact Submodule.subset_span rfl))
    · exact Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) za_zero)

theorem primitive_b : IsPrimitiveAxis F ExS.μ b := by
  apply primitive_jplus (by norm_num) (by norm_num) commutative
  · intro h; have hh := congrFun h 1; norm_num [b,e,Pi.single_apply] at hh
  · rw [b_mul]; funext k; fin_cases k <;> norm_num [b,e,Pi.single_apply]
  · exact b_top
  · exact eig_b_one
  · intro u hu v hv
    rw [eig_b_half] at hu hv
    apply mul_mem_of_spans ?_ hu hv
    rw [b_half_sq]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (mem_eigspSet (l := 1) (by simp)
        (by rw [eig_b_one]; exact Submodule.subset_span rfl))
    · exact Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) zb_zero)

theorem primitive_c : IsPrimitiveAxis F ExS.μ c := by
  apply primitive_jplus (by norm_num) (by norm_num) commutative
  · intro h; have hh := congrFun h 3; norm_num [c,e,Pi.single_apply] at hh
  · rw [c_mul]; funext k; fin_cases k <;> norm_num [c,e,Pi.single_apply]
  · exact c_top
  · exact eig_c_one
  · intro u hu v hv
    rw [eig_c_half] at hu hv
    apply mul_mem_of_spans ?_ hu hv
    rw [c_half_sq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) a_zero_c))
      (Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) b_zero_c))

theorem coordinates (u : A) : u = u 0 • a + u 1 • b + u 2 • x + u 3 • c := by
  funext k
  fin_cases k <;> simp [a,b,x,c,e]

theorem x_from_ab : x = a+b-(4 : ℚ) • ExS.μ a b := by
  rw [a_mul]
  funext k
  fin_cases k <;> norm_num [a,b,x,e,Pi.single_apply]

theorem generates : gen ExS.μ ExS.X = ⊤ := by
  have ma : a ∈ gen ExS.μ ExS.X := mem_gen_of_mem (by simp [ExS.X,a])
  have mb : b ∈ gen ExS.μ ExS.X := mem_gen_of_mem (by simp [ExS.X,b])
  have mc : c ∈ gen ExS.μ ExS.X := mem_gen_of_mem (by simp [ExS.X,c])
  have mx : x ∈ gen ExS.μ ExS.X := by
    rw [x_from_ab]
    exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb)
      (Submodule.smul_mem _ _ (gen_isSubalgebra _ _ _ ma _ mb))
  rw [eq_top_iff]
  intro u _
  rw [coordinates u]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ ma) (Submodule.smul_mem _ _ mb))
    (Submodule.smul_mem _ _ mx)) (Submodule.smul_mem _ _ mc)

theorem axial : IsPrimitiveAxialAlgebra F ExS.μ ExS.X := by
  refine ⟨commutative, ?_, generates⟩
  rintro z (rfl | rfl | rfl)
  · exact primitive_a
  · exact primitive_b
  · exact primitive_c

#print axioms axial
end SimpleExample
end CodexAxial
