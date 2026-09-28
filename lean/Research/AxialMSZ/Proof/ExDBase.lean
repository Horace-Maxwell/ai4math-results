import Research.AxialMSZ.Proof.ExSBase

/-! Coordinate and eigenspace proofs for the frozen ExD contract.
Frozen Challenge SHA256: 0d88e7321e0f0931f953ea250f2c5dc1d6d5773cd8f78e3080e0d6eeceb13ee1.
-/
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

section Mild
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem primitive_jmild {μ : V →ₗ[ℚ] V →ₗ[ℚ] V} {a : V} {η : ℚ}
    (hη0 : η ≠ 0) (hη1 : η ≠ 1) (hc : IsCommutative μ) (ha : a ≠ 0)
    (hid : μ a a = a) (ht : eigspSet μ a (JMild η).carrier = ⊤)
    (h1 : eigsp μ a 1 = Submodule.span ℚ {a})
    (h00 : ∀ u ∈ eigsp μ a 0, ∀ v ∈ eigsp μ a 0,
      μ u v ∈ eigspSet μ a {0,η})
    (h0h : ∀ u ∈ eigsp μ a 0, ∀ v ∈ eigsp μ a η,
      μ u v ∈ eigspSet μ a {0,η})
    (hhh : ∀ u ∈ eigsp μ a η, ∀ v ∈ eigsp μ a η,
      μ u v ∈ eigspSet μ a {1,0}) : IsPrimitiveAxis (JMild η) μ a := by
  refine ⟨⟨ha,hid,ht,?_⟩,h1⟩
  intro l hl m hm u hu v hv
  simp only [JMild,Set.mem_insert_iff,Set.mem_singleton_iff] at hl hm
  rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  · simpa [JMild] using mul_span_axis_eigen (h1 ▸ hu) hv
  · simpa [JMild] using mul_span_axis_zero (h1 ▸ hu) hv
  · simpa [JMild,hη0] using mul_span_axis_eigen (h1 ▸ hu) hv
  · simpa [JMild,hc u v] using mul_span_axis_zero (h1 ▸ hv) hu
  · simpa [JMild] using h00 u hu v hv
  · simpa [JMild,hη1] using h0h u hu v hv
  · simpa [JMild,hη0,hη1,hc u v] using mul_span_axis_eigen (h1 ▸ hv) hu
  · simpa [JMild,hη1,hc u v] using h0h v hv u hu
  · simpa [JMild,hη0,hη1] using hhh u hu v hv
end Mild

namespace DecomposableExample
abbrev A := Fin 5 → ℚ
abbrev a : A := e 0
abbrev b : A := e 1
abbrev x : A := e 2
abbrev c : A := e 3
abbrev d : A := e 4
abbrev za : A := ![-1/2,1,1,0,0]
abbrev ha : A := ![0,-1,1,0,0]
abbrev zb : A := ![1,-1/2,1,0,0]
abbrev hb : A := ![-1,0,1,0,0]
abbrev zc : A := ![0,0,1,0,-2]
abbrev F := JMild (1/2 : ℚ)

theorem mul_apply (u v : A) (k : Fin 5) :
    ExD.μ u v k = ∑ i, ∑ j, u i * v j * ExD.T i j k := by
  simp [ExD.μ,structProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem mul_formula (u v : A) : ExD.μ u v =
    ![u 0*v 0+(u 0*v 1+u 1*v 0+u 0*v 2+u 2*v 0-u 1*v 2-u 2*v 1)/4,
      u 1*v 1+(u 0*v 1+u 1*v 0-u 0*v 2-u 2*v 0+u 1*v 2+u 2*v 1)/4,
      u 2*v 2+(-u 0*v 1-u 1*v 0+u 0*v 2+u 2*v 0+u 1*v 2+u 2*v 1)/4,
      u 3*v 3, u 2*v 3+u 3*v 2+(u 3*v 4+u 4*v 3)/2] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_succ,ExD.T] <;> ring

theorem commutative : IsCommutative ExD.μ := by
  intro u v
  rw [mul_formula,mul_formula]
  funext k
  fin_cases k <;> simp <;> ring

theorem a_mul (u : A) : ExD.μ a u =
    ![u 0+u 1/4+u 2/4,u 1/4-u 2/4,-u 1/4+u 2/4,0,0] := by
  rw [mul_formula]
  funext k
  fin_cases k <;> simp [a,e] <;> ring

theorem b_mul (u : A) : ExD.μ b u =
    ![u 0/4-u 2/4,u 0/4+u 1+u 2/4,-u 0/4+u 2/4,0,0] := by
  rw [mul_formula]
  funext k
  fin_cases k <;> simp [b,e] <;> ring

theorem c_mul (u : A) : ExD.μ c u = ![0,0,0,u 3,u 2+u 4/2] := by
  rw [mul_formula]
  funext k
  fin_cases k <;> simp [c,e]

theorem coordinates (u : A) :
    u = u 0 • a + u 1 • b + u 2 • x + u 3 • c + u 4 • d := by
  funext k
  fin_cases k <;> simp [a,b,x,c,d,e]

theorem eig_a_one : eigsp ExD.μ a 1 = Submodule.span ℚ {a} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,a_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 0, ?_⟩
    funext k
    fin_cases k <;> simp [a,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [a,e]

theorem eig_b_one : eigsp ExD.μ b 1 = Submodule.span ℚ {b} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,b_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 1, ?_⟩
    funext k
    fin_cases k <;> simp [b,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [b,e]

theorem eig_c_one : eigsp ExD.μ c 1 = Submodule.span ℚ {c} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,c_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 3, ?_⟩
    funext k
    fin_cases k <;> simp [c,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [c,e]

theorem eig_a_half : eigsp ExD.μ a (1/2) = Submodule.span ℚ {ha} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,a_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 2, ?_⟩
    funext k
    fin_cases k <;> simp [ha] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [ha] <;> ring

theorem eig_b_half : eigsp ExD.μ b (1/2) = Submodule.span ℚ {hb} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,b_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 2, ?_⟩
    funext k
    fin_cases k <;> simp [hb] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [hb] <;> ring

theorem eig_c_half : eigsp ExD.μ c (1/2) = Submodule.span ℚ {d} := by
  ext u
  rw [eigsp,Module.End.mem_eigenspace_iff,Submodule.mem_span_singleton,c_mul]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3; have h4 := congrFun h 4
    simp at h0 h1 h2 h3 h4
    refine ⟨u 4, ?_⟩
    funext k
    fin_cases k <;> simp [d,e] <;> linarith
  · rintro ⟨t,rfl⟩
    funext k
    fin_cases k <;> simp [d,e]
    ring

theorem za_zero_a : za ∈ eigsp ExD.μ a 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul]
  funext k
  fin_cases k <;> norm_num [za,e,Pi.single_apply]

theorem c_zero_a : c ∈ eigsp ExD.μ a 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul]
  funext k
  fin_cases k <;> norm_num [c,e,Pi.single_apply]

theorem d_zero_a : d ∈ eigsp ExD.μ a 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul]
  funext k
  fin_cases k <;> norm_num [d,e,Pi.single_apply]

theorem zb_zero_b : zb ∈ eigsp ExD.μ b 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul]
  funext k
  fin_cases k <;> norm_num [zb,e,Pi.single_apply]

theorem c_zero_b : c ∈ eigsp ExD.μ b 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul]
  funext k
  fin_cases k <;> norm_num [c,e,Pi.single_apply]

theorem d_zero_b : d ∈ eigsp ExD.μ b 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul]
  funext k
  fin_cases k <;> norm_num [d,e,Pi.single_apply]

theorem a_zero_c : a ∈ eigsp ExD.μ c 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul]
  funext k
  fin_cases k <;> norm_num [a,e,Pi.single_apply]

theorem b_zero_c : b ∈ eigsp ExD.μ c 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul]
  funext k
  fin_cases k <;> norm_num [b,e,Pi.single_apply]

theorem zc_zero_c : zc ∈ eigsp ExD.μ c 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul]
  funext k
  fin_cases k <;> norm_num [zc,e,Pi.single_apply]

theorem a_zero_data {u : A} (hu : u ∈ eigsp ExD.μ a 0) :
    u 0 = -u 2/2 ∧ u 1 = u 2 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,a_mul] at hu
  have h0 := congrFun hu 0; have h1 := congrFun hu 1
  simp at h0 h1
  constructor <;> linarith

theorem a_top : eigspSet ExD.μ a F.carrier = ⊤ := by
  let S := eigspSet ExD.μ a F.carrier
  have h1 : a ∈ S := mem_eigspSet (l := 1) (by simp [F,JMild])
    (by rw [eig_a_one]; exact Submodule.subset_span rfl)
  have h0 : za ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) za_zero_a
  have hh : ha ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JMild])
    (by rw [eig_a_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) c_zero_a
  have hd : d ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) d_zero_a
  rw [eq_top_iff]
  intro u _
  have he : u = (u 0+(u 1+u 2)/4) • a + ((u 1+u 2)/2) • za +
      ((u 2-u 1)/2) • ha + u 3 • c + u 4 • d := by
    funext k
    fin_cases k <;> simp [a,c,d,e,za,ha,Matrix.vecHead,Matrix.vecTail] <;> ring
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1)
    (S.smul_mem _ h0)) (S.smul_mem _ hh)) (S.smul_mem _ hc)) (S.smul_mem _ hd)

theorem a_no_one_mem {u : A} (hu : u 0+(u 1+u 2)/4 = 0) :
    u ∈ eigspSet ExD.μ a {0,1/2} := by
  let S := eigspSet ExD.μ a {0,1/2}
  have h0 : za ∈ S := mem_eigspSet (l := 0) (by simp) za_zero_a
  have hh : ha ∈ S := mem_eigspSet (l := 1/2) (by simp)
    (by rw [eig_a_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp) c_zero_a
  have hd : d ∈ S := mem_eigspSet (l := 0) (by simp) d_zero_a
  have he : u = ((u 1+u 2)/2) • za + ((u 2-u 1)/2) • ha + u 3 • c + u 4 • d := by
    funext k
    fin_cases k <;> simp [za,ha,c,d,e,Matrix.vecHead,Matrix.vecTail] <;> linarith
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h0)
    (S.smul_mem _ hh)) (S.smul_mem _ hc)) (S.smul_mem _ hd)

theorem a_fusion00 (u : A) (hu : u ∈ eigsp ExD.μ a 0)
    (v : A) (hv : v ∈ eigsp ExD.μ a 0) : ExD.μ u v ∈ eigspSet ExD.μ a {0,1/2} := by
  obtain ⟨hu0,hu1⟩ := a_zero_data hu
  obtain ⟨hv0,hv1⟩ := a_zero_data hv
  apply a_no_one_mem
  rw [mul_formula]
  simp [hu0,hu1,hv0,hv1]
  ring

theorem a_fusion0h (u : A) (hu : u ∈ eigsp ExD.μ a 0)
    (v : A) (hv : v ∈ eigsp ExD.μ a (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ a {0,1/2} := by
  obtain ⟨hu0,hu1⟩ := a_zero_data hu
  rw [eig_a_half] at hv
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv
  apply a_no_one_mem
  rw [mul_formula]
  simp [hu0,hu1,ha]
  ring

theorem a_half_sq : ExD.μ ha ha = (3/4 : ℚ) • a + (1/2 : ℚ) • za := by
  rw [mul_formula]
  funext k
  fin_cases k <;> norm_num [ha,za,a,e,Pi.single_apply]

theorem a_fusionhh (u : A) (hu : u ∈ eigsp ExD.μ a (1/2))
    (v : A) (hv : v ∈ eigsp ExD.μ a (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ a {1,0} := by
  rw [eig_a_half] at hu hv
  apply mul_mem_of_spans ?_ hu hv
  rw [a_half_sq]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (mem_eigspSet (l := 1) (by simp)
      (by rw [eig_a_one]; exact Submodule.subset_span rfl)))
    (Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) za_zero_a))

theorem b_zero_data {u : A} (hu : u ∈ eigsp ExD.μ b 0) :
    u 1 = -u 2/2 ∧ u 0 = u 2 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,b_mul] at hu
  have h0 := congrFun hu 1; have h1 := congrFun hu 0
  simp at h0 h1
  constructor <;> linarith

theorem b_top : eigspSet ExD.μ b F.carrier = ⊤ := by
  let S := eigspSet ExD.μ b F.carrier
  have h1 : b ∈ S := mem_eigspSet (l := 1) (by simp [F,JMild])
    (by rw [eig_b_one]; exact Submodule.subset_span rfl)
  have h0 : zb ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) zb_zero_b
  have hh : hb ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JMild])
    (by rw [eig_b_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) c_zero_b
  have hd : d ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) d_zero_b
  rw [eq_top_iff]
  intro u _
  have he : u = (u 1+(u 0+u 2)/4) • b + ((u 0+u 2)/2) • zb +
      ((u 2-u 0)/2) • hb + u 3 • c + u 4 • d := by
    funext k
    fin_cases k <;> simp [b,c,d,e,zb,hb,Matrix.vecHead,Matrix.vecTail] <;> ring
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1)
    (S.smul_mem _ h0)) (S.smul_mem _ hh)) (S.smul_mem _ hc)) (S.smul_mem _ hd)

theorem b_no_one_mem {u : A} (hu : u 1+(u 0+u 2)/4 = 0) :
    u ∈ eigspSet ExD.μ b {0,1/2} := by
  let S := eigspSet ExD.μ b {0,1/2}
  have h0 : zb ∈ S := mem_eigspSet (l := 0) (by simp) zb_zero_b
  have hh : hb ∈ S := mem_eigspSet (l := 1/2) (by simp)
    (by rw [eig_b_half]; exact Submodule.subset_span rfl)
  have hc : c ∈ S := mem_eigspSet (l := 0) (by simp) c_zero_b
  have hd : d ∈ S := mem_eigspSet (l := 0) (by simp) d_zero_b
  have he : u = ((u 0+u 2)/2) • zb + ((u 2-u 0)/2) • hb + u 3 • c + u 4 • d := by
    funext k
    fin_cases k <;> simp [zb,hb,c,d,e,Matrix.vecHead,Matrix.vecTail] <;> linarith
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h0)
    (S.smul_mem _ hh)) (S.smul_mem _ hc)) (S.smul_mem _ hd)

theorem b_fusion00 (u : A) (hu : u ∈ eigsp ExD.μ b 0)
    (v : A) (hv : v ∈ eigsp ExD.μ b 0) : ExD.μ u v ∈ eigspSet ExD.μ b {0,1/2} := by
  obtain ⟨hu0,hu1⟩ := b_zero_data hu
  obtain ⟨hv0,hv1⟩ := b_zero_data hv
  apply b_no_one_mem
  rw [mul_formula]
  simp [hu0,hu1,hv0,hv1]
  ring

theorem b_fusion0h (u : A) (hu : u ∈ eigsp ExD.μ b 0)
    (v : A) (hv : v ∈ eigsp ExD.μ b (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ b {0,1/2} := by
  obtain ⟨hu0,hu1⟩ := b_zero_data hu
  rw [eig_b_half] at hv
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv
  apply b_no_one_mem
  rw [mul_formula]
  simp [hu0,hu1,hb]
  ring

theorem b_half_sq : ExD.μ hb hb = (3/4 : ℚ) • b + (1/2 : ℚ) • zb := by
  rw [mul_formula]
  funext k
  fin_cases k <;> norm_num [hb,zb,b,e,Pi.single_apply]

theorem b_fusionhh (u : A) (hu : u ∈ eigsp ExD.μ b (1/2))
    (v : A) (hv : v ∈ eigsp ExD.μ b (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ b {1,0} := by
  rw [eig_b_half] at hu hv
  apply mul_mem_of_spans ?_ hu hv
  rw [b_half_sq]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (mem_eigspSet (l := 1) (by simp)
      (by rw [eig_b_one]; exact Submodule.subset_span rfl)))
    (Submodule.smul_mem _ _ (mem_eigspSet (l := 0) (by simp) zb_zero_b))

theorem c_zero_data {u : A} (hu : u ∈ eigsp ExD.μ c 0) : u 3 = 0 := by
  rw [eigsp,Module.End.mem_eigenspace_iff,c_mul] at hu
  simpa using congrFun hu 3

theorem c_top : eigspSet ExD.μ c F.carrier = ⊤ := by
  let S := eigspSet ExD.μ c F.carrier
  have ha : a ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) a_zero_c
  have hb : b ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) b_zero_c
  have hz : zc ∈ S := mem_eigspSet (l := 0) (by simp [F,JMild]) zc_zero_c
  have hc : c ∈ S := mem_eigspSet (l := 1) (by simp [F,JMild])
    (by rw [eig_c_one]; exact Submodule.subset_span rfl)
  have hd : d ∈ S := mem_eigspSet (l := 1/2) (by simp [F,JMild])
    (by rw [eig_c_half]; exact Submodule.subset_span rfl)
  rw [eq_top_iff]
  intro u _
  have he : u = u 0 • a + u 1 • b + u 2 • zc + u 3 • c + (u 4+2*u 2) • d := by
    funext k
    fin_cases k <;> simp [a,b,zc,c,d,e,Matrix.vecHead,Matrix.vecTail]
    ring
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ ha)
    (S.smul_mem _ hb)) (S.smul_mem _ hz)) (S.smul_mem _ hc)) (S.smul_mem _ hd)

theorem c_no_one_mem {u : A} (hu : u 3 = 0) : u ∈ eigspSet ExD.μ c {0,1/2} := by
  let S := eigspSet ExD.μ c {0,1/2}
  have ha : a ∈ S := mem_eigspSet (l := 0) (by simp) a_zero_c
  have hb : b ∈ S := mem_eigspSet (l := 0) (by simp) b_zero_c
  have hz : zc ∈ S := mem_eigspSet (l := 0) (by simp) zc_zero_c
  have hd : d ∈ S := mem_eigspSet (l := 1/2) (by simp)
    (by rw [eig_c_half]; exact Submodule.subset_span rfl)
  have he : u = u 0 • a + u 1 • b + u 2 • zc + (u 4+2*u 2) • d := by
    funext k
    fin_cases k <;> simp [a,b,zc,d,e,hu,Matrix.vecHead,Matrix.vecTail]
    ring
  rw [he]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ ha)
    (S.smul_mem _ hb)) (S.smul_mem _ hz)) (S.smul_mem _ hd)

theorem c_fusion00 (u : A) (hu : u ∈ eigsp ExD.μ c 0)
    (v : A) (_hv : v ∈ eigsp ExD.μ c 0) : ExD.μ u v ∈ eigspSet ExD.μ c {0,1/2} := by
  apply c_no_one_mem
  rw [mul_formula]
  simp [c_zero_data hu]

theorem c_fusion0h (u : A) (hu : u ∈ eigsp ExD.μ c 0)
    (v : A) (_hv : v ∈ eigsp ExD.μ c (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ c {0,1/2} := by
  apply c_no_one_mem
  rw [mul_formula]
  simp [c_zero_data hu]

theorem d_sq : ExD.μ d d = 0 := by
  rw [mul_formula]
  funext k
  fin_cases k <;> norm_num [d,e,Pi.single_apply]

theorem c_fusionhh (u : A) (hu : u ∈ eigsp ExD.μ c (1/2))
    (v : A) (hv : v ∈ eigsp ExD.μ c (1/2)) : ExD.μ u v ∈ eigspSet ExD.μ c {1,0} := by
  rw [eig_c_half] at hu hv
  apply mul_mem_of_spans ?_ hu hv
  rw [d_sq]
  exact Submodule.zero_mem _

theorem primitive_a : IsPrimitiveAxis F ExD.μ a := by
  apply primitive_jmild (by norm_num) (by norm_num) commutative
  · intro h
    have hh := congrFun h 0
    norm_num [a,e,Pi.single_apply] at hh
  · rw [a_mul]
    funext k
    fin_cases k <;> norm_num [a,e,Pi.single_apply]
  · exact a_top
  · exact eig_a_one
  · exact a_fusion00
  · exact a_fusion0h
  · exact a_fusionhh

theorem primitive_b : IsPrimitiveAxis F ExD.μ b := by
  apply primitive_jmild (by norm_num) (by norm_num) commutative
  · intro h
    have hh := congrFun h 1
    norm_num [b,e,Pi.single_apply] at hh
  · rw [b_mul]
    funext k
    fin_cases k <;> norm_num [b,e,Pi.single_apply]
  · exact b_top
  · exact eig_b_one
  · exact b_fusion00
  · exact b_fusion0h
  · exact b_fusionhh

theorem primitive_c : IsPrimitiveAxis F ExD.μ c := by
  apply primitive_jmild (by norm_num) (by norm_num) commutative
  · intro h
    have hh := congrFun h 3
    norm_num [c,e,Pi.single_apply] at hh
  · rw [c_mul]
    funext k
    fin_cases k <;> norm_num [c,e,Pi.single_apply]
  · exact c_top
  · exact eig_c_one
  · exact c_fusion00
  · exact c_fusion0h
  · exact c_fusionhh

theorem x_from_ab : x = a+b-(4 : ℚ) • ExD.μ a b := by
  rw [a_mul]
  funext k
  fin_cases k <;> norm_num [a,b,x,e,Pi.single_apply]

theorem cx_eq_d : ExD.μ c x = d := by
  rw [c_mul]
  funext k
  fin_cases k <;> norm_num [x,d,e,Pi.single_apply]

theorem generates : gen ExD.μ ExD.X = ⊤ := by
  have ma : a ∈ gen ExD.μ ExD.X := mem_gen_of_mem (by simp [ExD.X,a])
  have mb : b ∈ gen ExD.μ ExD.X := mem_gen_of_mem (by simp [ExD.X,b])
  have mc : c ∈ gen ExD.μ ExD.X := mem_gen_of_mem (by simp [ExD.X,c])
  have mx : x ∈ gen ExD.μ ExD.X := by
    rw [x_from_ab]
    exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb)
      (Submodule.smul_mem _ _ (gen_isSubalgebra _ _ _ ma _ mb))
  have md : d ∈ gen ExD.μ ExD.X := by
    rw [← cx_eq_d]
    exact gen_isSubalgebra _ _ _ mc _ mx
  rw [eq_top_iff]
  intro u _
  rw [coordinates u]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ ma) (Submodule.smul_mem _ _ mb))
    (Submodule.smul_mem _ _ mx)) (Submodule.smul_mem _ _ mc)) (Submodule.smul_mem _ _ md)

theorem axial : IsPrimitiveAxialAlgebra F ExD.μ ExD.X := by
  refine ⟨commutative,?_,generates⟩
  rintro z (rfl | rfl | rfl)
  · exact primitive_a
  · exact primitive_b
  · exact primitive_c

#print axioms axial
end DecomposableExample
end CodexAxial
