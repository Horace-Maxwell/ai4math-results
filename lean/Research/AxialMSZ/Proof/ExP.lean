import Research.AxialMSZ.Challenge

set_option autoImplicit false

namespace CodexAxial
open AxialMSZ.Challenge

section Closure
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_gen_of_mem {μ : V →ₗ[K] V →ₗ[K] V} {X : Set V} {a : V}
    (ha : a ∈ X) : a ∈ gen μ X :=
  Submodule.mem_sInf.mpr fun _ h => h.1 ha

theorem gen_le_of_closed {μ : V →ₗ[K] V →ₗ[K] V} {X : Set V}
    {S : Submodule K V} (hX : X ⊆ S) (hS : IsSubalgebra μ S) : gen μ X ≤ S :=
  sInf_le ⟨hX, hS⟩

theorem mem_block_self (μ : V →ₗ[K] V →ₗ[K] V) (a : V) : a ∈ block μ a :=
  Submodule.mem_sInf.mpr fun _ h => h.2

theorem block_le_of_ideal {μ : V →ₗ[K] V →ₗ[K] V} {a : V}
    {I : Submodule K V} (hI : IsIdeal μ I) (ha : a ∈ I) : block μ a ≤ I :=
  sInf_le ⟨hI, ha⟩

theorem block_isIdeal (μ : V →ₗ[K] V →ₗ[K] V) (a : V) : IsIdeal μ (block μ a) := by
  intro u v hv
  constructor
  · exact Submodule.mem_sInf.mpr fun I hI => (hI.1 u v (Submodule.mem_sInf.mp hv I hI)).1
  · exact Submodule.mem_sInf.mpr fun I hI => (hI.1 u v (Submodule.mem_sInf.mp hv I hI)).2

theorem mem_eigspSet {μ : V →ₗ[K] V →ₗ[K] V} {a u : V} {l : K} {L : Set K}
    (hl : l ∈ L) (hu : u ∈ eigsp μ a l) : u ∈ eigspSet μ a L := by
  change u ∈ ⨆ k ∈ L, eigsp μ a k
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem hl hu)

@[simp] theorem eigspSet_singleton (μ : V →ₗ[K] V →ₗ[K] V) (a : V) (l : K) :
    eigspSet μ a {l} = eigsp μ a l := by simp [eigspSet]

@[simp] theorem eigspSet_empty (μ : V →ₗ[K] V →ₗ[K] V) (a : V) :
    eigspSet μ a ∅ = ⊥ := by simp [eigspSet]

theorem mul_mem_of_spans {μ : V →ₗ[K] V →ₗ[K] V} {a b : V} {S : Submodule K V}
    (hab : μ a b ∈ S) {u v : V} (hu : u ∈ Submodule.span K {a})
    (hv : v ∈ Submodule.span K {b}) : μ u v ∈ S := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simpa using S.smul_mem t (S.smul_mem s hab)
end Closure

namespace Peng
abbrev A := Fin 2 → ℚ
abbrev a : A := e 0
abbrev b : A := e 1
abbrev w : A := ![1,-2]

theorem a_eq : a = ![1,0] := by
  ext k
  fin_cases k <;> simp [a,e]

theorem b_eq : b = ![0,1] := by
  ext k
  fin_cases k <;> simp [b,e]

theorem mul_formula (u v : A) :
    ExP.μ u v = ![u 0 * v 0, 2 * u 0 * v 1 + 2 * u 1 * v 0 + u 1 * v 1] := by
  ext k
  fin_cases k <;> simp [ExP.μ, structProduct, ExP.T, Fin.sum_univ_two]
  ring

theorem commutative : IsCommutative ExP.μ := by
  intro u v
  rw [mul_formula, mul_formula]
  ext k
  fin_cases k <;> simp <;> ring

theorem coordinates (u : A) : u = u 0 • a + u 1 • b := by
  ext k
  fin_cases k <;> simp [a,b,e]

theorem coordinates_b (u : A) : u = u 0 • w + (u 1 + 2*u 0) • b := by
  ext k
  fin_cases k <;> simp [w,b,e]
  ring

theorem eig_a_iff (u : A) (l : ℚ) :
    u ∈ eigsp ExP.μ a l ↔ u 0 = l * u 0 ∧ 2 * u 1 = l * u 1 := by
  rw [eigsp, Module.End.mem_eigenspace_iff, mul_formula]
  simp [a,e, funext_iff, Fin.forall_fin_two]

theorem eig_b_iff (u : A) (l : ℚ) :
    u ∈ eigsp ExP.μ b l ↔ 0 = l * u 0 ∧ 2 * u 0 + u 1 = l * u 1 := by
  rw [eigsp, Module.End.mem_eigenspace_iff, mul_formula]
  simp [b,e, funext_iff, Fin.forall_fin_two]

theorem eig_a_zero : eigsp ExP.μ a 0 = ⊥ := by
  ext u
  rw [eig_a_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨h0,h1⟩
    ext k
    fin_cases k <;> simp_all
  · rintro rfl
    simp

theorem eig_a_one : eigsp ExP.μ a 1 = Submodule.span ℚ {a} := by
  ext u
  rw [eig_a_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨_,h1⟩
    refine ⟨u 0, ?_⟩
    ext k
    fin_cases k <;> simp [a,e]
    linarith
  · rintro ⟨t,rfl⟩
    simp [a,e]

theorem eig_a_two : eigsp ExP.μ a 2 = Submodule.span ℚ {b} := by
  ext u
  rw [eig_a_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h0,_⟩
    refine ⟨u 1, ?_⟩
    ext k
    fin_cases k <;> simp [b,e]
    linarith
  · rintro ⟨t,rfl⟩
    simp [b,e]

theorem eig_b_zero : eigsp ExP.μ b 0 = Submodule.span ℚ {w} := by
  ext u
  rw [eig_b_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨_,h1⟩
    refine ⟨u 0, ?_⟩
    ext k
    fin_cases k <;> simp [w]
    linarith
  · rintro ⟨t,rfl⟩
    simp [w]
    ring

theorem eig_b_one : eigsp ExP.μ b 1 = Submodule.span ℚ {b} := by
  ext u
  rw [eig_b_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h0,_⟩
    have hz : u 0 = 0 := by linarith
    refine ⟨u 1, ?_⟩
    ext k
    fin_cases k <;> simp [b_eq,hz]
  · rintro ⟨t,rfl⟩
    simp [b,e]

theorem eig_b_two : eigsp ExP.μ b 2 = ⊥ := by
  ext u
  rw [eig_b_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨h0,h1⟩
    ext k
    fin_cases k <;> simp <;> linarith
  · rintro rfl
    simp

theorem a_decomposition : eigspSet ExP.μ a FD3.carrier = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have ha : a ∈ eigspSet ExP.μ a FD3.carrier :=
    mem_eigspSet (l := 1) (by norm_num [FD3]) (by rw [eig_a_one]; exact Submodule.subset_span rfl)
  have hb : b ∈ eigspSet ExP.μ a FD3.carrier :=
    mem_eigspSet (l := 2) (by norm_num [FD3]) (by rw [eig_a_two]; exact Submodule.subset_span rfl)
  rw [coordinates u]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem b_decomposition01 : eigspSet ExP.μ b {0,1} = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hw : w ∈ eigspSet ExP.μ b {0,1} :=
    mem_eigspSet (l := 0) (by simp) (by rw [eig_b_zero]; exact Submodule.subset_span rfl)
  have hb : b ∈ eigspSet ExP.μ b {0,1} :=
    mem_eigspSet (l := 1) (by simp) (by rw [eig_b_one]; exact Submodule.subset_span rfl)
  rw [coordinates_b u]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hb)

theorem b_decomposition : eigspSet ExP.μ b FD3.carrier = ⊤ := by
  rw [eq_top_iff, ← b_decomposition01]
  unfold eigspSet
  exact iSup_le fun l => iSup_le fun hl =>
    le_iSup_of_le l (le_iSup_of_le (by rcases hl with rfl | rfl <;> norm_num [FD3]) le_rfl)

theorem a_fusion : ∀ l ∈ FD3.carrier, ∀ m ∈ FD3.carrier,
    ∀ u ∈ eigsp ExP.μ a l, ∀ v ∈ eigsp ExP.μ a m,
      ExP.μ u v ∈ eigspSet ExP.μ a (FD3.star l m) := by
  intro l hl m hm u hu v hv
  simp only [FD3, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
  rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
    norm_num [FD3, eig_a_zero, eig_a_one, eig_a_two] at hu hv ⊢
  all_goals first
    | (subst u; simp)
    | (subst v; simp)
    | (apply mul_mem_of_spans ?_ hu hv
       rw [Submodule.mem_span_singleton]
       first
       | (refine ⟨1, ?_⟩; rw [mul_formula]; ext k; fin_cases k <;> norm_num [a_eq,b_eq]; all_goals done)
       | (refine ⟨2, ?_⟩; rw [mul_formula]; ext k; fin_cases k <;> norm_num [a_eq,b_eq]))

theorem b_fusion : ∀ l ∈ FD3.carrier, ∀ m ∈ FD3.carrier,
    ∀ u ∈ eigsp ExP.μ b l, ∀ v ∈ eigsp ExP.μ b m,
      ExP.μ u v ∈ eigspSet ExP.μ b (FD3.star l m) := by
  intro l hl m hm u hu v hv
  simp only [FD3, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
  rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
    norm_num [FD3, b_decomposition01, eig_b_zero, eig_b_one, eig_b_two] at hu hv ⊢
  all_goals first
    | (subst u; simp)
    | (subst v; simp)
    | (change ExP.μ u v ∈ (⊥ : Submodule ℚ A)
       apply mul_mem_of_spans ?_ hu hv
       rw [Submodule.mem_bot, mul_formula]
       ext k
       fin_cases k <;> norm_num [w,b_eq])
    | (apply mul_mem_of_spans ?_ hu hv
       rw [Submodule.mem_span_singleton]
       refine ⟨1, ?_⟩
       rw [mul_formula]
       ext k
       fin_cases k <;> norm_num [w,b_eq])

theorem a_primitive : IsPrimitiveAxis FD3 ExP.μ a := by
  refine ⟨⟨?_, ?_, a_decomposition, a_fusion⟩, eig_a_one⟩
  · intro h
    have := congrFun h 0
    norm_num [a,e] at this
  · rw [mul_formula]
    ext k
    fin_cases k <;> norm_num [a_eq]

theorem b_primitive : IsPrimitiveAxis FD3 ExP.μ b := by
  refine ⟨⟨?_, ?_, b_decomposition, b_fusion⟩, eig_b_one⟩
  · intro h
    have := congrFun h 1
    norm_num [b,e] at this
  · rw [mul_formula]
    ext k
    fin_cases k <;> norm_num [b_eq]

theorem generates : gen ExP.μ ExP.X = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have ha : a ∈ gen ExP.μ ExP.X := mem_gen_of_mem (by simp [ExP.X,a])
  have hb : b ∈ gen ExP.μ ExP.X := mem_gen_of_mem (by simp [ExP.X,b])
  rw [coordinates u]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem axial : IsPrimitiveAxialAlgebra FD3 ExP.μ ExP.X := by
  refine ⟨commutative, ?_, generates⟩
  rintro x (rfl | rfl)
  · exact a_primitive
  · exact b_primitive

theorem b_span_ideal : IsIdeal ExP.μ (Submodule.span ℚ {b}) := by
  intro u v hv
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv
  have h : ExP.μ u (t • b) ∈ Submodule.span ℚ {b} := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(2*u 0+u 1)*t, ?_⟩
    rw [mul_formula]
    ext k
    fin_cases k <;> simp [b,e]
    ring
  exact ⟨h, (commutative _ _).symm ▸ h⟩

theorem block_b : block ExP.μ b = Submodule.span ℚ {b} := by
  apply le_antisymm
  · exact block_le_of_ideal b_span_ideal (Submodule.subset_span rfl)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (mem_block_self _ _))

theorem block_a : block ExP.μ a = ⊤ := by
  rw [eq_top_iff]
  have ha := mem_block_self ExP.μ a
  have hm := (block_isIdeal ExP.μ a b a ha).1
  have hb : b ∈ block ExP.μ a := by
    have he : (1/2 : ℚ) • ExP.μ b a = b := by
      rw [mul_formula]
      ext k
      fin_cases k <;> norm_num [a_eq,b_eq]
    rw [← he]
    exact Submodule.smul_mem _ _ hm
  intro u _
  rw [coordinates u]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem blocks_strict : block ExP.μ b < block ExP.μ a := by
  rw [block_b, block_a, lt_top_iff_ne_top]
  intro h
  have ha : a ∈ Submodule.span ℚ {b} := h ▸ Submodule.mem_top
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp ha
  have hc := congrFun ht 0
  norm_num [a,b,e] at hc

end Peng

theorem check_RemarkP : AxialMSZ.Challenge.RemarkP := ⟨Peng.axial, Peng.blocks_strict⟩
theorem check_ExP_Statement : AxialMSZ.Challenge.ExP.Statement := check_RemarkP

#print axioms check_RemarkP
#print axioms check_ExP_Statement
end CodexAxial
