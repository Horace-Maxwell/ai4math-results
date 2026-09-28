import Research.AxialMSZ.Proof.ExEBase
set_option autoImplicit false
namespace CodexAxial.DominanceExample
open AxialMSZ.Challenge

theorem a_vec : a = ![1,0,0,0] := by
  funext k
  fin_cases k <;> simp [a,e]
theorem b_vec : b = ![0,1,0,0] := by
  funext k
  fin_cases k <;> simp [b,e]
theorem x_vec : x = ![0,0,1,0] := by
  funext k
  fin_cases k <;> simp [x,e]
theorem c_vec : c = ![0,0,0,1] := by
  funext k
  fin_cases k <;> simp [c,e]

theorem x_mul (u : A) : ExE.μ x u =
    ![u 0/6-u 1/6-u 3/3, -u 0/6+u 1/6-u 3/3,
      u 0/6+u 1/6+u 2+u 3/3, 0] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExE.T,x,e] <;> ring

def plane : Submodule ℚ A where
  carrier := {u | u 3 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; change u 3+v 3=0; rw [hu,hv]; ring
  smul_mem' := by intro r u hu; change r*u 3=0; rw [hu]; ring

@[simp] theorem mem_plane (u : A) : u ∈ plane ↔ u 3 = 0 := Iff.rfl

theorem plane_ideal : IsIdeal ExE.μ plane := by
  intro u v hv
  have he : ExE.μ u v 3 = u 3*v 3 := by
    rw [mul_apply]
    simp [Fin.sum_univ_four,ExE.T]
  have hm : ExE.μ u v ∈ plane := by
    rw [mem_plane,he,(mem_plane v).mp hv,mul_zero]
  exact ⟨hm, (commutative _ _).symm ▸ hm⟩

theorem plane_span : plane = Submodule.span ℚ {a,b,x} := by
  apply le_antisymm
  · intro u hu
    have hd : u = u 0 • a + u 1 • b + u 2 • x := by
      have hz := (mem_plane u).mp hu
      rw [coordinates u]
      simp [hz]
    rw [hd]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl | rfl) <;> norm_num [mem_plane,a,b,x,e]

theorem b_from_a : b = (9 : ℚ) • ExE.μ b (ExE.μ a b) - (3 : ℚ) • ExE.μ a b := by
  rw [b_mul,a_mul]
  funext k
  fin_cases k <;> norm_num [a_vec,b_vec,Matrix.vecHead,Matrix.vecTail]

theorem a_from_b : a = (9 : ℚ) • ExE.μ a (ExE.μ a b) - (3 : ℚ) • ExE.μ a b := by
  simp only [a_mul]
  funext k
  fin_cases k <;> norm_num [a_vec,b_vec,Matrix.vecHead,Matrix.vecTail]

theorem plane_le_ideal_of_a {I : Submodule ℚ A} (hI : IsIdeal ExE.μ I) (ma : a ∈ I) : plane ≤ I := by
  have mab : ExE.μ a b ∈ I := (hI b a ma).2
  have mb : b ∈ I := by
    rw [b_from_a]
    exact I.sub_mem (I.smul_mem 9 (hI b _ mab).1) (I.smul_mem 3 mab)
  have mx : x ∈ I := by
    rw [x_from_ab]
    exact I.sub_mem (I.add_mem ma mb) (I.smul_mem 6 mab)
  rw [plane_span]
  exact Submodule.span_le.mpr (by rintro v (rfl | rfl | rfl) <;> assumption)

theorem plane_le_ideal_of_b {I : Submodule ℚ A} (hI : IsIdeal ExE.μ I) (mb : b ∈ I) : plane ≤ I := by
  have mab := (hI a b mb).1
  have ma : a ∈ I := by
    rw [a_from_b]
    exact I.sub_mem (I.smul_mem 9 (hI a _ mab).1) (I.smul_mem 3 mab)
  exact plane_le_ideal_of_a hI ma

theorem block_a : block ExE.μ a = plane := by
  apply le_antisymm
  · exact block_le_of_ideal plane_ideal (by norm_num [mem_plane,a,e])
  · exact plane_le_ideal_of_a (block_isIdeal _ _) (mem_block_self _ _)

theorem block_b : block ExE.μ b = plane := by
  apply le_antisymm
  · exact block_le_of_ideal plane_ideal (by norm_num [mem_plane,b,e])
  · exact plane_le_ideal_of_b (block_isIdeal _ _) (mem_block_self _ _)

theorem ideal_top_of_c {I : Submodule ℚ A} (hI : IsIdeal ExE.μ I) (mc : c ∈ I) : I = ⊤ := by
  have mw : w ∈ I := by
    have he : w = (3 : ℚ) • ExE.μ x c := by
      rw [x_mul]
      funext k
      fin_cases k <;> norm_num [w,c_vec]
    rw [he]
    exact I.smul_mem 3 (hI x c mc).1
  have mx : x ∈ I := by
    have he : x = (3/2 : ℚ) • ExE.μ x w := by
      rw [x_mul]
      funext k
      fin_cases k <;> norm_num [w,x_vec]
    rw [he]
    exact I.smul_mem _ (hI x w mw).1
  have max := (hI a x mx).1
  have ma : a ∈ I := by
    have he : a = (9 : ℚ) • ExE.μ a (ExE.μ a x) - (3 : ℚ) • ExE.μ a x := by
      simp only [a_mul]
      funext k
      fin_cases k <;> norm_num [a_vec,x_vec,Matrix.vecHead,Matrix.vecTail]
    rw [he]
    exact I.sub_mem (I.smul_mem 9 (hI a _ max).1) (I.smul_mem 3 max)
  have hplane := plane_le_ideal_of_a hI ma
  have mb : b ∈ I := hplane (by norm_num [mem_plane,b,e])
  rw [eq_top_iff]
  intro u _
  rw [coordinates u]
  exact I.add_mem (I.add_mem (I.add_mem (I.smul_mem _ ma) (I.smul_mem _ mb))
    (I.smul_mem _ mx)) (I.smul_mem _ mc)

theorem block_c : block ExE.μ c = ⊤ :=
  ideal_top_of_c (block_isIdeal _ _) (mem_block_self _ _)

theorem blocks_strict : block ExE.μ a < block ExE.μ c := by
  rw [block_a,block_c,lt_top_iff_ne_top]
  intro h
  have hc : c ∈ plane := h ▸ Submodule.mem_top
  norm_num [mem_plane,c,e] at hc

theorem blocks_equal : block ExE.μ a = block ExE.μ b := by rw [block_a,block_b]

theorem projector (u : A) :
    (1/2 : ℚ) • ((3 : ℚ) • ExE.μ c (ExE.μ c u) - ExE.μ c u) = u 3 • c := by
  simp only [c_mul]
  funext k
  fin_cases k <;> simp [c,e] <;> ring

theorem proper_ideal_le_plane {I : Submodule ℚ A} (hI : IsIdeal ExE.μ I) (hne : I ≠ ⊤) : I ≤ plane := by
  intro u hu
  rw [mem_plane]
  by_contra hz
  have hc := (hI c u hu).1
  have hcc := (hI c (ExE.μ c u) hc).1
  have hm : u 3 • c ∈ I := by
    rw [← projector]
    exact I.smul_mem _ (I.sub_mem (I.smul_mem 3 hcc) hc)
  have hi := I.smul_mem (u 3)⁻¹ hm
  have mc : c ∈ I := by simpa [smul_smul,inv_mul_cancel₀ hz] using hi
  exact hne (ideal_top_of_c hI mc)

theorem indecomposable : ¬ IsDecomposable ExE.μ := by
  intro h
  unfold IsDecomposable IsDecomposableSub at h
  have hl : sSup {J : Submodule ℚ A | IsIdealIn ExE.μ ⊤ J ∧ J ≠ ⊤} ≤ plane := by
    apply sSup_le
    intro J hJ
    exact proper_ideal_le_plane (fun u v hv => hJ.1.2 u Submodule.mem_top v hv) hJ.2
  rw [h] at hl
  have hc : c ∈ plane := hl Submodule.mem_top
  norm_num [mem_plane,c,e] at hc

#print axioms blocks_strict
#print axioms indecomposable
end CodexAxial.DominanceExample
