import Research.AxialMSZ.Proof.ExDBase

/-! Exact block, internal ideals and decomposition for the frozen ExD contract. -/
set_option autoImplicit false
namespace CodexAxial.DecomposableExample
open AxialMSZ.Challenge

def I : Submodule ℚ A where
  carrier := {u | u 3 = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv; simp_all
  smul_mem' := by intro r u hu; simp_all

def J : Submodule ℚ A where
  carrier := {u | u 3 = 0 ∧ u 4 = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv; simp_all
  smul_mem' := by intro r u hu; simp_all

abbrev K : Submodule ℚ A := Submodule.span ℚ {d}

@[simp] theorem mem_I (u : A) : u ∈ I ↔ u 3 = 0 := Iff.rfl
@[simp] theorem mem_J (u : A) : u ∈ J ↔ u 3 = 0 ∧ u 4 = 0 := Iff.rfl

theorem I_eq_span : I = Submodule.span ℚ {a,b,x,d} := by
  apply le_antisymm
  · intro u hu
    have hz : u 3 = 0 := hu
    let S := Submodule.span ℚ ({a,b,x,d} : Set A)
    have ha : a ∈ S := Submodule.subset_span (by simp)
    have hb : b ∈ S := Submodule.subset_span (by simp)
    have hx : x ∈ S := Submodule.subset_span (by simp)
    have hd : d ∈ S := Submodule.subset_span (by simp)
    have he : u = u 0 • a + u 1 • b + u 2 • x + u 4 • d := by
      funext k
      fin_cases k <;> simp [a,b,x,d,e,hz]
    rw [he]
    exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ ha) (S.smul_mem _ hb))
      (S.smul_mem _ hx)) (S.smul_mem _ hd)
  · apply Submodule.span_le.mpr
    rintro u (rfl | rfl | rfl | rfl) <;> norm_num [a,b,x,d,e,Pi.single_apply]

theorem J_eq_span : J = Submodule.span ℚ {a,b,x} := by
  apply le_antisymm
  · intro u hu
    have hz3 : u 3 = 0 := hu.1
    have hz4 : u 4 = 0 := hu.2
    let S := Submodule.span ℚ ({a,b,x} : Set A)
    have ha : a ∈ S := Submodule.subset_span (by simp)
    have hb : b ∈ S := Submodule.subset_span (by simp)
    have hx : x ∈ S := Submodule.subset_span (by simp)
    have he : u = u 0 • a + u 1 • b + u 2 • x := by
      funext k
      fin_cases k <;> simp [a,b,x,e,hz3,hz4]
    rw [he]
    exact S.add_mem (S.add_mem (S.smul_mem _ ha) (S.smul_mem _ hb)) (S.smul_mem _ hx)
  · apply Submodule.span_le.mpr
    rintro u (rfl | rfl | rfl) <;> norm_num [a,b,x,e,Pi.single_apply]

theorem I_ideal : IsIdeal ExD.μ I := by
  intro u v hv
  have hz : v 3 = 0 := hv
  have h : ExD.μ u v ∈ I := by
    rw [mem_I,mul_formula]
    simp [hz]
  exact ⟨h,by rw [commutative v u]; exact h⟩

theorem b_from_a_products : b =
    (8 : ℚ) • ExD.μ b (ExD.μ a b) - (4 : ℚ) • ExD.μ a b := by
  rw [b_mul,a_mul]
  funext k
  fin_cases k <;> norm_num [a,b,e,Pi.single_apply]

theorem block_a : block ExD.μ a = I := by
  apply le_antisymm
  · exact block_le_of_ideal I_ideal (by norm_num [a,e,Pi.single_apply])
  · have ma : a ∈ block ExD.μ a := mem_block_self _ _
    have hI := block_isIdeal ExD.μ a
    have mab : ExD.μ a b ∈ block ExD.μ a := (hI b a ma).2
    have mbab : ExD.μ b (ExD.μ a b) ∈ block ExD.μ a := (hI b _ mab).1
    have mb : b ∈ block ExD.μ a := by
      rw [b_from_a_products]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ mbab) (Submodule.smul_mem _ _ mab)
    have mx : x ∈ block ExD.μ a := by
      rw [x_from_ab]
      exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb) (Submodule.smul_mem _ _ mab)
    have md : d ∈ block ExD.μ a := by
      rw [← cx_eq_d]
      exact (hI c x mx).1
    rw [I_eq_span]
    apply Submodule.span_le.mpr
    rintro u (rfl | rfl | rfl | rfl)
    · exact ma
    · exact mb
    · exact mx
    · exact md

theorem block_a_exact : block ExD.μ (e 0) = Submodule.span ℚ {e 0,e 1,e 2,e 4} := by
  simpa [a,b,x,d] using block_a.trans I_eq_span

theorem J_le_I : J ≤ I := by
  intro u hu
  exact hu.1

theorem K_le_I : K ≤ I := by
  apply Submodule.span_le.mpr
  rintro u rfl
  norm_num [d,e,Pi.single_apply]

theorem J_idealIn : IsIdealIn ExD.μ I J := by
  refine ⟨J_le_I,?_⟩
  intro u hu v hv
  have hu3 : u 3 = 0 := hu
  have hv3 : v 3 = 0 := hv.1
  have hv4 : v 4 = 0 := hv.2
  have h : ExD.μ u v ∈ J := by
    rw [mem_J,mul_formula]
    simp [hu3,hv3,hv4]
  exact ⟨h,by rw [commutative v u]; exact h⟩

theorem K_idealIn : IsIdealIn ExD.μ I K := by
  refine ⟨K_le_I,?_⟩
  intro u hu v hv
  have hu3 : u 3 = 0 := hu
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv
  have he : ExD.μ u (t • d) = 0 := by
    rw [mul_formula]
    funext k
    fin_cases k <;> simp [d,e,hu3]
  constructor
  · rw [he]; exact K.zero_mem
  · rw [commutative,he]; exact K.zero_mem

theorem J_ne_I : J ≠ I := by
  intro h
  have hd : d ∈ I := by norm_num [d,e,Pi.single_apply]
  have hdJ : d ∈ J := by rw [h]; exact hd
  norm_num [d,e,Pi.single_apply] at hdJ

theorem K_ne_I : K ≠ I := by
  intro h
  have ha : a ∈ I := by norm_num [a,e,Pi.single_apply]
  have haK : a ∈ K := by rw [h]; exact ha
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp haK
  have hh := congrFun ht 0
  norm_num [a,d,e,Pi.single_apply] at hh

theorem J_sup_K : J ⊔ K = I := by
  apply le_antisymm (sup_le J_le_I K_le_I)
  rw [I_eq_span]
  apply Submodule.span_le.mpr
  rintro u (rfl | rfl | rfl | rfl)
  · exact (show J ≤ J ⊔ K from le_sup_left) (by norm_num [a,e,Pi.single_apply] : a ∈ J)
  · exact (show J ≤ J ⊔ K from le_sup_left) (by norm_num [b,e,Pi.single_apply] : b ∈ J)
  · exact (show J ≤ J ⊔ K from le_sup_left) (by norm_num [x,e,Pi.single_apply] : x ∈ J)
  · exact (show K ≤ J ⊔ K from le_sup_right) (Submodule.subset_span rfl : d ∈ K)

theorem decomposable_I : IsDecomposableSub ExD.μ I := by
  unfold IsDecomposableSub
  apply le_antisymm
  · exact sSup_le fun B hB => hB.1.1
  · have hJ : J ≤ sSup {B : Submodule ℚ A | IsIdealIn ExD.μ I B ∧ B ≠ I} :=
      le_sSup ⟨J_idealIn,J_ne_I⟩
    have hK : K ≤ sSup {B : Submodule ℚ A | IsIdealIn ExD.μ I B ∧ B ≠ I} :=
      le_sSup ⟨K_idealIn,K_ne_I⟩
    exact J_sup_K.symm.trans_le (sup_le hJ hK)

theorem decomposable_block : IsDecomposableSub ExD.μ (block ExD.μ (e 0)) := by
  change IsDecomposableSub ExD.μ (block ExD.μ a)
  rw [block_a]
  exact decomposable_I

theorem first_internal_ideal :
    IsIdealIn ExD.μ (block ExD.μ (e 0)) (Submodule.span ℚ {e 0,e 1,e 2}) := by
  change IsIdealIn ExD.μ (block ExD.μ a) (Submodule.span ℚ {a,b,x})
  rw [block_a,← J_eq_span]
  exact J_idealIn

theorem second_internal_ideal :
    IsIdealIn ExD.μ (block ExD.μ (e 0)) (Submodule.span ℚ {e 4}) := by
  change IsIdealIn ExD.μ (block ExD.μ a) K
  rw [block_a]
  exact K_idealIn

theorem notWholeIdeal : ¬ IsIdeal ExD.μ (Submodule.span ℚ {e 0,e 1,e 2}) := by
  change ¬ IsIdeal ExD.μ (Submodule.span ℚ {a,b,x})
  rw [← J_eq_span]
  intro h
  have hx : x ∈ J := by norm_num [x,e,Pi.single_apply]
  have hd := (h c x hx).1
  rw [cx_eq_d] at hd
  norm_num [d,e,Pi.single_apply] at hd

#print axioms block_a_exact
#print axioms decomposable_block
#print axioms first_internal_ideal
#print axioms second_internal_ideal
#print axioms notWholeIdeal
end CodexAxial.DecomposableExample
