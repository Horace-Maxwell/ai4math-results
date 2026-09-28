import Research.AxialMSZ.Challenge
set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

private theorem jplus_finite_symmetric (η : ℚ) :
    (JPlus η).IsFiniteSymmetric := by
  refine ⟨?_, ?_, ?_⟩
  · simp [JPlus]
  · intro l m
    simp only [JPlus]
    split_ifs <;> simp_all
  · intro l hl m hm
    simp only [JPlus, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
    rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
      simp [JPlus] <;> split_ifs <;> simp_all

private theorem jmild_finite_symmetric (η : ℚ) :
    (JMild η).IsFiniteSymmetric := by
  refine ⟨?_, ?_, ?_⟩
  · simp [JMild]
  · intro l m
    simp only [JMild]
    split_ifs <;> simp_all
  · intro l hl m hm
    simp only [JMild, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
    rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
      simp [JMild] <;> split_ifs <;> simp_all

private theorem fd3_finite_symmetric : FD3.IsFiniteSymmetric := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FD3]
  · intro l m
    simp only [FD3]
    split_ifs <;> simp_all <;> aesop
  · intro l hl m hm
    simp only [FD3, Set.mem_insert_iff, Set.mem_singleton_iff] at hl hm
    rcases hl with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
      norm_num [FD3]

theorem check_Laws_facts : Laws_facts := by
  refine ⟨jplus_finite_symmetric _, jplus_finite_symmetric _, jmild_finite_symmetric _,
    fd3_finite_symmetric, ?_, ?_, ?_⟩
  · intro h
    have bad := h.2 0 (by simp [JPlus]) (by norm_num [JPlus] : (1 : ℚ) ∈ (JPlus (1/2 : ℚ)).star 0 0)
    norm_num at bad
  · intro h
    have bad := h.2 0 (by simp [JPlus]) (by norm_num [JPlus] : (1 : ℚ) ∈ (JPlus (1/3 : ℚ)).star 0 0)
    norm_num at bad
  · intro h
    have bad := h.2 0 (by simp [JMild]) (by norm_num [JMild] : (1/2 : ℚ) ∈ (JMild (1/2 : ℚ)).star 0 0)
    norm_num at bad

#print axioms check_Laws_facts
end CodexAxial
