import Research.Backfill.Paper7.LegacyTestRequirements

/-! The actual 44-vertex SunV, with named coordinates. No paper contract is assumed.
Only the concrete λ=1 test is developed here. Source candidate; not compiled. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open scoped Matrix
namespace Paper7Test114
open BackfillPaper7.Challenge

abbrev P : Fin 4 → ℕ := ![0,0,0,0]
#print axioms Paper7Test114.P
abbrev Q : Fin 4 → ℕ := ![10,10,0,0]
#print axioms Paper7Test114.Q
abbrev V := SunV 4 (pq 4 P Q)
#print axioms Paper7Test114.V
abbrev G := SG 4 P Q
#print axioms Paper7Test114.G
noncomputable def A : Matrix V V ℝ := G.adjMatrix ℝ
#print axioms Paper7Test114.A

def root (k : Fin 4) : V := Sum.inl k
#print axioms Paper7Test114.root

/-- The dependent pendant-path length is exactly two for each actual arm. -/
theorem arm0_length (j : Fin 10) : (pq 4 P Q (0 : Fin 4)).get j = 2 := by
  fin_cases j <;> rfl
#print axioms Paper7Test114.arm0_length

theorem arm1_length (j : Fin 10) : (pq 4 P Q (1 : Fin 4)).get j = 2 := by
  fin_cases j <;> rfl
#print axioms Paper7Test114.arm1_length

def arm0 (j : Fin 10) (t : Fin 2) : V :=
  Sum.inr ⟨0, j, ⟨t.val, by rw [arm0_length]; exact t.isLt⟩⟩
#print axioms Paper7Test114.arm0

def arm1 (j : Fin 10) (t : Fin 2) : V :=
  Sum.inr ⟨1, j, ⟨t.val, by rw [arm1_length]; exact t.isLt⟩⟩
#print axioms Paper7Test114.arm1

theorem arm_index_bound (k : Fin 4) (j : Fin ((pq 4 P Q k).length)) : j.val < 10 := by
  have hj := j.isLt
  fin_cases k <;> simp [pq,P,Q] at hj <;> omega
#print axioms Paper7Test114.arm_index_bound

/-- Eliminate both dependent indices before reading the common path length. -/
theorem arm_position_bound (k : Fin 4) (j : Fin ((pq 4 P Q k).length))
    (t : Fin ((pq 4 P Q k).get j)) : t.val < 2 := by
  fin_cases k <;> fin_cases j <;> exact t.isLt
#print axioms Paper7Test114.arm_position_bound

theorem vertex_cases (v : V) :
    (∃ k : Fin 4, v = root k) ∨
    (∃ j : Fin 10, ∃ t : Fin 2, v = arm0 j t) ∨
    (∃ j : Fin 10, ∃ t : Fin 2, v = arm1 j t) := by
  rcases v with k | ⟨k,j,t⟩
  · exact Or.inl ⟨k,rfl⟩
  · fin_cases k
    · have ht : t.val < 2 := arm_position_bound (0 : Fin 4) j t
      exact Or.inr (Or.inl ⟨j,⟨t.val,ht⟩,rfl⟩)
    · have ht : t.val < 2 := arm_position_bound (1 : Fin 4) j t
      exact Or.inr (Or.inr ⟨j,⟨t.val,ht⟩,rfl⟩)
    · have hj := j.isLt
      simp [pq,P,Q] at hj
    · have hj := j.isLt
      simp [pq,P,Q] at hj
#print axioms Paper7Test114.vertex_cases

/-- A nondependent indexing type for precisely the original forty-four vertices. -/
abbrev PackedV := Fin 4 ⊕ ((Fin 10 × Fin 2) ⊕ (Fin 10 × Fin 2))
#print axioms Paper7Test114.PackedV

/-- Both inverse laws refer to the original SunV, including its dependent path indices. -/
def vertexEquiv : PackedV ≃ V where
  toFun := fun
    | Sum.inl k => root k
    | Sum.inr (Sum.inl (j,t)) => arm0 j t
    | Sum.inr (Sum.inr (j,t)) => arm1 j t
  invFun := fun
    | Sum.inl k => Sum.inl k
    | Sum.inr ⟨k,j,t⟩ =>
        if k = 0 then
          Sum.inr (Sum.inl (⟨j.val,arm_index_bound k j⟩,
            ⟨t.val,arm_position_bound k j t⟩))
        else
          Sum.inr (Sum.inr (⟨j.val,arm_index_bound k j⟩,
            ⟨t.val,arm_position_bound k j t⟩))
  left_inv := by
    rintro (k | (⟨j,t⟩ | ⟨j,t⟩)) <;> rfl
  right_inv := by
    intro v
    rcases vertex_cases v with ⟨k,rfl⟩ | ⟨j,t,rfl⟩ | ⟨j,t,rfl⟩ <;> rfl
#print axioms Paper7Test114.vertexEquiv

theorem vertexEquiv_root (k : Fin 4) : vertexEquiv (Sum.inl k) = root k := rfl
#print axioms Paper7Test114.vertexEquiv_root

theorem vertexEquiv_arm0 (j : Fin 10) (t : Fin 2) :
    vertexEquiv (Sum.inr (Sum.inl (j,t))) = arm0 j t := rfl
#print axioms Paper7Test114.vertexEquiv_arm0

theorem vertexEquiv_arm1 (j : Fin 10) (t : Fin 2) :
    vertexEquiv (Sum.inr (Sum.inr (j,t))) = arm1 j t := rfl
#print axioms Paper7Test114.vertexEquiv_arm1

/-- An exact change of finite summation indices, valid for every real-valued function. -/
theorem sum_vertices (f : V → ℝ) :
    (∑ v : V, f v) =
      (∑ k : Fin 4, f (root k)) +
      ((∑ j : Fin 10, ∑ t : Fin 2, f (arm0 j t)) +
       (∑ j : Fin 10, ∑ t : Fin 2, f (arm1 j t))) := by
  simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    vertexEquiv_root, vertexEquiv_arm0, vertexEquiv_arm1] using
    (vertexEquiv.sum_comp f).symm
#print axioms Paper7Test114.sum_vertices

/-- Only 4+40 actual coordinates are expanded; no determinant or eigenvalue enumeration. -/
macro "control_graph_simp" : tactic => `(tactic|
  (simp only [Matrix.mulVec, dotProduct]
   rw [sum_vertices]
   norm_num [A, Fin.sum_univ_succ, SimpleGraph.adjMatrix_apply,
     sunGraph, SimpleGraph.fromRel_adj, sunRel, pq, P, Q, root, arm0, arm1]
   <;> first
     | (split_ifs with h <;>
         first
           | (have hpos := congrArg (fun x => x.2.val) h
              norm_num at hpos)
           | rfl
           | ring)
     | rfl
     | ring))

theorem mul_root0 (f : V → ℝ) :
    (A *ᵥ f) (root 0) = f (root 1) + f (root 3) + ∑ j : Fin 10, f (arm0 j 0) := by
  control_graph_simp
#print axioms Paper7Test114.mul_root0

theorem mul_root1 (f : V → ℝ) :
    (A *ᵥ f) (root 1) = f (root 0) + f (root 2) + ∑ j : Fin 10, f (arm1 j 0) := by
  control_graph_simp
#print axioms Paper7Test114.mul_root1

theorem mul_root2 (f : V → ℝ) :
    (A *ᵥ f) (root 2) = f (root 1) + f (root 3) := by
  control_graph_simp
#print axioms Paper7Test114.mul_root2

theorem mul_root3 (f : V → ℝ) :
    (A *ᵥ f) (root 3) = f (root 0) + f (root 2) := by
  control_graph_simp
#print axioms Paper7Test114.mul_root3

theorem mul_arm0_inner (f : V → ℝ) (j : Fin 10) :
    (A *ᵥ f) (arm0 j 0) = f (root 0) + f (arm0 j 1) := by
  fin_cases j <;> control_graph_simp
#print axioms Paper7Test114.mul_arm0_inner

theorem mul_arm0_outer (f : V → ℝ) (j : Fin 10) :
    (A *ᵥ f) (arm0 j 1) = f (arm0 j 0) := by
  fin_cases j <;> control_graph_simp
#print axioms Paper7Test114.mul_arm0_outer

theorem mul_arm1_inner (f : V → ℝ) (j : Fin 10) :
    (A *ᵥ f) (arm1 j 0) = f (root 1) + f (arm1 j 1) := by
  fin_cases j <;> control_graph_simp
#print axioms Paper7Test114.mul_arm1_inner

theorem mul_arm1_outer (f : V → ℝ) (j : Fin 10) :
    (A *ᵥ f) (arm1 j 1) = f (arm1 j 0) := by
  fin_cases j <;> control_graph_simp
#print axioms Paper7Test114.mul_arm1_outer

/-- The exact equations at eigenvalue one, derived from the real adjacency matrix. -/
theorem eigen_one_coordinates (f : V → ℝ) (hf : A *ᵥ f = f) :
    f (root 0) = 0 ∧ f (root 1) = 0 ∧ f (root 3) = f (root 2) ∧
    (∀ j, f (arm0 j 1) = f (arm0 j 0)) ∧
    (∀ j, f (arm1 j 1) = f (arm1 j 0)) ∧
    (∑ j : Fin 10, f (arm0 j 0)) = - f (root 2) ∧
    (∑ j : Fin 10, f (arm1 j 0)) = - f (root 2) := by
  have ha (j : Fin 10) : f (arm0 j 1) = f (arm0 j 0) := by
    have h := congrFun hf (arm0 j 1)
    rw [mul_arm0_outer] at h
    exact h.symm
  have hb (j : Fin 10) : f (arm1 j 1) = f (arm1 j 0) := by
    have h := congrFun hf (arm1 j 1)
    rw [mul_arm1_outer] at h
    exact h.symm
  have h0 : f (root 0) = 0 := by
    have h := congrFun hf (arm0 0 0)
    rw [mul_arm0_inner, ha] at h
    linarith
  have h1 : f (root 1) = 0 := by
    have h := congrFun hf (arm1 0 0)
    rw [mul_arm1_inner, hb] at h
    linarith
  have h23 : f (root 3) = f (root 2) := by
    have h := congrFun hf (root 2)
    simpa [mul_root2,h1] using h
  refine ⟨h0,h1,h23,ha,hb,?_,?_⟩
  · have h := congrFun hf (root 0)
    rw [mul_root0,h0,h1,h23] at h
    linarith
  · have h := congrFun hf (root 1)
    rw [mul_root1,h0,h1] at h
    linarith
#print axioms Paper7Test114.eigen_one_coordinates

end Paper7Test114
