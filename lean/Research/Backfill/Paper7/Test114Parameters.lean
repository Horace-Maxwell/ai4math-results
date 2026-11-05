import Research.Backfill.Paper7.Test114Coordinates

/-! Explicit 1+9+9 parameters for the actual eigenvectors at one. -/
set_option autoImplicit false
set_option maxRecDepth 4096
open scoped Matrix
noncomputable section
namespace Paper7Test114
open Finset

abbrev Parameters := ℝ × ((Fin 9 → ℝ) × (Fin 9 → ℝ))
#print axioms Paper7Test114.Parameters

def ten (t : ℝ) (a : Fin 9 → ℝ) : Fin 10 → ℝ :=
  Fin.cases (-t - ∑ j, a j) a
#print axioms Paper7Test114.ten

def build (u : Parameters) : V → ℝ
  | Sum.inl k => ![0,0,u.1,u.1] k
  | Sum.inr ⟨k,j,_⟩ =>
      if k = 0 then ten u.1 u.2.1 ⟨j.val,arm_index_bound k j⟩
      else ten u.1 u.2.2 ⟨j.val,arm_index_bound k j⟩
#print axioms Paper7Test114.build

def extract (f : V → ℝ) : Parameters :=
  (f (root 2), (fun j => f (arm0 j.succ 0), fun j => f (arm1 j.succ 0)))
#print axioms Paper7Test114.extract

theorem build_root (u : Parameters) (k : Fin 4) :
    build u (root k) = ![0,0,u.1,u.1] k := rfl
#print axioms Paper7Test114.build_root

theorem build_arm0 (u : Parameters) (j : Fin 10) (t : Fin 2) :
    build u (arm0 j t) = ten u.1 u.2.1 j := rfl
#print axioms Paper7Test114.build_arm0

theorem build_arm1 (u : Parameters) (j : Fin 10) (t : Fin 2) :
    build u (arm1 j t) = ten u.1 u.2.2 j := rfl
#print axioms Paper7Test114.build_arm1

theorem sum_ten (t : ℝ) (a : Fin 9 → ℝ) : ∑ j, ten t a j = -t := by
  rw [Fin.sum_univ_succ]
  simp only [ten, Fin.cases_zero, Fin.cases_succ]
  ring
#print axioms Paper7Test114.sum_ten

theorem ten_add (t s : ℝ) (a b : Fin 9 → ℝ) (j : Fin 10) :
    ten (t+s) (a+b) j = ten t a j + ten s b j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [ten, Fin.cases_zero, Pi.add_apply, Finset.sum_add_distrib]
    ring
  · simp [ten]
#print axioms Paper7Test114.ten_add

theorem ten_smul (c t : ℝ) (a : Fin 9 → ℝ) (j : Fin 10) :
    ten (c*t) (c • a) j = c * ten t a j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [ten, Fin.cases_zero, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  · simp [ten]
#print axioms Paper7Test114.ten_smul

theorem build_add (u v : Parameters) : build (u+v) = build u + build v := by
  funext x
  rcases vertex_cases x with ⟨k,rfl⟩ | ⟨j,t,rfl⟩ | ⟨j,t,rfl⟩
  · fin_cases k <;> simp [build_root]
  · exact ten_add u.1 v.1 u.2.1 v.2.1 j
  · exact ten_add u.1 v.1 u.2.2 v.2.2 j
#print axioms Paper7Test114.build_add

theorem build_smul (c : ℝ) (u : Parameters) : build (c • u) = c • build u := by
  funext x
  rcases vertex_cases x with ⟨k,rfl⟩ | ⟨j,t,rfl⟩ | ⟨j,t,rfl⟩
  · fin_cases k <;> simp [build_root]
  · exact ten_smul c u.1 u.2.1 j
  · exact ten_smul c u.1 u.2.2 j
#print axioms Paper7Test114.build_smul

theorem build_eigen (u : Parameters) : A *ᵥ build u = build u := by
  funext x
  rcases vertex_cases x with ⟨k,rfl⟩ | ⟨j,t,rfl⟩ | ⟨j,t,rfl⟩
  · fin_cases k
    · simp [mul_root0,build_root,build_arm0,sum_ten]
    · simp [mul_root1,build_root,build_arm1,sum_ten]
    · simp [mul_root2,build_root]
    · simp [mul_root3,build_root]
  · fin_cases t
    · simp [mul_arm0_inner,build_root,build_arm0]
    · simp [mul_arm0_outer,build_arm0]
  · fin_cases t
    · simp [mul_arm1_inner,build_root,build_arm1]
    · simp [mul_arm1_outer,build_arm1]
#print axioms Paper7Test114.build_eigen

theorem extract_build (u : Parameters) : extract (build u) = u := by
  apply Prod.ext
  · simp [extract,build_root]
  · apply Prod.ext <;> funext j
    · simp [extract,build_arm0,ten]
    · simp [extract,build_arm1,ten]
#print axioms Paper7Test114.extract_build

theorem ten_reconstruct (f : Fin 10 → ℝ) (t : ℝ) (hs : ∑ j, f j = -t) :
    ten t (fun j => f j.succ) = f := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Fin.sum_univ_succ] at hs
    simp only [ten,Fin.cases_zero]
    linarith
  · simp [ten]
#print axioms Paper7Test114.ten_reconstruct

theorem build_extract (f : V → ℝ) (hf : A *ᵥ f = f) : build (extract f) = f := by
  obtain ⟨h0,h1,h3,ha,hb,hsa,hsb⟩ := eigen_one_coordinates f hf
  have hra := ten_reconstruct (fun j => f (arm0 j 0)) (f (root 2)) hsa
  have hrb := ten_reconstruct (fun j => f (arm1 j 0)) (f (root 2)) hsb
  funext x
  rcases vertex_cases x with ⟨k,rfl⟩ | ⟨j,t,rfl⟩ | ⟨j,t,rfl⟩
  · fin_cases k <;> simp [build_root,extract,h0,h1,h3]
  · fin_cases t
    · change ten (f (root 2)) (fun k => f (arm0 k.succ 0)) j = f (arm0 j 0)
      exact congrFun hra j
    · change ten (f (root 2)) (fun k => f (arm0 k.succ 0)) j = f (arm0 j 1)
      exact (congrFun hra j).trans (ha j).symm
  · fin_cases t
    · change ten (f (root 2)) (fun k => f (arm1 k.succ 0)) j = f (arm1 j 0)
      exact congrFun hrb j
    · change ten (f (root 2)) (fun k => f (arm1 k.succ 0)) j = f (arm1 j 1)
      exact (congrFun hrb j).trans (hb j).symm
#print axioms Paper7Test114.build_extract

end Paper7Test114
