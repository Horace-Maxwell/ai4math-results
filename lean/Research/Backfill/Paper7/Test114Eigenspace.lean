import Research.Backfill.Paper7.Test114Parameters

/-! The parameterization is a linear equivalence with the eigenspace of the
original SunV adjacency matrix. No reduced-matrix paper theorem is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 4096
open scoped Matrix
noncomputable section
namespace Paper7Test114

abbrev E := Module.End.eigenspace (Matrix.toEuclideanLin A) (1 : ℝ)
#print axioms Paper7Test114.E

theorem build_mem_eigenspace (u : Parameters) :
    WithLp.toLp 2 (build u) ∈ E := by
  apply Module.End.mem_eigenspace_iff.mpr
  change WithLp.toLp 2 (A *ᵥ build u) = (1 : ℝ) • WithLp.toLp 2 (build u)
  rw [one_smul, build_eigen]
#print axioms Paper7Test114.build_mem_eigenspace

theorem eigenvector_equation (v : E) :
    A *ᵥ WithLp.ofLp v.val = WithLp.ofLp v.val := by
  have h : Matrix.toEuclideanLin A v.val = v.val := by
    simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp v.property)
  have h' := congrArg (fun w : EuclideanSpace ℝ V => WithLp.ofLp w) h
  change A *ᵥ WithLp.ofLp v.val = WithLp.ofLp v.val at h'
  exact h'
#print axioms Paper7Test114.eigenvector_equation

/-- This equivalence includes both construction and recovery of every eigenvector. -/
def parametersEquiv : Parameters ≃ₗ[ℝ] E where
  toFun u := ⟨WithLp.toLp 2 (build u), build_mem_eigenspace u⟩
  invFun v := extract (WithLp.ofLp v.val)
  left_inv u := extract_build u
  right_inv v := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    change build (extract (WithLp.ofLp v.val)) = WithLp.ofLp v.val
    exact build_extract _ (eigenvector_equation v)
  map_add' u v := by
    apply Subtype.ext
    change WithLp.toLp 2 (build (u + v)) =
      WithLp.toLp 2 (build u) + WithLp.toLp 2 (build v)
    rw [build_add, WithLp.toLp_add]
  map_smul' c u := by
    apply Subtype.ext
    change WithLp.toLp 2 (build (c • u)) = c • WithLp.toLp 2 (build u)
    rw [build_smul, WithLp.toLp_smul]
#print axioms Paper7Test114.parametersEquiv

theorem eigenspace_finrank : Module.finrank ℝ E = 19 := by
  calc
    Module.finrank ℝ E = Module.finrank ℝ Parameters := parametersEquiv.finrank_eq.symm
    _ = 19 := by
      norm_num [Parameters, Module.finrank_prod, Module.finrank_pi, CommSemiring.finrank_self]
#print axioms Paper7Test114.eigenspace_finrank

end Paper7Test114
