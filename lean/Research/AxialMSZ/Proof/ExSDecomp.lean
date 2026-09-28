import Research.AxialMSZ.Proof.ExSBase

set_option autoImplicit false

namespace CodexAxial
open AxialMSZ.Challenge

section SumDecomposition
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Pairwise annihilating subalgebras that generate a simple algebra include the whole algebra. -/
theorem simple_onlyTrivialSumDecompositions
    {μ : V →ₗ[ℚ] V →ₗ[ℚ] V} (hcomm : IsCommutative μ)
    (hsimple : IsSimpleAlg μ) : OnlyTrivialSumDecompositions μ := by
  classical
  intro S hS
  let W : Submodule ℚ V := ⨆ B : {B : Submodule ℚ V // B ∈ S}, B.val
  have hle (B : Submodule ℚ V) (hB : B ∈ S) : B ≤ W := by
    exact le_iSup (fun C : {B : Submodule ℚ V // B ∈ S} => C.val) ⟨B,hB⟩
  have hmul (B C : Submodule ℚ V) (hB : B ∈ S) (hC : C ∈ S)
      (u : V) (hu : u ∈ B) (v : V) (hv : v ∈ C) : μ u v ∈ W := by
    by_cases he : B = C
    · subst C
      exact hle B hB (hS.1 B hB u hu v hv)
    · rw [hS.2.1 B hB C hC he u hu v hv]
      exact W.zero_mem
  have hclosed : IsSubalgebra μ W := by
    intro u hu
    change u ∈ ⨆ B : {B : Submodule ℚ V // B ∈ S}, B.val at hu
    refine Submodule.iSup_induction (fun B : {B : Submodule ℚ V // B ∈ S} => B.val)
      (motive := fun u => ∀ v ∈ W, μ u v ∈ W) hu ?_ ?_ ?_
    · intro B u hu v hv
      change v ∈ ⨆ B : {B : Submodule ℚ V // B ∈ S}, B.val at hv
      refine Submodule.iSup_induction (fun C : {B : Submodule ℚ V // B ∈ S} => C.val)
        (motive := fun v => μ u v ∈ W) hv ?_ ?_ ?_
      · intro C v hv
        exact hmul B.val C.val B.property C.property u hu v hv
      · simp
      · intro v w hv hw
        simpa only [map_add] using W.add_mem hv hw
    · intro v _
      simp
    · intro u w hu hw v hv
      simpa only [map_add, LinearMap.add_apply] using W.add_mem (hu v hv) (hw v hv)
  have hunion : (⋃ B ∈ S, (B : Set V)) ⊆ W := by
    intro u hu
    simp only [Set.mem_iUnion] at hu
    obtain ⟨B,hB,hu⟩ := hu
    exact hle B hB hu
  have hWtop : W = ⊤ := by
    apply top_unique
    rw [← hS.2.2]
    exact gen_le_of_closed hunion hclosed
  have hideal (B : Submodule ℚ V) (hB : B ∈ S) : IsIdeal μ B := by
    have hleft (u : V) (v : V) (hv : v ∈ B) : μ u v ∈ B := by
      have hu : u ∈ W := by rw [hWtop]; trivial
      change u ∈ ⨆ C : {B : Submodule ℚ V // B ∈ S}, C.val at hu
      refine Submodule.iSup_induction (fun C : {B : Submodule ℚ V // B ∈ S} => C.val)
        (motive := fun u => μ u v ∈ B) hu ?_ ?_ ?_
      · intro C u hu
        by_cases he : C.val = B
        · exact hS.1 B hB u (he ▸ hu) v hv
        · rw [hS.2.1 C.val C.property B hB he u hu v hv]
          exact B.zero_mem
      · simp
      · intro u w hu hw
        simpa only [map_add, LinearMap.add_apply] using B.add_mem hu hw
    intro u v hv
    exact ⟨hleft u v hv, by rw [hcomm v u]; exact hleft u v hv⟩
  by_contra hnot
  have hbot (B : Submodule ℚ V) (hB : B ∈ S) : B = ⊥ := by
    rcases hsimple.2 B (hideal B hB) with hb | ht
    · exact hb
    · exact False.elim (hnot (ht ▸ hB))
  have hWbot : W ≤ ⊥ := by
    apply iSup_le
    intro B
    rw [hbot B.val B.property]
  obtain ⟨u,v,hnz⟩ := hsimple.1
  have hu : u = 0 := by
    apply (Submodule.mem_bot ℚ).mp
    apply hWbot
    rw [hWtop]
    trivial
  apply hnz
  simp [hu]

end SumDecomposition
end CodexAxial
