import Research.TaskH.Gao.PathConcatenation

/-! Whole finite path families retain their common progression and actual support. -/
set_option autoImplicit false
universe u v
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {W : Type v}

theorem admissible_family_map (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hf : Function.Injective f) (x y : V) (k a d : ℕ)
    (p : Fin k → G.Walk x y) (hp : AdmissiblePathFamily G x y k a d p) :
    AdmissiblePathFamily H (f x) (f y) k a d (fun i => (p i).map f) ∧
      ∀ i w, w ∈ ((p i).map f).support ↔ ∃ z ∈ (p i).support, f z = w := by
  refine ⟨⟨hp.1, hp.2.1, ?_⟩, ?_⟩
  · intro i
    refine ⟨(Walk.isPath_map_iff_of_injective hf).mpr (hp.2.2 i).1, ?_⟩
    simpa only [Walk.length_map] using (hp.2.2 i).2
  · intro i w
    simp only [Walk.support_map, List.mem_map]

theorem admissible_family_reverse (G : SimpleGraph V) (x y : V) (k a d : ℕ)
    (p : Fin k → G.Walk x y) (hp : AdmissiblePathFamily G x y k a d p) :
    AdmissiblePathFamily G y x k a d (fun i => (p i).reverse) ∧
      ∀ i w, w ∈ (p i).reverse.support ↔ w ∈ (p i).support := by
  refine ⟨⟨hp.1, hp.2.1, ?_⟩, ?_⟩
  · intro i
    refine ⟨(hp.2.2 i).1.reverse, ?_⟩
    simpa only [Walk.length_reverse] using (hp.2.2 i).2
  · intro i w
    simp only [Walk.support_reverse, List.mem_reverse]

theorem admissible_family_append_fixed_tail (G : SimpleGraph V) (x y z : V)
    (k a d : ℕ) (p : Fin k → G.Walk x y) (r : G.Walk y z)
    (hp : AdmissiblePathFamily G x y k a d p) (hr : r.IsPath)
    (hmeet : ∀ i w, w ∈ (p i).support → w ∈ r.support → w = y) :
    AdmissiblePathFamily G x z k (a + r.length) d (fun i => (p i).append r) ∧
      ∀ i w, w ∈ ((p i).append r).support → w ∈ (p i).support ∨ w ∈ r.support := by
  have ha : 2 ≤ a + r.length := by
    have hh := hp.1
    omega
  refine ⟨⟨ha, hp.2.1, ?_⟩, ?_⟩
  · intro i
    refine ⟨append_isPath_of_only_common_endpoint (hp.2.2 i).1 hr (hmeet i), ?_⟩
    rw [Walk.length_append, (hp.2.2 i).2]
    omega
  · intro i w hw
    rw [Walk.support_append] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (List.mem_of_mem_tail hw)

#print axioms admissible_family_map
#print axioms admissible_family_reverse
#print axioms admissible_family_append_fixed_tail
end TaskH.Gao
