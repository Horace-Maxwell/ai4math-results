import Research.TaskH.Fan.RootEdgeNormalization
import Research.TaskH.Gao.RootedCutAdmissible

/-! The existing same-vertex root-edge deletion is reused literally.
Its identity inclusion preserves every length and support in an entire family. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem admissible_family_of_rootEdgeDeleted (G : SimpleGraph V) (x y : V)
    (k a d : ℕ) (p : Fin k → (rootEdgeDeleted G x y).Walk x y)
    (hp : AdmissiblePathFamily (rootEdgeDeleted G x y) x y k a d p) :
    AdmissiblePathFamily G x y k a d
      (fun i => (p i).map (rootEdgeDeletedInclusion G x y)) ∧
      (∀ i, ((p i).map (rootEdgeDeletedInclusion G x y)).length = (p i).length) ∧
      ∀ i, ((p i).map (rootEdgeDeletedInclusion G x y)).support = (p i).support := by
  have hf : Function.Injective (rootEdgeDeletedInclusion G x y) := fun _ _ h => h
  refine ⟨(admissible_family_map (rootEdgeDeleted G x y) G
    (rootEdgeDeletedInclusion G x y) hf x y k a d p hp).1, ?_, ?_⟩
  · intro i
    exact Walk.length_map (p := p i) (f := rootEdgeDeletedInclusion G x y)
  · intro i
    exact Walk.support_mapLe_eq_support (rootEdgeDeleted_le G x y) (p i)

theorem has_admissible_paths_of_rootEdgeDeleted (G : SimpleGraph V) (x y : V) (k : ℕ)
    (h : HasAdmissiblePaths (rootEdgeDeleted G x y) x y k) :
    HasAdmissiblePaths G x y k := by
  obtain ⟨a, d, p, hp⟩ := h
  exact ⟨a, d, (fun i => (p i).map (rootEdgeDeletedInclusion G x y)),
    (admissible_family_of_rootEdgeDeleted G x y k a d p hp).1⟩

theorem normalized_counterexample_preprocessing [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hroot : RootedTwoConnected G x y) (hk : 1 ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a c : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected J a c →
        NonrootDegreeAtLeast J a c (ell + 1) → HasAdmissiblePaths J a c ell)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ¬(rootEdgeDeleted G x y).Adj x y ∧
      RootedTwoConnected (rootEdgeDeleted G x y) x y ∧
      NonrootDegreeAtLeast (rootEdgeDeleted G x y) x y (k + 1) ∧
      ¬HasAdmissiblePaths (rootEdgeDeleted G x y) x y k ∧
      TwoConnected (rootEdgeDeleted G x y) := by
  have hr := rootEdgeDeleted_rooted_two_connected G x y hroot
  have hd := rootEdgeDeleted_nonroot_degree G x y (k + 1) hdeg
  have hn : ¬HasAdmissiblePaths (rootEdgeDeleted G x y) x y k := by
    intro h
    exact hno (has_admissible_paths_of_rootEdgeDeleted G x y k h)
  exact ⟨rootEdgeDeleted_not_adj G x y, hr, hd, hn,
    ordinary_twoConnected_of_no_admissible_with_smaller_IH
      (rootEdgeDeleted G x y) x y k hr hk hd ih hn⟩

#print axioms admissible_family_of_rootEdgeDeleted
#print axioms has_admissible_paths_of_rootEdgeDeleted
#print axioms normalized_counterexample_preprocessing
end TaskH.Gao
