import Research.TaskH.Gao.Challenge
import Research.TaskH.Fan.RootedLongPath

/-! The actual one-path base and exact family transports. No two-path theorem
or full Gao theorem is assumed. Every witness stays in the original graph. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V} {x y : V}

theorem has_admissible_one_of_path {p : G.Walk x y}
    (hp : p.IsPath) (hl : 2 ≤ p.length) : HasAdmissiblePaths G x y 1 := by
  refine ⟨p.length, 1, fun _ => p, hl, Or.inl rfl, ?_⟩
  intro i
  have hi0 : i.val = 0 := by have hi := i.isLt; omega
  exact ⟨hp, by
    change p.length = p.length + i.val * 1
    exact (congrArg (fun n : ℕ => p.length + n * 1) hi0).symm⟩

/-- Rooted two-connectivity alone suffices for the exact k=1 Gao conclusion. -/
theorem rooted_has_admissible_one [Fintype V]
    (h : TaskH.Fan.RootedTwoConnected G x y) : HasAdmissiblePaths G x y 1 := by
  obtain ⟨p, hp, hl⟩ := TaskH.Fan.rooted_exists_long_simple_path h
  exact has_admissible_one_of_path hp hl

theorem admissible_reverse {k a d : ℕ} {p : Fin k → G.Walk x y}
    (h : AdmissiblePathFamily G x y k a d p) :
    AdmissiblePathFamily G y x k a d (fun i => (p i).reverse) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i
  exact ⟨(h.2.2 i).1.reverse, by
    simpa only [Walk.length_reverse] using (h.2.2 i).2⟩

theorem admissible_initial_segment {m k a d : ℕ} {p : Fin k → G.Walk x y}
    (hmk : m ≤ k) (h : AdmissiblePathFamily G x y k a d p) :
    AdmissiblePathFamily G x y m a d
      (fun i => p ⟨i.val, lt_of_lt_of_le i.isLt hmk⟩) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i
  exact h.2.2 ⟨i.val, lt_of_lt_of_le i.isLt hmk⟩

theorem has_admissible_initial_segment {m k : ℕ} (hmk : m ≤ k)
    (h : HasAdmissiblePaths G x y k) : HasAdmissiblePaths G x y m := by
  obtain ⟨a, d, p, hp⟩ := h
  exact ⟨a, d, (fun i => p ⟨i.val, lt_of_lt_of_le i.isLt hmk⟩),
    admissible_initial_segment hmk hp⟩

#print axioms has_admissible_one_of_path
#print axioms rooted_has_admissible_one
#print axioms admissible_reverse
#print axioms admissible_initial_segment
#print axioms has_admissible_initial_segment
end TaskH.Gao
