import Research.TaskP.GeomSimplex.TCoordinates

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

private theorem collinear_minors {a b c : Lattice 3}
    (h : Collinear ℝ ({realPoint a, realPoint b, realPoint c} : Set (Space 3))) (i j : Fin 3) :
    (b i - a i) * (c j - a j) = (b j - a j) * (c i - a i) := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (show realPoint a ∈
    ({realPoint a, realPoint b, realPoint c} : Set (Space 3)) by simp)).mp h
  obtain ⟨r, hr⟩ := hv (realPoint b) (by simp)
  obtain ⟨s, hs⟩ := hv (realPoint c) (by simp)
  have hb (n : Fin 3) : (b n : ℝ) - a n = r * v n := by
    have e := congrFun hr n
    change (b n : ℝ) = r * v n + a n at e
    linarith
  have hc (n : Fin 3) : (c n : ℝ) - a n = s * v n := by
    have e := congrFun hs n
    change (c n : ℝ) = s * v n + a n at e
    linarith
  apply (Int.cast_inj (α := ℝ)).mp
  push_cast
  rw [hb, hb, hc, hc]
  ring

private def minor (a b c : Lattice 3) (i j : Fin 3) : Prop :=
  (b i - a i) * (c j - a j) = (b j - a j) * (c i - a i)

private instance (a b c : Lattice 3) (i j : Fin 3) : Decidable (minor a b c i j) :=
  inferInstanceAs (Decidable (_ = _))

set_option maxHeartbeats 1600000 in
private theorem diameter_table : ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k →
    ¬ (minor (tpoints i) (tpoints j) (tpoints k) 0 1 ∧
       minor (tpoints i) (tpoints j) (tpoints k) 0 2 ∧
       minor (tpoints i) (tpoints j) (tpoints k) 1 2) := by decide

theorem diameterT : diameterOne (simplex verticesT) := by
  refine ⟨⟨verticesT 0, verticesT 1, by decide, vertex_mem _ _, vertex_mem _ _⟩, ?_⟩
  intro a b c ha hb hc hcol
  obtain ⟨i, rfl⟩ := points_of_T ha
  obtain ⟨j, rfl⟩ := points_of_T hb
  obtain ⟨k, rfl⟩ := points_of_T hc
  by_contra! hd
  apply diameter_table i j k (fun h => hd.1 (congrArg tpoints h))
    (fun h => hd.2.1 (congrArg tpoints h)) (fun h => hd.2.2 (congrArg tpoints h))
  exact ⟨collinear_minors hcol _ _, collinear_minors hcol _ _, collinear_minors hcol _ _⟩

end TaskP.GeomSimplex.Proof
