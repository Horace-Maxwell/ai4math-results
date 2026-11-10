import Research.CographDist.Challenge

/-! Sanity tests of the definitions in `Challenge.lean`. -/

set_option autoImplicit false

namespace CographDist.Tests

open CographDist

/-- The path on four vertices has an induced `P₄`, so it is not a cograph. -/
theorem pathGraph_four_not_cograph : ¬ IsCograph (SimpleGraph.pathGraph 4) := by
  intro h
  apply h
  refine ⟨id, Function.injective_id, ?_⟩
  intro i j
  simp [SimpleGraph.pathGraph_adj]

/-- The complete graph on two vertices has distance matrix `[[0,1],[1,0]]`, with eigenvalue `1`. -/
theorem complete_two_distEigenvalue_one : IsDistEigenvalue (⊤ : SimpleGraph (Fin 2)) 1 := by
  refine ⟨fun _ => 1, fun h => by simpa using congrFun h 0, ?_⟩
  funext i
  have hd : ∀ u v : Fin 2, (⊤ : SimpleGraph (Fin 2)).dist u v = if u = v then 0 else 1 := by
    intro u v
    split_ifs with huv
    · subst huv; simp
    · exact (SimpleGraph.dist_eq_one_iff_adj).2 (by simpa using huv)
  fin_cases i <;> simp [distMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]

/-- `2` is not a distance eigenvalue of `K₂` (the definition is not trivially true). -/
theorem complete_two_not_distEigenvalue_two : ¬ IsDistEigenvalue (⊤ : SimpleGraph (Fin 2)) 2 := by
  rintro ⟨x, hx, hD⟩
  have hd : ∀ u v : Fin 2, (⊤ : SimpleGraph (Fin 2)).dist u v = if u = v then 0 else 1 := by
    intro u v
    split_ifs with huv
    · subst huv; simp
    · exact (SimpleGraph.dist_eq_one_iff_adj).2 (by simpa using huv)
  have h0 := congrFun hD 0
  have h1 := congrFun hD 1
  simp [distMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd] at h0 h1
  apply hx
  funext i
  fin_cases i <;> simp <;> linarith

/-- `K₂` is connected. -/
theorem complete_two_connected : (⊤ : SimpleGraph (Fin 2)).Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases h : u = v
  · subst h; exact SimpleGraph.Reachable.refl _
  · exact (show (⊤ : SimpleGraph (Fin 2)).Adj u v by simpa using h).reachable

/-- `K₂` is a cograph (it has only two vertices). -/
theorem complete_two_isCograph : IsCograph (⊤ : SimpleGraph (Fin 2)) := by
  rintro ⟨f, hf, -⟩
  have := Fintype.card_le_of_injective f hf
  simp at this

end CographDist.Tests
