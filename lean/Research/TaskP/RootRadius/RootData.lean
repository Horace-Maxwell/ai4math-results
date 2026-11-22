import Research.TaskP.RootRadius.Challenge

open Polynomial Filter
open scoped Topology

namespace TaskP.GraphRootRadius.Proof

open Challenge

variable {V : Type*} [Fintype V]

theorem dominates_univ (G : SimpleGraph V) : Dominates G Finset.univ :=
  fun v => Or.inl (Finset.mem_univ v)

omit [Fintype V] in
theorem not_dominates_empty [Nonempty V] (G : SimpleGraph V) : ¬ Dominates G ∅ := by
  intro h
  simpa using h (Classical.arbitrary V)

theorem top_coefficient (G : SimpleGraph V) :
    (dominationPolynomial G).coeff (Fintype.card V) = 1 := by
  classical
  rw [dominationPolynomial, finsetSum_coeff, Finset.sum_eq_single Finset.univ]
  · simp [dominates_univ]
  · intro S _ hS
    have hc : S.card ≠ Fintype.card V := fun h => hS (S.card_eq_iff_eq_univ.mp h)
    split_ifs <;> simp [coeff_X_pow, Ne.symm hc]
  · simp

theorem poly_ne_zero (G : SimpleGraph V) : dominationPolynomial G ≠ 0 := by
  intro h
  simpa [h] using top_coefficient G

theorem zero_root [Nonempty V] (G : SimpleGraph V) : (dominationPolynomial G).eval 0 = 0 := by
  classical
  rw [dominationPolynomial, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro S _
  by_cases h : Dominates G S
  · have hs : S ≠ ∅ := by
      rintro rfl
      exact not_dominates_empty G h
    simp [h, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)]
  · simp [h]

theorem attain_graph [Nonempty V] (G : SimpleGraph V) :
    IsGreatest {r : ℝ | ∃ z : ℂ, (dominationPolynomial G).eval z = 0 ∧ ‖z‖ = r}
      (rootRadius G) := by
  apply Set.Nonempty.isGreatest_csSup
  · exact ⟨0, 0, zero_root G, norm_zero⟩
  · exact (finite_setOfPred_isRoot (poly_ne_zero G)).image norm

theorem attainment : Attainment := by
  intro V _ _ B a m ha _
  let : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact attain_graph (petalJoin a m B)

theorem friendship_of_general (hg : GeneralAsymptotic) : FriendshipAsymptotic := by
  classical
  have hN (v : Fin 2) : closedNeighborhood (⊤ : SimpleGraph (Fin 2)) v = Finset.univ := by
    ext u
    simp [closedNeighborhood, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj, eq_comm]
    tauto
  have hfun : closedNeighborhood (⊤ : SimpleGraph (Fin 2)) = fun _ => Finset.univ := funext hN
  have hc : minimumSize (⊤ : SimpleGraph (Fin 2)) = 2 := by
    unfold minimumSize
    convert! congrArg (fun n : ℕ => n + 1) (SimpleGraph.minDegree_top (V := Fin 2)) using 1
    congr 2
  have hs : minimumCount (⊤ : SimpleGraph (Fin 2)) = 1 := by
    simp [minimumCount, hfun, hc, Finset.image_const Finset.univ_nonempty, Finset.filter_singleton]
  simpa [FriendshipAsymptotic, friendshipGraph, scale, hc, hs, Real.sqrt_eq_rpow] using
    hg (⊤ : SimpleGraph (Fin 2)) 1 (by decide)

end TaskP.GraphRootRadius.Proof
