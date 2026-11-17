import Research.TaskH.Six.CycleSix

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- The forbidden-pair graph on the five positions other than q is the
union of a three-vertex path and an edge; its independence number is three. -/
theorem six_index_neighbor_bound (A : Finset (Fin 6)) (q : Fin 6)
    (hq : q ∉ A)
    (h13 : ¬ (q + 1 ∈ A ∧ q + 3 ∈ A))
    (h24 : ¬ (q + 2 ∈ A ∧ q + 4 ∈ A))
    (h35 : ¬ (q + 3 ∈ A ∧ q + 5 ∈ A)) : A.card ≤ 3 := by
  revert A q
  decide +kernel

def firstForbiddenPath (q : Fin 6) : Fin 5 → Fin 6 :=
  ![q + 1, q, q + 5, q + 4, q + 3]

def secondForbiddenPath (q : Fin 6) : Fin 5 → Fin 6 :=
  ![q + 2, q + 1, q, q + 5, q + 4]

def thirdForbiddenPath (q : Fin 6) : Fin 5 → Fin 6 :=
  ![q + 3, q + 2, q + 1, q, q + 5]

theorem firstForbiddenPath_injective (q : Fin 6) :
    Function.Injective (firstForbiddenPath q) := by
  revert q
  decide +kernel

theorem secondForbiddenPath_injective (q : Fin 6) :
    Function.Injective (secondForbiddenPath q) := by
  revert q
  decide +kernel

theorem thirdForbiddenPath_injective (q : Fin 6) :
    Function.Injective (thirdForbiddenPath q) := by
  revert q
  decide +kernel

theorem hexagon_adj_succ {f : Fin 6 → V} (hf : IsHexagon G f) (i : Fin 6) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2

theorem hexagon_adj_of_cyclic_neighbor {f : Fin 6 → V} (hf : IsHexagon G f)
    (i j : Fin 6) (h : i = j + 1 ∨ j = i + 1) : G.Adj (f i) (f j) := by
  rcases h with h | h
  · rw [h]
    exact (hexagon_adj_succ hf j).symm
  · rw [h]
    exact hexagon_adj_succ hf i

theorem firstForbiddenPath_adj {f : Fin 6 → V} (hf : IsHexagon G f) (q : Fin 6) :
    G.Adj (f (firstForbiddenPath q 0)) (f (firstForbiddenPath q 1)) ∧
    G.Adj (f (firstForbiddenPath q 1)) (f (firstForbiddenPath q 2)) ∧
    G.Adj (f (firstForbiddenPath q 2)) (f (firstForbiddenPath q 3)) ∧
    G.Adj (f (firstForbiddenPath q 3)) (f (firstForbiddenPath q 4)) := by
  have ht : ∀ (q : Fin 6) (i : Fin 4),
      firstForbiddenPath q i.castSucc = firstForbiddenPath q i.succ + 1 ∨
        firstForbiddenPath q i.succ = firstForbiddenPath q i.castSucc + 1 := by
    decide +kernel
  exact ⟨hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 0),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 1),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 2),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 3)⟩

theorem secondForbiddenPath_adj {f : Fin 6 → V} (hf : IsHexagon G f) (q : Fin 6) :
    G.Adj (f (secondForbiddenPath q 0)) (f (secondForbiddenPath q 1)) ∧
    G.Adj (f (secondForbiddenPath q 1)) (f (secondForbiddenPath q 2)) ∧
    G.Adj (f (secondForbiddenPath q 2)) (f (secondForbiddenPath q 3)) ∧
    G.Adj (f (secondForbiddenPath q 3)) (f (secondForbiddenPath q 4)) := by
  have ht : ∀ (q : Fin 6) (i : Fin 4),
      secondForbiddenPath q i.castSucc = secondForbiddenPath q i.succ + 1 ∨
        secondForbiddenPath q i.succ = secondForbiddenPath q i.castSucc + 1 := by
    decide +kernel
  exact ⟨hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 0),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 1),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 2),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 3)⟩

theorem thirdForbiddenPath_adj {f : Fin 6 → V} (hf : IsHexagon G f) (q : Fin 6) :
    G.Adj (f (thirdForbiddenPath q 0)) (f (thirdForbiddenPath q 1)) ∧
    G.Adj (f (thirdForbiddenPath q 1)) (f (thirdForbiddenPath q 2)) ∧
    G.Adj (f (thirdForbiddenPath q 2)) (f (thirdForbiddenPath q 3)) ∧
    G.Adj (f (thirdForbiddenPath q 3)) (f (thirdForbiddenPath q 4)) := by
  have ht : ∀ (q : Fin 6) (i : Fin 4),
      thirdForbiddenPath q i.castSucc = thirdForbiddenPath q i.succ + 1 ∨
        thirdForbiddenPath q i.succ = thirdForbiddenPath q i.castSucc + 1 := by
    decide +kernel
  exact ⟨hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 0),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 1),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 2),
    hexagon_adj_of_cyclic_neighbor hf _ _ (ht q 3)⟩

/-- R forbids an external vertex with a repeated path color from closing a
real four-edge simple path into a six-cycle. -/
theorem rainbow_forbids_four_path
    (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (t : Fin 5 → V) (ht : Function.Injective t)
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (y : V) (hy : y ≠ w) (hwt : ∀ i, t i ≠ w)
    (hyout : ∀ i, y ≠ t i) (j : Fin 5)
    (hcolor : c ⟨y, hy⟩ = c ⟨t j, hwt j⟩) :
    ¬ (G.Adj y (t 0) ∧ G.Adj y (t 4)) := by
  classical
  rintro ⟨hy0, hy4⟩
  let f : Fin 6 → V := ![y, t 0, t 1, t 2, t 3, t 4]
  have hn0 := hyout 0
  have hn1 := hyout 1
  have hn2 := hyout 2
  have hn3 := hyout 3
  have hn4 := hyout 4
  have hf : Function.Injective f := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [f, ht.eq_iff]
    all_goals first
      | exact hyout 0 hik.symm
      | exact hyout 1 hik.symm
      | exact hyout 2 hik.symm
      | exact hyout 3 hik.symm
  let p := hexagonWalk G f hy0 h01 h12 h23 h34 hy4.symm
  have hp : p.IsCycle := hexagonWalk_isCycle G f hf hy0 h01 h12 h23 h34 hy4.symm
  have hlen : p.length = 6 := rfl
  have hyin : y ∈ p.support := p.start_mem_support
  have htjin : t j ∈ p.support := by
    fin_cases j <;> simp [p, hexagonWalk, f, Walk.support_cons]
  have he := hr w c p hp hlen ⟨y, hy⟩ ⟨t j, hwt j⟩ hyin htjin hcolor
  exact hyout j (congrArg Subtype.val he)

end TaskH.Six

#print axioms TaskH.Six.six_index_neighbor_bound
#print axioms TaskH.Six.firstForbiddenPath
#print axioms TaskH.Six.secondForbiddenPath
#print axioms TaskH.Six.thirdForbiddenPath
#print axioms TaskH.Six.firstForbiddenPath_injective
#print axioms TaskH.Six.secondForbiddenPath_injective
#print axioms TaskH.Six.thirdForbiddenPath_injective
#print axioms TaskH.Six.hexagon_adj_succ
#print axioms TaskH.Six.hexagon_adj_of_cyclic_neighbor
#print axioms TaskH.Six.firstForbiddenPath_adj
#print axioms TaskH.Six.secondForbiddenPath_adj
#print axioms TaskH.Six.thirdForbiddenPath_adj
#print axioms TaskH.Six.rainbow_forbids_four_path
