import Research.TaskH.Five.CycleFive

/-!
The five-position matching obstruction and its actual graph path bridge.
Only the fixed five-position identities use finite kernel computation.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem five_index_neighbor_bound (A : Finset (Fin 5)) (q : Fin 5)
    (hq : q ∉ A)
    (h13 : ¬ (q + 1 ∈ A ∧ q + 3 ∈ A))
    (h24 : ¬ (q + 2 ∈ A ∧ q + 4 ∈ A)) : A.card ≤ 2 := by
  revert A q
  decide +kernel

def firstForbiddenPath (q : Fin 5) : Fin 4 → Fin 5 :=
  ![q + 1, q, q + 4, q + 3]

def secondForbiddenPath (q : Fin 5) : Fin 4 → Fin 5 :=
  ![q + 2, q + 1, q, q + 4]

theorem firstForbiddenPath_injective (q : Fin 5) :
    Function.Injective (firstForbiddenPath q) := by
  revert q
  decide +kernel

theorem secondForbiddenPath_injective (q : Fin 5) :
    Function.Injective (secondForbiddenPath q) := by
  revert q
  decide +kernel

theorem pentagon_adj_succ {f : Fin 5 → V} (hf : IsPentagon G f) (i : Fin 5) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2

/-- A repeated deleted-vertex color cannot close an actual three-edge simple
path through an external point into a five-cycle. -/
theorem rainbow_forbids_three_path
    (hr : RainbowFiveCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 5))
    (t : Fin 4 → V) (ht : Function.Injective t)
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3))
    (y : V) (hy : y ≠ w) (hwt : ∀ i, t i ≠ w)
    (hyout : ∀ i, y ≠ t i) (j : Fin 4)
    (hcolor : c ⟨y, hy⟩ = c ⟨t j, hwt j⟩) :
    ¬ (G.Adj y (t 0) ∧ G.Adj y (t 3)) := by
  classical
  rintro ⟨hy0, hy3⟩
  let f : Fin 5 → V := ![y, t 0, t 1, t 2, t 3]
  have hn0 := hyout 0
  have hn1 := hyout 1
  have hn2 := hyout 2
  have hn3 := hyout 3
  have hf : Function.Injective f := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [f, ht.eq_iff]
    all_goals first
      | exact hyout 1 hik.symm
      | exact hyout 2 hik.symm
  let p := pentagonWalk G f hy0 h01 h12 h23 hy3.symm
  have hp : p.IsCycle := pentagonWalk_isCycle G f hf hy0 h01 h12 h23 hy3.symm
  have hlen : p.length = 5 := rfl
  have hyin : y ∈ p.support := p.start_mem_support
  have htjin : t j ∈ p.support := by
    fin_cases j <;> simp [p, pentagonWalk, f, Walk.support_cons]
  have he := hr w c p hp hlen ⟨y, hy⟩ ⟨t j, hwt j⟩ hyin htjin hcolor
  exact hyout j (congrArg Subtype.val he)

end TaskH.Five

#print axioms TaskH.Five.five_index_neighbor_bound
#print axioms TaskH.Five.firstForbiddenPath_injective
#print axioms TaskH.Five.secondForbiddenPath_injective
#print axioms TaskH.Five.pentagon_adj_succ
#print axioms TaskH.Five.rainbow_forbids_three_path
