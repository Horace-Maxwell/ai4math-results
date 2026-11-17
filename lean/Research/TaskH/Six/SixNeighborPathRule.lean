import Research.TaskH.Six.CycleSix

/-! A genuine four-edge path between neighbors closes to a counted hexagon. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def neighborPathHexagon (v : V) (t : Fin 5 → V) : Fin 6 → V :=
  ![v, t 0, t 1, t 2, t 3, t 4]

theorem neighborPathHexagon_injective (v : V) (t : Fin 5 → V)
    (ht : Function.Injective t) (htv : ∀ i, t i ≠ v) :
    Function.Injective (neighborPathHexagon v t) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [neighborPathHexagon, ht.eq_iff]

theorem neighborPathHexagon_isHexagon (v : V) (t : Fin 5 → V)
    (ht : Function.Injective t) (htv : ∀ i, t i ≠ v)
    (hv0 : G.Adj v (t 0))
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h4v : G.Adj (t 4) v) : IsHexagon G (neighborPathHexagon v t) := by
  exact ⟨neighborPathHexagon_injective v t ht htv, hv0, h01, h12, h23, h34, h4v⟩

theorem rainbow_five_path_colors_injective
    (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (t : Fin 5 → V) (ht : Function.Injective t) (htv : ∀ i, t i ≠ v)
    (hv0 : G.Adj v (t 0))
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h4v : G.Adj (t 4) v) :
    Function.Injective (fun i => c ⟨t i, htv i⟩) := by
  let f := neighborPathHexagon v t
  have hf : IsHexagon G f := neighborPathHexagon_isHexagon v t ht htv hv0 h01 h12 h23 h34 h4v
  let p := hexagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hp : p.IsCycle := hexagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hmem : ∀ i, t i ∈ p.support := by
    intro i
    change t i ∈ [v, t 0, t 1, t 2, t 3, t 4, v]
    fin_cases i <;> simp
  intro i j hij
  apply ht
  exact congrArg Subtype.val
    (hr v c p hp (by rfl) ⟨t i, htv i⟩ ⟨t j, htv j⟩ (hmem i) (hmem j) hij)

end TaskH.Six

#print axioms TaskH.Six.neighborPathHexagon
#print axioms TaskH.Six.neighborPathHexagon_injective
#print axioms TaskH.Six.neighborPathHexagon_isHexagon
#print axioms TaskH.Six.rainbow_five_path_colors_injective
