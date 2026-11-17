import Research.TaskH.Seven.SevenDegreeTwelveGeometry

/-! The k7 rule is an actual five-edge path closed by the deleted root.
A four-edge path would close to length six and is not used. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

def rootedFivePathHeptagon (v : V) (t : Fin 6 → V) : Fin 7 → V :=
  ![v, t 0, t 1, t 2, t 3, t 4, t 5]

theorem rootedFivePathHeptagon_injective (v : V) (t : Fin 6 → V)
    (ht : Function.Injective t) (hv : ∀ i, t i ≠ v) :
    Function.Injective (rootedFivePathHeptagon v t) := by
  have hv' : ∀ i, v ≠ t i := fun i => Ne.symm (hv i)
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [rootedFivePathHeptagon, ht.eq_iff]

theorem rooted_five_path_colors_injective (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (t : Fin 6 → V)
    (ht : Function.Injective t) (hv : ∀ i, t i ≠ v)
    (hstart : G.Adj v (t 0)) (hend : G.Adj v (t 5))
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h45 : G.Adj (t 4) (t 5)) :
    Function.Injective (fun i : Fin 6 => c ⟨t i, hv i⟩) := by
  let f := rootedFivePathHeptagon v t
  have hf : IsHeptagon G f :=
    ⟨rootedFivePathHeptagon_injective v t ht hv, hstart, h01, h12, h23, h34, h45, hend.symm⟩
  let p := heptagonWalk G f hstart h01 h12 h23 h34 h45 hend.symm
  have hp : p.IsCycle := heptagonWalk_isCycle G f hf.1 hstart h01 h12 h23 h34 h45 hend.symm
  have hm : ∀ i : Fin 6, t i ∈ p.support := by
    intro i
    change t i ∈ [v, t 0, t 1, t 2, t 3, t 4, t 5, v]
    fin_cases i <;> simp
  intro i j he
  apply ht
  exact congrArg Subtype.val (hr v c p hp (by rfl) ⟨t i, hv i⟩ ⟨t j, hv j⟩
    (hm i) (hm j) he)

theorem rooted_five_path_same_color_false (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (t : Fin 6 → V)
    (ht : Function.Injective t) (hv : ∀ i, t i ≠ v)
    (hstart : G.Adj v (t 0)) (hend : G.Adj v (t 5))
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h45 : G.Adj (t 4) (t 5))
    (i j : Fin 6) (hij : i ≠ j) (hcolor : c ⟨t i, hv i⟩ = c ⟨t j, hv j⟩) : False :=
  hij (rooted_five_path_colors_injective hr v c t ht hv hstart hend
    h01 h12 h23 h34 h45 hcolor)


theorem neighbor_five_path_same_color_false
    (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (t : Fin 6 → G.neighborSet v) (ht : Function.Injective t)
    (h01 : G.Adj (t 0).val (t 1).val) (h12 : G.Adj (t 1).val (t 2).val)
    (h23 : G.Adj (t 2).val (t 3).val) (h34 : G.Adj (t 3).val (t 4).val)
    (h45 : G.Adj (t 4).val (t 5).val)
    (i j : Fin 6) (hij : i ≠ j)
    (hcolor : neighborColor v c (t i) = neighborColor v c (t j)) : False := by
  have htv : Function.Injective (fun k => (t k).val) := by
    intro k l he
    exact ht (Subtype.ext he)
  exact rooted_five_path_same_color_false hr v c (fun k => (t k).val) htv
    (fun k => (t k).property.ne.symm) (t 0).property (t 5).property
    h01 h12 h23 h34 h45 i j hij hcolor

end TaskH.Seven
#print axioms TaskH.Seven.rootedFivePathHeptagon
#print axioms TaskH.Seven.rootedFivePathHeptagon_injective
#print axioms TaskH.Seven.rooted_five_path_colors_injective
#print axioms TaskH.Seven.rooted_five_path_same_color_false

#print axioms TaskH.Seven.neighbor_five_path_same_color_false
