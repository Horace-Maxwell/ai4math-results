import Research.TaskH.Six.CycleSix

/-! Rainbow transport still applies when the deleted vertex lies on the hexagon. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem rainbow_hexagon_deleted_colors_ne
    (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (f : Fin 6 → V) (hf : IsHexagon G f)
    (i j : Fin 6) (hiv : f i ≠ v) (hjv : f j ≠ v) (hij : i ≠ j) :
    c ⟨f i, hiv⟩ ≠ c ⟨f j, hjv⟩ := by
  let p := hexagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hp : p.IsCycle := hexagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hmem : ∀ a, f a ∈ p.support := by
    intro a
    change f a ∈ [f 0, f 1, f 2, f 3, f 4, f 5, f 0]
    fin_cases a <;> simp
  intro hcolor
  have he := hr v c p hp (by rfl) ⟨f i, hiv⟩ ⟨f j, hjv⟩
    (hmem i) (hmem j) hcolor
  exact hij (hf.1 (congrArg Subtype.val he))

theorem rainbow_hexagon_same_color_impossible
    (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (f : Fin 6 → V) (hf : IsHexagon G f)
    (x y : V) (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y)
    (hxf : ∃ i, f i = x) (hyf : ∃ j, f j = y)
    (hcolor : c ⟨x, hxv⟩ = c ⟨y, hyv⟩) : False := by
  obtain ⟨i, hi⟩ := hxf
  obtain ⟨j, hj⟩ := hyf
  have hiv : f i ≠ v := by simpa only [hi] using hxv
  have hjv : f j ≠ v := by simpa only [hj] using hyv
  have hij : i ≠ j := by
    intro he
    apply hxy
    exact hi.symm.trans ((congrArg f he).trans hj)
  have hne := rainbow_hexagon_deleted_colors_ne hr v c f hf i j hiv hjv hij
  apply hne
  simpa only [hi, hj] using hcolor

end TaskH.Six

#print axioms TaskH.Six.rainbow_hexagon_deleted_colors_ne
#print axioms TaskH.Six.rainbow_hexagon_same_color_impossible
