import Research.TaskH.Seven.CycleSeven

/-!
R is transported to actual seven-vertex cycle certificates. The second and
third lemmas permit the deleted vertex to lie on the circle, as required by
the later singleton/pool contradictions.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem rainbow_heptagon_colors_injective
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (f : Fin 7 → V) (hf : IsHeptagon G f) (hfw : ∀ i, f i ≠ w) :
    Function.Injective (fun i => c ⟨f i, hfw i⟩) := by
  rcases hf with ⟨hfi, h01, h12, h23, h34, h45, h56, h60⟩
  let p := heptagonWalk G f h01 h12 h23 h34 h45 h56 h60
  have hp : p.IsCycle := heptagonWalk_isCycle G f hfi h01 h12 h23 h34 h45 h56 h60
  have hmem : ∀ i, f i ∈ p.support := by
    intro i
    change f i ∈ [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 0]
    fin_cases i <;> simp
  intro i j hij
  apply hfi
  exact congrArg Subtype.val
    (hr w c p hp (by rfl) ⟨f i, hfw i⟩ ⟨f j, hfw j⟩ (hmem i) (hmem j) hij)

theorem rainbow_heptagon_deleted_colors_ne
    (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (f : Fin 7 → V) (hf : IsHeptagon G f)
    (i j : Fin 7) (hiv : f i ≠ v) (hjv : f j ≠ v) (hij : i ≠ j) :
    c ⟨f i, hiv⟩ ≠ c ⟨f j, hjv⟩ := by
  rcases hf with ⟨hfi, h01, h12, h23, h34, h45, h56, h60⟩
  let p := heptagonWalk G f h01 h12 h23 h34 h45 h56 h60
  have hp : p.IsCycle := heptagonWalk_isCycle G f hfi h01 h12 h23 h34 h45 h56 h60
  have hmem : ∀ a, f a ∈ p.support := by
    intro a
    change f a ∈ [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 0]
    fin_cases a <;> simp
  intro hcolor
  have he := hr v c p hp (by rfl) ⟨f i, hiv⟩ ⟨f j, hjv⟩
    (hmem i) (hmem j) hcolor
  exact hij (hfi (congrArg Subtype.val he))

theorem rainbow_heptagon_same_color_impossible
    (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (f : Fin 7 → V) (hf : IsHeptagon G f)
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
  have hne := rainbow_heptagon_deleted_colors_ne hr v c f hf i j hiv hjv hij
  apply hne
  simpa only [hi, hj] using hcolor

end TaskH.Seven

#print axioms TaskH.Seven.rainbow_heptagon_colors_injective
#print axioms TaskH.Seven.rainbow_heptagon_deleted_colors_ne
#print axioms TaskH.Seven.rainbow_heptagon_same_color_impossible
