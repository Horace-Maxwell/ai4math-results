import Research.TaskH.Five.FivePatternForcedColors

/-! A shared external neighbor would close a genuine non-rainbow five-cycle. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem forced_group_common_neighbors_unique
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn : 9 ≤ Fintype.card V) (f : Fin 5 → V) (a : Fin 5) (Z : Finset V)
    (hforce : ∀ x ∈ Z, ForcedTo G f a x)
    (hcross : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y) :
    ∀ z ∈ (patternVertexSet f)ᶜ, ∀ x ∈ Z, ∀ y ∈ Z,
      G.Adj x z → G.Adj y z → x = y := by
  classical
  intro z hz x hx y hy hxz hyz
  by_contra hne
  have hind := forced_group_independent hcrit hn f a Z hforce
  have hnot : ¬ G.Adj x y := hind x hx y hy
  obtain ⟨i, j, hxi, hij, hjy⟩ := hcross x hx y hy hne
  have hxfi : x ≠ f i := hxi.ne
  have hxfj : x ≠ f j := by
    intro he
    apply hnot
    simpa only [he] using hjy
  have hfiy : f i ≠ y := by
    intro he
    apply hnot
    simpa only [he] using hxi
  have hznS : z ∉ patternVertexSet f := Finset.mem_compl.mp hz
  have hfiz : f i ≠ z := by
    intro he
    apply hznS
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hfjz : f j ≠ z := by
    intro he
    apply hznS
    rw [← he]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hnodup : ([x, f i, f j, y, z] : List V).Nodup := by
    simp [hxfi, hxfj, hne, hxz.ne, hij.ne, hfiy, hfiz, hjy.ne, hfjz, hyz.ne]
  let g : Fin 5 → V := ![x, f i, f j, y, z]
  have hginj : Function.Injective g := by
    have he : g = ([x, f i, f j, y, z] : List V).get := by
      funext k
      fin_cases k <;> rfl
    rw [he]
    exact List.nodup_iff_injective_get.mp hnodup
  let p := pentagonWalk G g hxi hij hjy hyz hxz.symm
  have hp : p.IsCycle := pentagonWalk_isCycle G g hginj hxi hij hjy hyz hxz.symm
  obtain ⟨w, hwS, hwT⟩ := exists_deletedVertex_away hn f {x, y, z} Finset.card_le_three
  have hfw : ∀ k, f k ≠ w := by
    intro k he
    apply hwS
    rw [← he]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hxw : x ≠ w := by
    intro he
    apply hwT
    simp [← he]
  have hyw : y ≠ w := by
    intro he
    apply hwT
    simp [← he]
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hxcol := hforce x hx w c hfw hxw
  have hycol := hforce y hy w c hfw hyw
  have hyin : y ∈ p.support := by simp [p, pentagonWalk, g, Walk.support_cons]
  have he := hr w c p hp (by rfl) ⟨x, hxw⟩ ⟨y, hyw⟩ p.start_mem_support hyin
    (hxcol.trans hycol.symm)
  exact hne (congrArg Subtype.val he)

end TaskH.Five

#print axioms TaskH.Five.forced_group_common_neighbors_unique
