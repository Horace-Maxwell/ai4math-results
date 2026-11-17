import Research.TaskH.Seven.SevenTwoColorFourPairs

/-! Strong actual singleton retention. Coloring the root by the old singleton
color and deleting its unique neighbor is a genuine proper coloring. Thus an
old same-colored point other than that neighbor is excluded from EVERY actual
seven-cycle through the root, even when the deleted singleton itself lies on
the cycle. This does not assume an outside-pool cover or a hub inequality. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem singleton_color_forbidden_on_root_circle (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c)) {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hl : p.length = 7) (hv : v ∈ p.support)
    (z : {x : V // x ≠ v}) (hz : z.val ∈ p.support)
    (hza : z.val ≠ (singletonNeighbor v c j).val) : c z ≠ j.val := by
  intro hcolor
  let d := singletonDeletedColoring v c j
  let vv : {x : V // x ≠ (singletonNeighbor v c j).val} :=
    ⟨v, (singletonNeighbor v c j).property.ne⟩
  let zz : {x : V // x ≠ (singletonNeighbor v c j).val} := ⟨z.val, hza⟩
  have hsame : d vv = d zz := by
    rw [singletonDeletedColoring_base, singletonDeletedColoring_outside v c j zz z.property]
    exact hcolor.symm
  have he := hr (singletonNeighbor v c j).val d p hp hl vv zz hv hz hsame
  exact z.property (congrArg Subtype.val he).symm

theorem singleton_color_forbidden_on_rooted_five_path
    (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c)) (t : Fin 6 → V)
    (ht : Function.Injective t) (htv : ∀ i, t i ≠ v)
    (hstart : G.Adj v (t 0)) (hend : G.Adj v (t 5))
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h45 : G.Adj (t 4) (t 5)) (i : Fin 6)
    (hia : t i ≠ (singletonNeighbor v c j).val) :
    c ⟨t i, htv i⟩ ≠ j.val := by
  let f := rootedFivePathHeptagon v t
  let p := heptagonWalk G f hstart h01 h12 h23 h34 h45 hend.symm
  have hp : p.IsCycle := heptagonWalk_isCycle G f
    (rootedFivePathHeptagon_injective v t ht htv) hstart h01 h12 h23 h34 h45 hend.symm
  have hvmem : v ∈ p.support := p.start_mem_support
  have hmem : t i ∈ p.support := by
    change t i ∈ [v, t 0, t 1, t 2, t 3, t 4, t 5, v]
    fin_cases i <;> simp
  exact singleton_color_forbidden_on_root_circle hr v c j p hp (by rfl) hvmem
    ⟨t i, htv i⟩ hmem hia

theorem equality_singleton_color_forbidden_on_root_circle
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c)) {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hl : p.length = 7) (hv : v ∈ p.support)
    (z : {x : V // x ≠ v}) (hz : z.val ∈ p.support)
    (hza : z.val ≠ (singletonNeighbor v c j).val) : c z ≠ j.val :=
  singleton_color_forbidden_on_root_circle (equality_rainbowSevenCycles hcrit hc)
    v c j p hp hl hv z hz hza

end TaskH.Seven
#print axioms TaskH.Seven.singleton_color_forbidden_on_root_circle
#print axioms TaskH.Seven.singleton_color_forbidden_on_rooted_five_path
#print axioms TaskH.Seven.equality_singleton_color_forbidden_on_root_circle
