import Research.TaskJ.Grid.GridAttainmentCases
import Research.TaskJ.Grid.GridCanonical
import Research.TaskJ.Grid.GridCore

namespace Grid.Attainment

open Challenge

theorem even_budget (k : ℕ) : evenCost k = Core.evenBudget k := by
  unfold evenCost Core.evenBudget
  ring

private theorem choose_core (k q base : ℕ) (hne : 0 < k+q)
    (hb : base=2 ∨ base=4) (hb4 : base=4 → k=1 ∧ q=1) :
    ∃ core, (List.replicate k base ++ List.replicate q 3).Perm core ∧
      Core.Witness core (coreCost k q base) := by
  cases k with
  | zero =>
    cases q with
    | zero => omega
    | succ n =>
      refine ⟨List.replicate (n+1) 3,by simp,?_⟩
      simpa [coreCost] using Core.odd n
  | succ e =>
    cases q with
    | zero =>
      have h2 : base=2 := hb.resolve_right (fun h => by have := (hb4 h).2; omega)
      subst base
      refine ⟨List.replicate (e+1) 2,by simp,?_⟩
      simpa [coreCost,even_budget] using Core.allEven e
    | succ q =>
      cases q with
      | zero =>
        cases e with
        | zero =>
          rcases hb with rfl | rfl
          · exact ⟨[2,3],List.Perm.refl _,Core.planeNarrow⟩
          · exact ⟨[4,3],List.Perm.refl _,Core.planeWide⟩
        | succ e =>
          have h2 : base=2 := hb.resolve_right (fun h => by have := (hb4 h).1; omega)
          subst base
          refine ⟨List.replicate e 2 ++ [2,2,3],?_,?_⟩
          · rw [List.replicate_succ' (n := e+1), List.replicate_succ' (n := e)]
            simp [List.append_assoc]
          · simpa [coreCost,even_budget] using Core.oneOdd e
      | succ o =>
        have h2 : base=2 := hb.resolve_right (fun h => by have := (hb4 h).2; omega)
        subst base
        refine ⟨_,Canonical.mixed_perm e o,?_⟩
        simpa [coreCost,even_budget] using Core.severalOdd e o

private theorem mass_perm {a b : List ℕ} (p : a.Perm b) : mass a = mass b := by
  simp only [mass,massAt,p.prod_eq]
  exact (p.map _).sum_eq

theorem normalized_attained (ds : List ℕ) (wide : ∀ d ∈ ds, 1<d) :
    ∃ p, Order ds p ∧ (pathLength p : ℤ) = optimumFormula ds := by
  by_cases hempty : ds = []
  · subst ds
    exact empty_order
  let k := evenCount ds
  let q := ds.length - k
  let b := Canonical.evenBase ds
  have hle : k ≤ ds.length := List.length_filter_le _ _
  have hkq : k+q = ds.length := by dsimp [q]; omega
  have hn : 0 < k+q := by rw [hkq]; exact List.length_pos_iff.mpr hempty
  have hfour : b=4 → k=1 ∧ q=1 := by
    intro hh
    dsimp [b,Canonical.evenBase] at hh
    split at hh
    · rename_i he
      exact ⟨he.2.1,by dsimp [q,k]; omega⟩
    · contradiction
  obtain ⟨core,perm,w⟩ := choose_core k q b hn (Canonical.evenBase_cases ds) hfour
  obtain ⟨pads,hwide,hinner,houter⟩ := Canonical.prepare ds core wide perm
  have hw : Core.Witness (Pad.inner pads) (coreCost k q b) := hinner ▸ w
  have hpos : PositiveSides (Pad.outer pads) := fun d hd => by
    have := wide d (houter.mem_iff.mp hd)
    omega
  obtain ⟨p,hp,hc⟩ := hw.inflate hwide hpos
  obtain ⟨f⟩ := Transport.of_perm houter
  obtain ⟨p',hp',hlen⟩ := f.transport_order hp
  rw [mass_perm houter] at hc
  have hf := normalized_cost wide b (by
    intro hl he
    simp only [b,Canonical.evenBase,hl,he,true_and]
    by_cases hw : ∀ d ∈ ds, d%2=0 → 4 ≤ d
    · rw [ite_eq_left hw]
      simp [(large_even_iff hl he).mp hw]
    · rw [ite_eq_right hw]
      simp [mt (large_even_iff hl he).mpr hw])
  exact ⟨p',hp',by rw [hlen]; exact from_cost hc hf⟩

end Grid.Attainment
