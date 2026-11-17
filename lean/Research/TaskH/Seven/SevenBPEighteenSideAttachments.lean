import Research.TaskH.Seven.SevenBPEighteenClassBoundary

/-! The actual outside sides and their attachment sums. The lower bound36
is transported from the nine actual cycle vertices by a true relation count. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem eighteen_class_colors_eq (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (q : Fin 2) (i j : Fin 9) :
    c (u (eighteenClassIndex q i))=c (u (eighteenClassIndex q j)) := by
  have hcases : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide +kernel
  rcases hcases q with hq | hq
  · subst q
    rw [eighteen_class_zero_color u hu c i,eighteen_class_zero_color u hu c j]
  · subst q
    have hi := eighteen_class_one_color_ne u hu c i
    have hj := eighteen_class_one_color_ne u hu c j
    cases h0 : c (u 0) <;> cases h1 : c (u (eighteenClassIndex 1 i)) <;>
      cases h2 : c (u (eighteenClassIndex 1 j)) <;> simp_all

theorem eighteen_class_colors_ne (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (q r : Fin 2) (hqr : q≠r) (i j : Fin 9) :
    c (u (eighteenClassIndex q i))≠c (u (eighteenClassIndex r j)) := by
  have hcases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hcases q with hq | hq <;> rcases hcases r with hr | hr <;>
    subst q <;> subst r
  · exact (hqr rfl).elim
  · rw [eighteen_class_zero_color u hu c i]
    exact (eighteen_class_one_color_ne u hu c j).symm
  · rw [eighteen_class_zero_color u hu c j]
    exact eighteen_class_one_color_ne u hu c i
  · exact (hqr rfl).elim

noncomputable def eighteenOutsideSide [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (q : Fin 2) : Finset V :=
  (Finset.univ \ Finset.univ.image u).filter
    (fun z => c z≠c (u (eighteenClassIndex q 0)))

theorem eighteen_outside_neighbor_in_side [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) (i : Fin 9) (z : V)
    (hz : z∉Finset.univ.image u) (ha : G.Adj (u (eighteenClassIndex q i)) z) :
    z∈eighteenOutsideSide c u q := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩,?_⟩
  intro he
  apply c.valid ha
  exact (eighteen_class_colors_eq u hu c q i 0).trans he.symm

theorem eighteen_side_hook_image [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) (z : V)
    (hz : z∈eighteenOutsideSide c u q) :
    eighteenOutsideHooks G u z=(eighteenClassHooks G u z q).image (eighteenClassIndex q) := by
  ext j
  constructor
  · intro hj
    let e : Fin 9 × Fin 2 ≃ Fin (9 * 2) := finProdFinEquiv
    let p : Fin 9 × Fin 2 := e.symm j
    have hp : eighteenClassIndex p.2 p.1=j := by
      change e (e.symm j) = j
      exact e.apply_symm_apply j
    have hrq : p.2=q := by
      by_contra hne
      have hcn := eighteen_class_colors_ne u hu c p.2 q hne p.1 0
      have hzn : c z≠c (u (eighteenClassIndex p.2 p.1)) := by
        apply c.valid
        simpa only [hp] using (Finset.mem_filter.mp hj).2
      have hzq := (Finset.mem_filter.mp hz).2
      cases hz' : c z <;> cases hr' : c (u (eighteenClassIndex p.2 p.1)) <;>
        cases hq' : c (u (eighteenClassIndex q 0)) <;> simp_all
    have he : eighteenClassIndex q p.1=j := by simpa only [hrq] using hp
    exact Finset.mem_image.mpr ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa only [he] using (Finset.mem_filter.mp hj).2⟩,he⟩
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

theorem eighteen_side_hook_card [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) (z : V)
    (hz : z∈eighteenOutsideSide c u q) :
    (eighteenOutsideHooks G u z).card=(eighteenClassHooks G u z q).card := by
  rw [eighteen_side_hook_image c u hu q z hz,
    Finset.card_image_of_injective _ (eighteenClassIndex_injective q)]

theorem eighteen_outside_side_attachment_count [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) :
    (∑ i : Fin 9,(G.neighborFinset (u (eighteenClassIndex q i)) \ Finset.univ.image u).card)=
      ∑ z∈eighteenOutsideSide c u q,(eighteenOutsideHooks G u z).card := by
  let S := eighteenOutsideSide c u q
  let R : Fin 9 → V → Prop := fun i z => G.Adj (u (eighteenClassIndex q i)) z
  have hrow (i : Fin 9) : S.filter (R i)=
      G.neighborFinset (u (eighteenClassIndex q i)) \ Finset.univ.image u := by
    ext z
    constructor
    · intro hz
      have hzs := (Finset.mem_filter.mp hz).1
      have ha := (Finset.mem_filter.mp hz).2
      exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ha,
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzs).1).2⟩
    · intro hz
      have ha := (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1
      have hzs := eighteen_outside_neighbor_in_side c u hu q i z (Finset.mem_sdiff.mp hz).2 ha
      exact Finset.mem_filter.mpr ⟨hzs,ha⟩
  have hcol (z : V) : (Finset.univ : Finset (Fin 9)).filter (fun i => R i z)=
      eighteenClassHooks G u z q := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,eighteenClassHooks]
    exact ⟨fun h=>h.symm,fun h=>h.symm⟩
  calc
    _ = ∑ i : Fin 9,(S.filter (R i)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow]
    _ = ∑ z∈S,((Finset.univ : Finset (Fin 9)).filter (fun i=>R i z)).card :=
      FiniteBudget.relation_double_count Finset.univ S R
    _ = ∑ z∈S,(eighteenOutsideHooks G u z).card := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hcol,←eighteen_side_hook_card c u hu q z hz]

theorem eighteen_each_side_attachments_ge_thirty_six [Fintype V]
    (hb : G.IsBipartite) (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (hd : ∀ x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) :
    36 ≤ ∑ z∈eighteenOutsideSide c u q,(eighteenOutsideHooks G u z).card := by
  have hh := eighteen_cycle_class_external_edges_ge_thirty_six hb h14 h16 u hu hd q
  rw [eighteen_outside_side_attachment_count c u hu q] at hh
  exact hh

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteen_class_colors_eq
#print axioms TaskH.Seven.BP.eighteen_class_colors_ne
#print axioms TaskH.Seven.BP.eighteenOutsideSide
#print axioms TaskH.Seven.BP.eighteen_outside_neighbor_in_side
#print axioms TaskH.Seven.BP.eighteen_side_hook_image
#print axioms TaskH.Seven.BP.eighteen_side_hook_card
#print axioms TaskH.Seven.BP.eighteen_outside_side_attachment_count
#print axioms TaskH.Seven.BP.eighteen_each_side_attachments_ge_thirty_six
