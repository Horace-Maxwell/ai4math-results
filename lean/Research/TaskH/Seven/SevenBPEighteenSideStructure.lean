import Research.TaskH.Seven.SevenBPEighteenSideAttachments

/-! Actual outside-side partition, order31 budget, and four genuine low
neighbors forced on the opposite outside side by a triple vertex. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

noncomputable def eighteenSideLow [Fintype V] (c : G.Coloring Bool) (u : Fin 18 → V) (q : Fin 2) : Finset V :=
  (eighteenOutsideSide c u q).filter (fun z=>(eighteenOutsideHooks G u z).card≤1)
noncomputable def eighteenSideTriple [Fintype V] (c : G.Coloring Bool) (u : Fin 18 → V) (q : Fin 2) : Finset V :=
  (eighteenOutsideSide c u q).filter (fun z=>(eighteenOutsideHooks G u z).card=3)

theorem eighteen_side_not_range [Fintype V] (c : G.Coloring Bool) (u : Fin 18 → V)
    (q : Fin 2) (z : V) (hz : z∈eighteenOutsideSide c u q) : z∉Set.range u := by
  rintro ⟨i,hi⟩
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)

theorem eighteen_outside_side_union [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    eighteenOutsideSide c u 0 ∪ eighteenOutsideSide c u 1=Finset.univ \ Finset.univ.image u := by
  have hne := eighteen_class_colors_ne u hu c 0 1 (by decide) 0 0
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1
  · intro hz
    by_cases h0 : c z≠c (u (eighteenClassIndex 0 0))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h0⟩)
    · have he : c z=c (u (eighteenClassIndex 0 0)) := not_ne_iff.mp h0
      have h1 : c z≠c (u (eighteenClassIndex 1 0)) := by
        intro hh
        exact hne (he.symm.trans hh)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h1⟩)

theorem eighteen_outside_sides_disjoint [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    Disjoint (eighteenOutsideSide c u 0) (eighteenOutsideSide c u 1) := by
  apply Finset.disjoint_left.mpr
  intro z hz0 hz1
  have h0 := (Finset.mem_filter.mp hz0).2
  have h1 := (Finset.mem_filter.mp hz1).2
  have hne := eighteen_class_colors_ne u hu c 0 1 (by decide) 0 0
  cases hz : c z <;> cases hx : c (u (eighteenClassIndex 0 0)) <;>
    cases hy : c (u (eighteenClassIndex 1 0)) <;> simp_all

theorem eighteen_outside_sides_card [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    (eighteenOutsideSide c u 0).card+(eighteenOutsideSide c u 1).card=Fintype.card V-18 := by
  have hS : (Finset.univ.image u).card=18 := by
    rw [Finset.card_image_of_injective _ hu.1,Finset.card_univ,Fintype.card_fin]
  have hh := Finset.card_union_of_disjoint (eighteen_outside_sides_disjoint c u hu)
  rw [eighteen_outside_side_union c u hu] at hh
  simpa only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hS] using hh.symm

theorem eighteen_outside_sides_card_le_thirty_one [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (hn : Fintype.card V≤49) :
    (eighteenOutsideSide c u 0).card+(eighteenOutsideSide c u 1).card≤31 := by
  have hh := eighteen_outside_sides_card c u hu
  omega

theorem eighteen_outside_neighbor_opposite_side [Fintype V] (c : G.Coloring Bool)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) (a b : V)
    (ha : a∉Set.range u) (hb : b∈eighteenOutsideSide c u q) (hba : G.Adj b a) :
    a∈eighteenOutsideSide c u (q+1) := by
  have hqr : q≠q+1 := by
    have tab : ∀ q : Fin 2,q≠q+1 := by decide +kernel
    exact tab q
  have hne := eighteen_class_colors_ne u hu c q (q+1) hqr 0 0
  have hbq := (Finset.mem_filter.mp hb).2
  have hbeq : c b=c (u (eighteenClassIndex (q+1) 0)) := by
    cases h0 : c b <;> cases h1 : c (u (eighteenClassIndex q 0)) <;>
      cases h2 : c (u (eighteenClassIndex (q+1) 0)) <;> simp_all
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    exact ha ⟨i,hi⟩
  · intro he
    exact c.valid hba (hbeq.trans he.symm)

theorem eighteen_triple_forces_four_opposite_low [Fintype V]
    (hb : G.IsBipartite) (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (hd : ∀ x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) (b : V) (hbq : b∈eighteenSideTriple c u q) :
    4≤(eighteenSideLow c u (q+1)).card := by
  have hbs := (Finset.mem_filter.mp hbq).1
  have hb3 := (Finset.mem_filter.mp hbq).2
  have hbout := eighteen_side_not_range c u q b hbs
  have hdegree := eighteen_outside_degree_ge_four hb h14 h16 u hu b hbout (hd b)
  have hs : G.neighborFinset b \ Finset.univ.image u ⊆ eighteenSideLow c u (q+1) := by
    intro a ha
    have hba := (G.mem_neighborFinset b a).mp (Finset.mem_sdiff.mp ha).1
    have haout : a∉Set.range u := by
      rintro ⟨i,hi⟩
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
    have haside := eighteen_outside_neighbor_opposite_side c u hu q a b haout hbs hba
    have halow := eighteen_neighbor_of_triple_is_low hb h14 h16 u hu a b haout hbout hba hb3
    exact Finset.mem_filter.mpr ⟨haside,halow⟩
  exact le_trans hdegree (Finset.card_le_card hs)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteenSideLow
#print axioms TaskH.Seven.BP.eighteenSideTriple
#print axioms TaskH.Seven.BP.eighteen_side_not_range
#print axioms TaskH.Seven.BP.eighteen_outside_side_union
#print axioms TaskH.Seven.BP.eighteen_outside_sides_disjoint
#print axioms TaskH.Seven.BP.eighteen_outside_sides_card
#print axioms TaskH.Seven.BP.eighteen_outside_sides_card_le_thirty_one
#print axioms TaskH.Seven.BP.eighteen_outside_neighbor_opposite_side
#print axioms TaskH.Seven.BP.eighteen_triple_forces_four_opposite_low
