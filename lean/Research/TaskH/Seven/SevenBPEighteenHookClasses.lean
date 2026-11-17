import Research.TaskH.Seven.SevenBPEighteenCompatibility

/-! Actual C18 parity and the exact reduction of a nonempty outside hook set
to one of the two nine-position bipartition classes. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem cycle_eighteen_color_even_iff (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (i : Fin 18) : Even i.val ↔ (c (u 0) ↔ c (u i)) := by
  have hh := c.even_length_iff_congr ((cycleEighteenWalk G u hu.2).take i.val)
  simpa only [Walk.take_length,cycleEighteenWalk_length,
    inf_eq_left.mpr (Nat.le_of_lt i.isLt),cycleEighteenWalk_getVert] using hh

theorem eighteen_outside_hooks_same_parity (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (z : V) (i j : Fin 18)
    (hi : i ∈ eighteenOutsideHooks G u z) (hj : j ∈ eighteenOutsideHooks G u z) :
    i.val%2=j.val%2 := by
  have hi' := c.valid (Finset.mem_filter.mp hi).2
  have hj' := c.valid (Finset.mem_filter.mp hj).2
  have he : c (u i)=c (u j) := by
    cases h0 : c z <;> cases h1 : c (u i) <;> cases h2 : c (u j) <;> simp_all
  have hci := cycle_eighteen_color_even_iff u hu c i
  have hcj := cycle_eighteen_color_even_iff u hu c j
  rw [he] at hci
  have hpar : Even i.val ↔ Even j.val := hci.trans hcj.symm
  simp only [Nat.even_iff] at hpar
  omega

noncomputable def eighteenClassHooks (G : SimpleGraph V) (u : Fin 18 → V) (z : V) (q : Fin 2) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => G.Adj z (u (eighteenClassIndex q i)))

theorem eighteenClassIndex_injective (q : Fin 2) : Function.Injective (eighteenClassIndex q) := by
  intro i j he
  exact congrArg Prod.fst (finProdFinEquiv.injective he)

theorem eighteen_hook_class_image (hb : G.IsBipartite) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (z : V) (hk : (eighteenOutsideHooks G u z).Nonempty) :
    ∃ q : Fin 2, eighteenOutsideHooks G u z =
      (eighteenClassHooks G u z q).image (eighteenClassIndex q) := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  obtain ⟨k,hk⟩ := hk
  let q : Fin 2 := ⟨k.val%2,Nat.mod_lt _ (by decide)⟩
  refine ⟨q,?_⟩
  ext j
  constructor
  · intro hj
    have hpar : q.val=j.val%2 := eighteen_outside_hooks_same_parity u hu c z k j hk hj
    have tab : ∀ q : Fin 2, ∀ j : Fin 18, q.val=j.val%2 →
        ∃ i : Fin 9, eighteenClassIndex q i=j := by decide +kernel
    obtain ⟨i,hi⟩ := tab q j hpar
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hi⟩
    simpa only [hi] using (Finset.mem_filter.mp hj).2
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

theorem eighteen_class_zero_color (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (i : Fin 9) : c (u (eighteenClassIndex 0 i))=c (u 0) := by
  have hc := cycle_eighteen_color_even_iff u hu c (eighteenClassIndex 0 i)
  have hi : Even (eighteenClassIndex 0 i).val := by
    rw [Nat.even_iff]
    have tab : ∀ i : Fin 9, (eighteenClassIndex 0 i).val%2=0 := by decide +kernel
    exact tab i
  have hh := hc.mp hi
  cases h0 : c (u 0) <;> cases h1 : c (u (eighteenClassIndex 0 i)) <;> simp_all

theorem eighteen_class_one_color_ne (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (i : Fin 9) : c (u (eighteenClassIndex 1 i))≠c (u 0) := by
  have hc := cycle_eighteen_color_even_iff u hu c (eighteenClassIndex 1 i)
  have hi : ¬Even (eighteenClassIndex 1 i).val := by
    rw [Nat.even_iff]
    have tab : ∀ i : Fin 9, (eighteenClassIndex 1 i).val%2≠0 := by decide +kernel
    exact tab i
  intro he
  apply hi
  apply hc.mpr
  rw [he]

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.cycle_eighteen_color_even_iff
#print axioms TaskH.Seven.BP.eighteen_outside_hooks_same_parity
#print axioms TaskH.Seven.BP.eighteenClassHooks
#print axioms TaskH.Seven.BP.eighteenClassIndex_injective
#print axioms TaskH.Seven.BP.eighteen_hook_class_image
#print axioms TaskH.Seven.BP.eighteen_class_zero_color
#print axioms TaskH.Seven.BP.eighteen_class_one_color_ne
