import Research.TaskH.Seven.SevenBPEighteenHookClasses

/-! Actual three-hook vertices have exactly one displayed C18 attachment type.
The finite classification concerns three positions on the nine-cycle only. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def EighteenHookClassAdj (i j : Fin 9) : Prop :=
  j=i+1 ∨ i=j+1 ∨ j=i+4 ∨ i=j+4

theorem eighteen_hook_class_adj_symm (i j : Fin 9) :
    EighteenHookClassAdj i j → EighteenHookClassAdj j i := by
  have tab : ∀ i j : Fin 9, EighteenHookClassAdj i j → EighteenHookClassAdj j i := by
    unfold EighteenHookClassAdj
    decide +kernel
  exact tab i j

theorem eighteen_actual_hook_class_pair (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (z : V) (hz : z ∉ Set.range u)
    (q : Fin 2) (i j : Fin 9) (hne : i≠j)
    (hi : i ∈ eighteenClassHooks G u z q) (hj : j ∈ eighteenClassHooks G u z q) :
    EighteenHookClassAdj i j := by
  let p := cycleEighteenWalk G u hu.2
  have hp := cycleEighteenWalk_shortest hb h14 h16 u hu
  have hzout : z ∉ p.support := fun h => hz ((cycleEighteenWalk_support_range G u hu.2 z).mp h)
  have hforward : ∀ (i j : Fin 9), i≠j →
      i ∈ eighteenClassHooks G u z q → j ∈ eighteenClassHooks G u z q →
      (eighteenClassIndex q i).val ≤ (eighteenClassIndex q j).val →
      EighteenHookClassAdj i j := by
    intro i j hne hi hj hord
    let ai := eighteenClassIndex q i
    let aj := eighteenClassIndex q j
    have hia : G.Adj (p.getVert ai.val) z := by
      have hget : p.getVert ai.val = u ai := cycleEighteenWalk_getVert G u hu.2 ai
      rw [hget]
      exact (Finset.mem_filter.mp hi).2.symm
    have hja : G.Adj (p.getVert aj.val) z := by
      have hget : p.getVert aj.val = u aj := cycleEighteenWalk_getVert G u hu.2 aj
      rw [hget]
      exact (Finset.mem_filter.mp hj).2.symm
    have hival : ai.val≠aj.val := by
      intro he
      exact hne (eighteenClassIndex_injective q (Fin.ext he))
    have hmod : ai.val%2=aj.val%2 := by
      have tab : ∀ q : Fin 2, ∀ i j : Fin 9,
          (eighteenClassIndex q i).val%2=(eighteenClassIndex q j).val%2 := by decide +kernel
      exact tab q i j
    have hiLt : ai.val<18 := ai.isLt
    have hjLt : aj.val<18 := aj.isLt
    have hlen : p.length=18 := rfl
    have hdelta : aj.val-ai.val=2 ∨ aj.val-ai.val=8 ∨ aj.val-ai.val=10 ∨ aj.val-ai.val=16 := by
      by_cases h2 : aj.val-ai.val=2
      · exact Or.inl h2
      · by_cases h16 : aj.val-ai.val=16
        · exact Or.inr (Or.inr (Or.inr h16))
        · have hh := shortest_cycle_external_pair_distances hb p hp hzout ai.val aj.val hord
            (by omega) (by omega) (by omega) hia hja
          have hcase : aj.val-ai.val=8 ∨ aj.val-ai.val=10 := by omega
          rcases hcase with he | he
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr (Or.inl he))
    have tab : ∀ q : Fin 2, ∀ i j : Fin 9,
        (eighteenClassIndex q j).val-(eighteenClassIndex q i).val=2 ∨
        (eighteenClassIndex q j).val-(eighteenClassIndex q i).val=8 ∨
        (eighteenClassIndex q j).val-(eighteenClassIndex q i).val=10 ∨
        (eighteenClassIndex q j).val-(eighteenClassIndex q i).val=16 → EighteenHookClassAdj i j := by
      unfold EighteenHookClassAdj
      decide +kernel
    exact tab q i j hdelta
  rcases le_total (eighteenClassIndex q i).val (eighteenClassIndex q j).val with hij | hji
  · exact hforward i j hne hi hj hij
  · exact eighteen_hook_class_adj_symm j i (hforward j i hne.symm hj hi hji)

def eighteenTripleIndices (i : Fin 9) : Finset (Fin 9) := {i,i+1,i+5}

theorem three_position_hook_classification (A : Finset (Fin 9)) (hc : A.card=3)
    (hpair : ∀ i∈A,∀ j∈A,i≠j → EighteenHookClassAdj i j) :
    ∃ i : Fin 9, A=eighteenTripleIndices i := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hc
  have hpab := hpair a (by simp) b (by simp) hab
  have hpac := hpair a (by simp) c (by simp) hac
  have hpbc := hpair b (by simp) c (by simp) hbc
  have tab : ∀ a b c : Fin 9, a≠b → a≠c → b≠c →
      EighteenHookClassAdj a b → EighteenHookClassAdj a c → EighteenHookClassAdj b c →
      ∃ i : Fin 9, ({a,b,c} : Finset (Fin 9))=eighteenTripleIndices i := by
    unfold EighteenHookClassAdj eighteenTripleIndices
    decide +kernel
  exact tab a b c hab hac hbc hpab hpac hpbc

theorem eighteenTripleIndices_injective : Function.Injective eighteenTripleIndices := by
  have tab : ∀ i j : Fin 9, eighteenTripleIndices i=eighteenTripleIndices j → i=j := by
    unfold eighteenTripleIndices
    decide +kernel
  exact fun i j he => tab i j he

theorem eighteen_actual_class_triple (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (z : V) (hz : z ∉ Set.range u)
    (q : Fin 2) (hc : (eighteenClassHooks G u z q).card=3) :
    ∃ i : Fin 9, eighteenClassHooks G u z q=eighteenTripleIndices i := by
  apply three_position_hook_classification _ hc
  intro i hi j hj hne
  exact eighteen_actual_hook_class_pair hb h14 h16 u hu z hz q i j hne hi hj

theorem eighteen_actual_triple_classification (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (z : V) (hz : z ∉ Set.range u)
    (hc : (eighteenOutsideHooks G u z).card=3) :
    ∃ (q : Fin 2) (i : Fin 9), eighteenOutsideHooks G u z =
      {eighteenClassIndex q i,eighteenClassIndex q (i+1),eighteenClassIndex q (i+5)} := by
  have hnon : (eighteenOutsideHooks G u z).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := eighteen_hook_class_image hb u hu z hnon
  have hcard : (eighteenClassHooks G u z q).card=3 := by
    rw [hq,Finset.card_image_of_injective _ (eighteenClassIndex_injective q)] at hc
    exact hc
  obtain ⟨i,hi⟩ := eighteen_actual_class_triple hb h14 h16 u hu z hz q hcard
  refine ⟨q,i,?_⟩
  rw [hq,hi,eighteenTripleIndices]
  simp only [Finset.image_insert,Finset.image_singleton]

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.EighteenHookClassAdj
#print axioms TaskH.Seven.BP.eighteen_hook_class_adj_symm
#print axioms TaskH.Seven.BP.eighteen_actual_hook_class_pair
#print axioms TaskH.Seven.BP.eighteenTripleIndices
#print axioms TaskH.Seven.BP.three_position_hook_classification
#print axioms TaskH.Seven.BP.eighteenTripleIndices_injective
#print axioms TaskH.Seven.BP.eighteen_actual_class_triple
#print axioms TaskH.Seven.BP.eighteen_actual_triple_classification
