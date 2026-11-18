import Research.TaskH.Gao.BicliqueLexicographicSelection
import Research.TaskH.Gao.Challenge

/-! Two genuine x-a paths are constructed from the same original nonroot w
and its actual two Q-neighbors. No short-path family is supplied as input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem casebi_hub_nonroot_two_neighbors_short_family [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y a w : V)
    (hmax : CasebiLexMax G x y A B) (hB : B = {x, a}) (hxa : x ≠ a)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hw : w ∉ (A ∪ B) ∪ {y})
    (hhigh : 2 ≤ (G.neighborSet w ∩ (A ∪ B)).ncard) :
    (G.neighborSet w ∩ (A ∪ B)).ncard = 2 ∧
      ∃ (d : ℕ) (P : Fin 2 → G.Walk x a),
        AdmissiblePathFamily G x a 2 2 d P ∧
        ∀ i z, z ∈ (P i).support → z ∈ A ∪ B ∨ z = w := by
  classical
  have hB2 : B.ncard = 2 := by rw [hB, Set.ncard_pair hxa]
  have hcap := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad w hw
  have htwo : (G.neighborSet w ∩ (A ∪ B)).ncard = 2 := by omega
  have hcapB := casebi_lexmax_second_neighbor_cap G x y A B hmax w hw
  have hAne : ∃ u ∈ A, G.Adj w u := by
    by_contra hn
    have heq : G.neighborSet w ∩ (A ∪ B) = G.neighborSet w ∩ B := by
      ext z
      constructor
      · rintro ⟨ewz, hzA | hzB⟩
        · exact False.elim (hn ⟨z, hzA, ewz⟩)
        · exact ⟨ewz, hzB⟩
      · rintro ⟨ewz, hzB⟩; exact ⟨ewz, Or.inr hzB⟩
    rw [heq] at hhigh
    omega
  obtain ⟨u, huA, ewu⟩ := hAne
  have hxB : x ∈ B := hmax.1.2.2.1
  have haB : a ∈ B := by rw [hB]; exact Or.inr rfl
  have hwy : w ≠ y := fun he => hw (Or.inr he)
  have huy : u ≠ y := fun he => hmax.1.2.2.2.1
    (Or.inl (Eq.mp (congrArg (fun z : V => z ∈ A) he) huA))
  have hwQ : w ∉ A ∪ B := fun hh => hw (Or.inl hh)
  have hnx : ¬G.Adj w x := by
    intro ewx
    exact htri u w huy hwy (hmax.1.2.1 u huA x hxB).symm ewu.symm ewx
  obtain ⟨v, hvN, hvu⟩ := Set.exists_ne_of_one_lt_ncard
    (by omega : 1 < (G.neighborSet w ∩ (A ∪ B)).ncard) u
  have hxu : x ≠ u := fun he => Set.disjoint_left.mp hmax.1.1 huA
    (Eq.mp (congrArg (fun z : V => z ∈ B) he) hxB)
  have hua : u ≠ a := fun he => Set.disjoint_left.mp hmax.1.1 huA
    (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB)
  have hxw : x ≠ w := fun he => hwQ
    (Or.inr (Eq.mp (congrArg (fun z : V => z ∈ B) he) hxB))
  have huw : u ≠ w := fun he => hwQ
    (Or.inl (Eq.mp (congrArg (fun z : V => z ∈ A) he) huA))
  have hwa : w ≠ a := fun he => hwQ
    (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB))
  let p0 : G.Walk x a := Walk.cons (hmax.1.2.1 u huA x hxB).symm
    (hmax.1.2.1 u huA a haB).toWalk
  have hp0 : p0.IsPath := by
    apply Walk.IsPath.mk'
    change [x, u, a].Nodup
    simp [hxu, hxa, hua]
  rcases hvN.2 with hvA | hvB
  · have hxv : x ≠ v := fun he => Set.disjoint_left.mp hmax.1.1 hvA
      (Eq.mp (congrArg (fun z : V => z ∈ B) he) hxB)
    have hva : v ≠ a := fun he => Set.disjoint_left.mp hmax.1.1 hvA
      (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB)
    have hwv : w ≠ v := fun he => hwQ
      (Or.inl (Eq.mpr (congrArg (fun z : V => z ∈ A) he) hvA))
    let p1 : G.Walk x a := Walk.cons (hmax.1.2.1 u huA x hxB).symm
      (Walk.cons ewu.symm (Walk.cons hvN.1 (hmax.1.2.1 v hvA a haB).toWalk))
    have hp1 : p1.IsPath := by
      apply Walk.IsPath.mk'
      change [x, u, w, v, a].Nodup
      simp [hxu, hxw, hxv, hxa, huw, hvu.symm, hua, hwv, hwa, hva]
    let P : Fin 2 → G.Walk x a := fun i => if i.val = 0 then p0 else p1
    refine ⟨htwo, 2, P, ⟨by omega, Or.inr rfl, ?_⟩, ?_⟩
    · intro i; fin_cases i
      · exact ⟨hp0, rfl⟩
      · exact ⟨hp1, rfl⟩
    · intro i z hz; fin_cases i
      · change z ∈ [x, u, a] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact Or.inl (Or.inr hxB)
        · exact Or.inl (Or.inl huA)
        · exact Or.inl (Or.inr haB)
      · change z ∈ [x, u, w, v, a] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inr hxB)
        · exact Or.inl (Or.inl huA)
        · exact Or.inr rfl
        · exact Or.inl (Or.inl hvA)
        · exact Or.inl (Or.inr haB)
  · have hv : v = x ∨ v = a :=
      Eq.mp (congrArg (fun Q : Set V => v ∈ Q) hB) hvB
    rcases hv with hvx | hva
    · exact False.elim (hnx (Eq.mp (congrArg (fun v : V => G.Adj w v) hvx) hvN.1))
    · subst v
      let p1 : G.Walk x a := Walk.cons (hmax.1.2.1 u huA x hxB).symm
        (Walk.cons ewu.symm hvN.1.toWalk)
      have hp1 : p1.IsPath := by
        apply Walk.IsPath.mk'
        change [x, u, w, a].Nodup
        simp [hxu, hxw, hxa, huw, hua, hwa]
      let P : Fin 2 → G.Walk x a := fun i => if i.val = 0 then p0 else p1
      refine ⟨htwo, 1, P, ⟨by omega, Or.inl rfl, ?_⟩, ?_⟩
      · intro i; fin_cases i
        · exact ⟨hp0, rfl⟩
        · exact ⟨hp1, rfl⟩
      · intro i z hz; fin_cases i
        · change z ∈ [x, u, a] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact Or.inl (Or.inr hxB)
          · exact Or.inl (Or.inl huA)
          · exact Or.inl (Or.inr haB)
        · change z ∈ [x, u, w, a] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact Or.inl (Or.inr hxB)
          · exact Or.inl (Or.inl huA)
          · exact Or.inr rfl
          · exact Or.inl (Or.inr haB)

#print axioms casebi_hub_nonroot_two_neighbors_short_family
end TaskH.Gao
