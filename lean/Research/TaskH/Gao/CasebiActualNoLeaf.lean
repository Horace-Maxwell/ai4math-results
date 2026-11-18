import Research.TaskH.Gao.CasebiComponentPrefixes
import Research.TaskH.Gao.ComponentTerminalTail
import Research.TaskH.Gao.CliqueBoundaryBudget

/-! Original no-leaf argument on the actual component containing y, not a block oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_component_neighbor_partition [Finite V] (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) (d : C.supp) :
    (C.toSimpleGraph.neighborSet d).ncard + (G.neighborSet (componentVertex C d) ∩ Q).ncard =
      (G.neighborSet (componentVertex C d)).ncard := by
  let D := componentRegion C Set.univ
  have hdis : Disjoint D Q := componentRegion_disjoint C Set.univ
  have hcover : ∀ z, G.Adj (componentVertex C d) z → z ∈ D ∨ z ∈ Q := by
    intro z edz
    by_cases hz : z ∈ Q
    · exact Or.inr hz
    · have e : (G.induce Qᶜ).Adj d.1 ⟨z, hz⟩ := edz
      let zr : C.supp := ⟨⟨z, hz⟩, C.mem_supp_of_adj_mem_supp d.2 e⟩
      exact Or.inl ⟨zr, Set.mem_univ zr, rfl⟩
  have heq : (C.toSimpleGraph.neighborSet d).ncard =
      (G.neighborSet (componentVertex C d) ∩ D).ncard := by
    apply Set.ncard_congr (fun a _ => componentVertex C a)
    · intro a ha; exact ⟨ha, a, Set.mem_univ a, rfl⟩
    · intro a b _ _ he; exact componentVertex_injective C he
    · rintro z ⟨edz, a, _ha, he⟩
      have e : C.toSimpleGraph.Adj d a :=
        Eq.mpr (congrArg (fun z : V => G.Adj (componentVertex C d) z) he) edz
      exact ⟨a, e, he⟩
  rw [heq]
  exact (disjoint_region_neighbor_partition G D Q hdis (componentVertex C d) hcover).symm

theorem casebi_actual_component_tail (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) (d yr : C.supp) (y : V)
    (hY : componentVertex C yr = y) :
    ∃ R : G.Walk (componentVertex C d) y, R.IsPath ∧ ∀ z ∈ R.support, z ∉ Q := by
  subst y
  obtain ⟨r, hr⟩ := C.connected_toSimpleGraph.exists_isPath d yr
  let R := r.map (componentVertexHom C)
  refine ⟨R, (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hr, ?_⟩
  intro z hz
  change z ∈ (r.map (componentVertexHom C)).support at hz
  rw [Walk.support_map] at hz
  obtain ⟨a, _ha, he⟩ := List.mem_map.mp hz
  have he' : componentVertex C a = z := he
  exact fun hzQ => a.1.2 (Eq.mpr (congrArg (fun z : V => z ∈ Q) he') hzQ)

theorem casebi_component_no_nonroot_leaf [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y) (d : C.supp) (hdy : d ≠ yr) :
    2 ≤ (C.toSimpleGraph.neighborSet d).ncard := by
  classical
  by_contra hn
  have hin : (C.toSimpleGraph.neighborSet d).ncard ≤ 1 := by omega
  have hdx : componentVertex C d ≠ x := fun he => d.1.2
    (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr hmax.1.2.2.1))
  have hdyV : componentVertex C d ≠ y := fun he =>
    hdy (componentVertex_injective C (he.trans hY.symm))
  have hout : componentVertex C d ∉ (A ∪ B) ∪ {y} := by
    rintro (hz | hz)
    · exact d.1.2 hz
    · exact hdyV hz
  have hpart := casebi_component_neighbor_partition G (A ∪ B) C d
  have hdOrig := hd (componentVertex C d) hdx hdyV
  have hcore : k ≤ (G.neighborSet (componentVertex C d) ∩ (A ∪ B)).ncard := by omega
  have hcap := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad
    (componentVertex C d) hout
  obtain ⟨R, hR, hRQ⟩ := casebi_actual_component_tail G (A ∪ B) C d yr y hY
  by_cases hA : ∃ a ∈ A, G.Adj (componentVertex C d) a
  · obtain ⟨a, ha, eda⟩ := hA
    have hkB : k ≤ B.ncard := by omega
    obtain ⟨P, hP⟩ := casebi_set_odd_prefix G A B k x a hmax.1.1 hmax.1.2.1
      hmax.1.2.2.1 ha (hkB.trans hmax.1.2.2.2.2.2) hkB
    have haR : a ∉ R.support := fun hh => hRQ a hh (Or.inl ha)
    let T : G.Walk a y := Walk.cons eda.symm R
    have hT : T.IsPath := hR.cons haR
    have hTQ : ∀ z ∈ T.support, z ∈ A ∪ B → z = a := by
      intro z hz hzQ
      change z ∈ a :: R.support at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact he
      · exact False.elim (hRQ z hz hzQ)
    exact hno (casebi_prefix_and_actual_tail G (A ∪ B) x a y k 1 2 P hP (Or.inr rfl)
      T hT hTQ (by change 2 ≤ 1 + (Walk.cons eda.symm R).length; rw [Walk.length_cons]; omega))
  · have heq : G.neighborSet (componentVertex C d) ∩ (A ∪ B) =
        G.neighborSet (componentVertex C d) ∩ B := by
      ext z
      constructor
      · rintro ⟨edz, hzA | hzB⟩
        · exact False.elim (hA ⟨z, hzA, edz⟩)
        · exact ⟨edz, hzB⟩
      · rintro ⟨edz, hzB⟩; exact ⟨edz, Or.inr hzB⟩
    rw [heq] at hcore
    have hcapB := casebi_lexmax_second_neighbor_cap G x y A B hmax
      (componentVertex C d) hout
    have hks : k ≤ s := by omega
    obtain ⟨a, ha, hax⟩ := Set.exists_ne_of_one_lt_ncard
      (by omega : 1 < (G.neighborSet (componentVertex C d) ∩ B).ncard) x
    obtain ⟨P, hP⟩ := casebi_set_even_prefix G A B k x a hmax.1.1 hmax.1.2.1
      hmax.1.2.2.1 ha.2 hax.symm
      (by have hh := hmax.1.2.2.2.2.2; omega) (by omega)
    have haR : a ∉ R.support := fun hh => hRQ a hh (Or.inr ha.2)
    let T : G.Walk a y := Walk.cons ha.1.symm R
    have hT : T.IsPath := hR.cons haR
    have hTQ : ∀ z ∈ T.support, z ∈ A ∪ B → z = a := by
      intro z hz hzQ
      change z ∈ a :: R.support at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact he
      · exact False.elim (hRQ z hz hzQ)
    exact hno (casebi_prefix_and_actual_tail G (A ∪ B) x a y k 2 2 P hP (Or.inr rfl)
      T hT hTQ (by omega))

#print axioms casebi_component_neighbor_partition
#print axioms casebi_actual_component_tail
#print axioms casebi_component_no_nonroot_leaf
end TaskH.Gao
