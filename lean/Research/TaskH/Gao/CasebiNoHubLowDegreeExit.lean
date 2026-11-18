import Research.TaskH.Gao.CasebiOriginalLeafCommonPoint

/-! The final small-internal-degree exit gives the actual forbidden y-triangle.
Exact neighbor identities are the conclusions of the preceding original-domain
wrapper, not new premises of Gao.Main. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_y_leaf_boundary_low_degree_contradiction [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (k : ℕ)
    (hQ : CasebiBiclique G x y A B) (hB2 : B.ncard = 2) (hk : 3 ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (htriY : CasebiNoRootTriangle G y x)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr b2 p : C.supp)
    (hY : componentVertex C yr = y)
    (hleaf : C.toSimpleGraph.neighborSet yr = {b2}) (hbp : b2 ≠ p)
    (hNX : G.neighborSet x = insert (componentVertex C p) A)
    (hNY : G.neighborSet y = insert (componentVertex C b2) A)
    (hsmall : (C.toSimpleGraph.neighborSet b2).ncard ≤ 2) : False := by
  classical
  let b := componentVertex C b2
  have hbx : b ≠ x := by
    intro he
    exact b2.1.2 (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr hQ.2.2.1))
  have eYB : C.toSimpleGraph.Adj yr b2 := by
    have hh : b2 ∈ ({b2} : Set C.supp) := rfl
    rw [← hleaf] at hh
    exact hh
  have eyb : G.Adj y b :=
    Eq.mp (congrArg (fun z : V => G.Adj z b) hY) eYB
  have hby : b ≠ y := by
    intro he
    have eyy : G.Adj y y := Eq.mp (congrArg (fun z : V => G.Adj y z) he) eyb
    exact G.irrefl eyy
  have hnxb : ¬G.Adj x b := by
    intro exb
    have hh : b ∈ insert (componentVertex C p) A := by rw [← hNX]; exact exb
    rcases hh with he | hbA
    · exact hbp (componentVertex_injective C he)
    · exact b2.1.2 (Or.inl hbA)
  have hpart := casebi_component_neighbor_partition G (A ∪ B) C b2
  have hdeg := hd b hbx hby
  have hcore : 2 ≤ (G.neighborSet b ∩ (A ∪ B)).ncard := by
    change k + 1 ≤ (G.neighborSet (componentVertex C b2)).ncard at hdeg
    change 2 ≤ (G.neighborSet (componentVertex C b2) ∩ (A ∪ B)).ncard
    omega
  obtain ⟨a, haB, hax⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < B.ncard) x
  have hpair : ({x, a} : Set V) ⊆ B := by
    rintro z (hzx | hza)
    · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hzx) hQ.2.2.1
    · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hza) haB
  have hBeq : B = ({x, a} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le hpair
    rw [Set.ncard_pair hax.symm]
    omega
  have htouch : ∃ w ∈ A, G.Adj b w := by
    by_contra hn
    have hsub : G.neighborSet b ∩ (A ∪ B) ⊆ ({a} : Set V) := by
      intro z hz
      rcases hz.2 with hzA | hzB
      · exact False.elim (hn ⟨z, hzA, hz.1⟩)
      · rw [hBeq] at hzB
        rcases hzB with hzx | hza
        · have ebx : G.Adj b x := Eq.mp (congrArg (fun z : V => G.Adj b z) hzx) hz.1
          exact False.elim (hnxb ebx.symm)
        · exact hza
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at hh
    omega
  obtain ⟨w, hwA, ebw⟩ := htouch
  have hwx : w ≠ x := by
    intro he
    exact Set.disjoint_left.mp hQ.1
      (Eq.mp (congrArg (fun z : V => z ∈ A) he) hwA) hQ.2.2.1
  have eyw : G.Adj y w := by
    change w ∈ G.neighborSet y
    rw [hNY]
    exact Or.inr hwA
  exact htriY b w hbx hwx eyb ebw eyw.symm

#print axioms casebi_y_leaf_boundary_low_degree_contradiction
end TaskH.Gao
