import Research.TaskH.Gao.OriginalLeafDegreeNeighborSets
import Research.TaskH.Gao.TerminalCommonPointDeletedComponents
import Research.TaskH.Gao.CasebiFeasibleRigidity

/-! The common terminal point and deleted-component restriction are derived
inside the actual original normalized counterexample's y-leaf branch. No
terminal cover, common-point oracle, or desired path family is input. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_y_leaf_original_common_terminal_point [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (hxy : ¬G.Adj x y)
    (htri : CasebiNoRootTriangle G x y) (htriY : CasebiNoRootTriangle G y x)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (r + 1) → HasAdmissiblePaths J a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr b2 : C.supp) (hY : componentVertex C yr = y)
    (hC : 2 ≤ Fintype.card C.supp)
    (hleaf : C.toSimpleGraph.neighborSet yr = {b2}) :
    ∃ p : C.supp,
      G.neighborSet x = insert (componentVertex C p) A ∧
      G.neighborSet y = insert (componentVertex C b2) A ∧
      (∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        yr ∉ I → p ∈ I) ∧
      ∀ (z : C.supp) (D : (C.toSimpleGraph.induce {v | v ≠ z}).ConnectedComponent),
        yr ∉ deletedInterior C.toSimpleGraph z D → p ∈ deletedInterior C.toSimpleGraph z D := by
  classical
  obtain ⟨I1, b1, hT1, hyI1, _hI1, _hTwo1, _hTail1⟩ :=
    casebi_actual_feasible_block_exists G A B x y s k hmax hBs hk htri hquad hd hno
      C yr hY hC
  obtain ⟨hs1, hattach1⟩ := casebi_feasible_second_side_rigidity G A B x y s k hmax hBs hk
    hG htri hquad hd hno ih C yr hY I1 b1 hT1 hyI1
  obtain ⟨p, _hpI1, epx⟩ := hattach1 x hmax.1.2.2.1
  have hB2 : B.ncard = 2 := by omega
  obtain ⟨a, haB, hax⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < B.ncard) x
  have hpair : ({x, a} : Set V) ⊆ B := by
    rintro z (hzx | hza)
    · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hzx) hmax.1.2.2.1
    · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hza) haB
  have hBeq : B = ({x, a} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le hpair
    rw [Set.ncard_pair hax.symm]
    omega
  have hA2 : 2 ≤ A.ncard := hmax.1.2.2.2.2.1.trans hmax.1.2.2.2.2.2
  have hxA : x ∉ A := fun hx => Set.disjoint_left.mp hmax.1.1 hx hmax.1.2.2.1
  have hpA : componentVertex C p ∉ A := fun hp => p.1.2 (Or.inl hp)
  have hbA : componentVertex C b2 ∉ A := fun hb => b2.1.2 (Or.inl hb)
  have hab : a ≠ componentVertex C b2 := by
    intro he
    exact b2.1.2 (Or.inr (Eq.mp (congrArg (fun z : V => z ∈ B) he) haB))
  have hcover : ∀ z, G.Adj y z → z ∈ A ∨ z = a ∨ z = componentVertex C b2 := by
    intro z eyz
    rcases actual_component_root_leaf_neighbor_cover G (A ∪ B) C yr b2 y hY hleaf z eyz with hzQ | hzb
    · rcases hzQ with hzA | hzB
      · exact Or.inl hzA
      · rw [hBeq] at hzB
        rcases hzB with hzx | hza
        · have eyx : G.Adj y x := Eq.mp (congrArg (fun z : V => G.Adj y z) hzx) eyz
          exact False.elim (hxy eyx.symm)
        · exact Or.inr (Or.inl hza)
    · exact Or.inr (Or.inr hzb)
  obtain ⟨hNX, hNY⟩ := biclique_leaf_root_neighbor_sets G A x y a
    (componentVertex C b2) (componentVertex C p) hA2 hxA hpA hbA hax hab
    (fun u hu => (hmax.1.2.1 u hu x hmax.1.2.2.1).symm)
    (fun u hu => (hmax.1.2.1 u hu a haB).symm) epx.symm hcover htriY horder
  have hcommon : ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      yr ∉ I → p ∈ I := by
    intro I b hT hyI
    obtain ⟨_hs, hattach⟩ := casebi_feasible_second_side_rigidity G A B x y s k hmax hBs hk
      hG htri hquad hd hno ih C yr hY I b hT hyI
    obtain ⟨q, hqI, eqx⟩ := hattach x hmax.1.2.2.1
    have hmem : componentVertex C q ∈ insert (componentVertex C p) A := by
      rw [← hNX]
      exact eqx.symm
    rcases hmem with he | hqA
    · have hqp : q = p := componentVertex_injective C he
      exact Eq.mp (congrArg (fun z : C.supp => z ∈ I) hqp) hqI
    · exact False.elim (q.1.2 (Or.inl hqA))
  refine ⟨p, hNX, hNY, hcommon, ?_⟩
  intro z D hyD
  exact terminal_common_point_in_deleted_component C.toSimpleGraph yr p z
    C.connected_toSimpleGraph hcommon D hyD

#print axioms casebi_y_leaf_original_common_terminal_point
end TaskH.Gao
