import Research.TaskH.Gao.CasebiFeasibleRigidity
import Research.TaskH.Fan.RootedSetRetraction

/-! Actual G-C rooted connectivity for the s=1 Case1 branch, with every deletion. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_core_outside_component (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) (z : V) (hz : z ∈ Q) :
    z ∈ (componentRegion C Set.univ)ᶜ :=
  fun hzC => Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) hzC hz

theorem casebi_component_exit_in_core (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) (v z : V)
    (hv : v ∈ componentRegion C Set.univ) (hz : z ∉ componentRegion C Set.univ)
    (evz : G.Adj v z) : z ∈ Q := by
  classical
  by_contra hzQ
  obtain ⟨w, _hw, he⟩ := hv
  have ewz : (G.induce Qᶜ).Adj w.1 ⟨z, hzQ⟩ :=
    Eq.mpr (congrArg (fun v : V => G.Adj v z) he) evz
  let zr : C.supp := ⟨⟨z, hzQ⟩, C.mem_supp_of_adj_mem_supp w.2 ewz⟩
  exact hz ⟨zr, Set.mem_univ zr, rfl⟩

theorem casebi_pair_augmented_adj_or_eq (G : SimpleGraph V) (S : Set V)
    (x a : V) (hx : x ∈ S) (ha : a ∈ S) (v t : S)
    (hv : v.1 = x ∨ v.1 = a) (ht : t.1 = x ∨ t.1 = a) :
    v = t ∨ ((G.induce S) ⊔ SimpleGraph.edge ⟨x, hx⟩ ⟨a, ha⟩).Adj v t := by
  classical
  by_cases he : v = t
  · exact Or.inl he
  · right; right
    apply (SimpleGraph.edge_adj (⟨x, hx⟩ : S) ⟨a, ha⟩ v t).mpr
    refine ⟨?_, he⟩
    rcases hv with hvx | hva <;> rcases ht with htx | hta
    · exact False.elim (he (Subtype.ext (hvx.trans htx.symm)))
    · exact Or.inl ⟨Subtype.ext hvx, Subtype.ext hta⟩
    · exact Or.inr ⟨Subtype.ext hva, Subtype.ext htx⟩
    · exact False.elim (he (Subtype.ext (hva.trans hta.symm)))

theorem casebi_outside_retraction_adj_or_eq (G : SimpleGraph V) (A B : Set V)
    (x a : V) (hcross : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) (hB : B = {x, a})
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent)
    (hx : x ∈ (componentRegion C Set.univ)ᶜ) (ha : a ∈ (componentRegion C Set.univ)ᶜ)
    (t : {v : V // v ∉ componentRegion C Set.univ}) (ht : t.1 = x ∨ t.1 = a)
    {v w : V} (evw : G.Adj v w) :
    rootedSetRetraction (componentRegion C Set.univ)ᶜ t.1 t.2 v =
      rootedSetRetraction (componentRegion C Set.univ)ᶜ t.1 t.2 w ∨
      (((G.induce (componentRegion C Set.univ)ᶜ) ⊔
        SimpleGraph.edge ⟨x, hx⟩ ⟨a, ha⟩)).Adj
        (rootedSetRetraction (componentRegion C Set.univ)ᶜ t.1 t.2 v)
        (rootedSetRetraction (componentRegion C Set.univ)ᶜ t.1 t.2 w) := by
  classical
  let S := (componentRegion C Set.univ)ᶜ
  have hcore : ∀ z : S, z.1 ∈ A ∪ B → z = t ∨
      ((G.induce S) ⊔ SimpleGraph.edge ⟨x, hx⟩ ⟨a, ha⟩).Adj z t := by
    intro z hz
    rcases hz with hzA | hzB
    · right; left
      have htB : t.1 ∈ B :=
        Eq.mpr (congrArg (fun Q : Set V => t.1 ∈ Q) hB) ht
      exact hcross z.1 hzA t.1 htB
    · have hzB' : z.1 = x ∨ z.1 = a :=
        Eq.mp (congrArg (fun Q : Set V => z.1 ∈ Q) hB) hzB
      exact casebi_pair_augmented_adj_or_eq G S x a hx ha z t hzB' ht
  by_cases hv : v ∈ S
  · by_cases hw : w ∈ S
    · rw [rootedSetRetraction_mem S t.1 t.2 v hv, rootedSetRetraction_mem S t.1 t.2 w hw]
      exact Or.inr (Or.inl evw)
    · have hwC : w ∈ componentRegion C Set.univ := by
        change ¬(w ∉ componentRegion C Set.univ) at hw
        exact not_not.mp hw
      have hvQ := casebi_component_exit_in_core G (A ∪ B) C w v hwC hv evw.symm
      rw [rootedSetRetraction_mem S t.1 t.2 v hv]
      have hwt : rootedSetRetraction S t.1 t.2 w = t := by
        unfold rootedSetRetraction; exact dite_eq_right hw
      rw [hwt]
      exact hcore ⟨v, hv⟩ hvQ
  · by_cases hw : w ∈ S
    · have hvC : v ∈ componentRegion C Set.univ := by
        change ¬(v ∉ componentRegion C Set.univ) at hv
        exact not_not.mp hv
      have hwQ := casebi_component_exit_in_core G (A ∪ B) C v w hvC hw evw
      rw [rootedSetRetraction_mem S t.1 t.2 w hw]
      have hvt : rootedSetRetraction S t.1 t.2 v = t := by
        unfold rootedSetRetraction; exact dite_eq_right hv
      rw [hvt]
      exact (hcore ⟨w, hw⟩ hwQ).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    · left
      have hvt : rootedSetRetraction S t.1 t.2 v = t := by
        unfold rootedSetRetraction
        exact dite_eq_right hv
      have hwt : rootedSetRetraction S t.1 t.2 w = t := by
        unfold rootedSetRetraction
        exact dite_eq_right hw
      exact hvt.trans hwt.symm

theorem casebi_outside_component_rooted [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x a : V) (hAB : Disjoint A B)
    (hcross : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) (hB : B = {x, a}) (hxa : x ≠ a)
    (hA : A.Nonempty) (hG : TwoConnected G)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent)
    [Fintype ↥((componentRegion C Set.univ)ᶜ : Set V)] :
    RootedTwoConnected (G.induce (componentRegion C Set.univ)ᶜ)
      ⟨x, casebi_core_outside_component G (A ∪ B) C x (Or.inr (by rw [hB]; exact Or.inl rfl))⟩
      ⟨a, casebi_core_outside_component G (A ∪ B) C a (Or.inr (by rw [hB]; exact Or.inr rfl))⟩ := by
  classical
  let S := (componentRegion C Set.univ)ᶜ
  have hxB : x ∈ B := by rw [hB]; exact Or.inl rfl
  have haB : a ∈ B := by rw [hB]; exact Or.inr rfl
  have hxS : x ∈ S := casebi_core_outside_component G (A ∪ B) C x (Or.inr hxB)
  have haS : a ∈ S := casebi_core_outside_component G (A ∪ B) C a (Or.inr haB)
  let xr : S := ⟨x, hxS⟩
  let ar : S := ⟨a, haS⟩
  let J := (G.induce S) ⊔ SimpleGraph.edge xr ar
  have hxr : xr ≠ ar := fun he => hxa (congrArg Subtype.val he)
  obtain ⟨c, hcA⟩ := hA
  let cr : S := ⟨c, casebi_core_outside_component G (A ∪ B) C c (Or.inl hcA)⟩
  have hxc : xr ≠ cr := fun he => Set.disjoint_left.mp hAB hcA
    (Eq.mp (congrArg (fun z : V => z ∈ B) (congrArg Subtype.val he)) hxB)
  have hac : ar ≠ cr := fun he => Set.disjoint_left.mp hAB hcA
    (Eq.mp (congrArg (fun z : V => z ∈ B) (congrArg Subtype.val he)) haB)
  have hcard : 3 ≤ Fintype.card S := by
    have hn := Fintype.two_lt_card_iff.mpr ⟨xr, ar, cr, hxr, hxc, hac⟩
    omega
  have hc : J.Connected := connected_of_surjective_adj_or_eq
    (rootedSetRetraction S x hxS) (rootedSetRetraction_surjective S x hxS)
    (casebi_outside_retraction_adj_or_eq G A B x a hcross hB C hxS haS xr (Or.inl rfl)) hG.2.1
  refine ⟨hxr, hcard, hc, ?_⟩
  intro z
  have hchoose : ∃ t : S, (t.1 = x ∨ t.1 = a) ∧ z.1 ≠ t.1 := by
    by_cases hzx : z.1 = x
    · exact ⟨ar, Or.inr rfl, fun he => hxa (hzx.symm.trans he)⟩
    · exact ⟨xr, Or.inl rfl, hzx⟩
  obtain ⟨t, ht, hzt⟩ := hchoose
  let f := rootedSetDeleteRetraction S t.1 t.2 z hzt
  have hf : ∀ {v w : {v : V // v ≠ z.1}},
      (G.induce {v : V | v ≠ z.1}).Adj v w → f v = f w ∨
        (J.induce {v : S | v ≠ z}).Adj (f v) (f w) := by
    intro v w e
    rcases casebi_outside_retraction_adj_or_eq G A B x a hcross hB C hxS haS t ht e with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  exact connected_of_surjective_adj_or_eq f
    (rootedSetDeleteRetraction_surjective S t.1 t.2 z hzt) hf (hG.2.2 z.1)

theorem casebi_outside_component_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y a : V) (k : ℕ) (hB : B = {x, a})
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y)
    (hcase : ∀ w : C.supp, w ≠ yr → ∀ z ∈ A, ¬G.Adj (componentVertex C w) z)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hx : x ∈ (componentRegion C Set.univ)ᶜ) (ha : a ∈ (componentRegion C Set.univ)ᶜ) :
    NonrootDegreeAtLeast (G.induce (componentRegion C Set.univ)ᶜ) ⟨x, hx⟩ ⟨a, ha⟩ k := by
  classical
  let D := componentRegion C Set.univ
  intro v hvx hva
  have hvx' : v.1 ≠ x := fun he => hvx (Subtype.ext he)
  have hva' : v.1 ≠ a := fun he => hva (Subtype.ext he)
  have hyD : y ∈ D := ⟨yr, Set.mem_univ yr, hY⟩
  have hvy : v.1 ≠ y := fun he => v.2
    (Eq.mpr (congrArg (fun v : V => v ∈ D) he) hyD)
  have hsub : G.neighborSet v.1 ∩ D ⊆ {y} := by
    rintro z ⟨evz, w, _hw, he⟩
    change z = y
    by_contra hzy
    have hvQ := casebi_component_exit_in_core G (A ∪ B) C z v.1
      ⟨w, Set.mem_univ w, he⟩ v.2 evz.symm
    rcases hvQ with hvA | hvB
    · have hwy : w ≠ yr := by
        intro hw
        have hwyV : componentVertex C w = y := (congrArg (componentVertex C) hw).trans hY
        exact hzy (he.symm.trans hwyV)
      have ewv : G.Adj (componentVertex C w) v.1 :=
        Eq.mpr (congrArg (fun z : V => G.Adj z v.1) he) evz.symm
      exact hcase w hwy v.1 hvA ewv
    · have hvB' : v.1 = x ∨ v.1 = a :=
        Eq.mp (congrArg (fun Q : Set V => v.1 ∈ Q) hB) hvB
      exact hvB'.elim hvx' hva'
  have hsmall : (G.neighborSet v.1 ∩ D).ncard ≤ 1 := by
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
  have heq : ((G.induce Dᶜ).neighborSet v).ncard = (G.neighborSet v.1 \ D).ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact ⟨hz, z.2⟩
    · intro z w _ _ he; exact Subtype.ext he
    · rintro z ⟨evz, hzD⟩; exact ⟨⟨z, hzD⟩, evz, rfl⟩
  have hp := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v.1) D
  have ho := hd v.1 hvx' hvy
  rw [heq]
  omega

#print axioms casebi_core_outside_component
#print axioms casebi_component_exit_in_core
#print axioms casebi_pair_augmented_adj_or_eq
#print axioms casebi_outside_retraction_adj_or_eq
#print axioms casebi_outside_component_rooted
#print axioms casebi_outside_component_degree
end TaskH.Gao
