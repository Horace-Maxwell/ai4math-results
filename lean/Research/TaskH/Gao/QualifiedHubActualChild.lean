import Research.TaskH.Gao.MaximalRegionActualAttachments
import Research.TaskH.Gao.CarrierAttachmentCuts
import Research.TaskH.Gao.CasebiActualNoLeaf
import Research.TaskH.Gao.FamilyOperations
import Research.TaskH.Fan.IdentificationYComponent

/-! Actual cut qualification gives nonroot neighbor closure, then original
neighbor partition and strict order supply the low-Q child family. Bypass
uses the actual ordinary hub minus the same nonroot w, never a different B. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem maximal_region_nonroot_neighbors_stay [Fintype V]
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (hG : G.Connected) (hS : TwoConnected (G.induce S))
    (hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S)
    (u v : S) (_huv : u ≠ v)
    (hcut : ∀ z ∈ S, ¬(G.induce {w | w ≠ z}).Connected → z = u.1 ∨ z = v.1)
    (w : S) (hwu : w ≠ u) (hwv : w ≠ v) :
    ∀ d, G.Adj w.1 d → d ∈ S := by
  classical
  have hCar := maximal_twoConnected_region_single_attachment G S hG hS hmax
  intro d ewd
  by_contra hdS
  let C := (G.induce Sᶜ).connectedComponentMk ⟨d, hdS⟩
  let dr : C.supp := ⟨⟨d, hdS⟩, rfl⟩
  have he : w = carrierAttachment G S hCar C :=
    carrierAttachment_unique G S hCar C dr w ewd.symm
  have hu : u ≠ carrierAttachment G S hCar C :=
    fun hu => hwu (he.trans hu.symm)
  have hAtt := carrierAttachment_cut G S hCar C u hu
  have hwcut : ¬(G.induce {d | d ≠ w.1}).Connected := by
    intro hc
    apply hAtt
    exact Eq.mp (congrArg (fun z : V => (G.induce {d | d ≠ z}).Connected)
      (congrArg Subtype.val he)) hc
  exact (hcut w.1 w.2 hwcut).elim
    (fun he => hwu (Subtype.ext he)) (fun he => hwv (Subtype.ext he))

theorem maximal_hub_low_Q_original_family [Fintype V]
    (G : SimpleGraph V) (Q : Set V) (x y : V) (k : ℕ) (hk : 3 ≤ k) (hxQ : x ∈ Q)
    (C : (G.induce Qᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (S : Set C.supp) [Fintype S] (u v : S) (huv : u ≠ v)
    (hS : TwoConnected (C.toSimpleGraph.induce S))
    (hmax : ∀ (T : Set C.supp) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (C.toSimpleGraph.induce T) → T ⊆ S)
    (hcut : ∀ z ∈ S, ¬(C.toSimpleGraph.induce {w | w ≠ z}).Connected →
      z = u.1 ∨ z = v.1)
    (hyS : yr ∈ S → yr = v.1)
    (hLow : ∀ w : S, w ≠ u → w ≠ v →
      (G.neighborSet (componentVertex C w.1) ∩ Q).ncard ≤ 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (n + 1) → HasAdmissiblePaths J a b n) :
    ∃ (a d : ℕ) (P : Fin (k - 1) → G.Walk (componentVertex C u.1) (componentVertex C v.1)),
      AdmissiblePathFamily G (componentVertex C u.1) (componentVertex C v.1) (k - 1) a d P ∧
      ∀ i z, z ∈ (P i).support → z ∈ componentRegion C S := by
  classical
  have hdeg : NonrootDegreeAtLeast (C.toSimpleGraph.induce S) u v k := by
    intro w hwu hwv
    have hclosed := maximal_region_nonroot_neighbors_stay C.toSimpleGraph S
      C.connected_toSimpleGraph hS hmax u v huv hcut w hwu hwv
    have heq : ((C.toSimpleGraph.induce S).neighborSet w).ncard =
        (C.toSimpleGraph.neighborSet w.1).ncard := by
      apply Set.ncard_congr (fun z _ => z.1)
      · intro z hz; exact hz
      · intro z d _ _ he; exact Subtype.ext he
      · intro z hz; exact ⟨⟨z, hclosed z hz⟩, hz, rfl⟩
    have hwx : componentVertex C w.1 ≠ x := fun he => w.1.1.2
      (Eq.mpr (congrArg (fun z : V => z ∈ Q) he) hxQ)
    have hwy : componentVertex C w.1 ≠ y := by
      intro he
      have hwyr : w.1 = yr := componentVertex_injective C (he.trans hY.symm)
      have hyr : yr ∈ S := Eq.mp (congrArg (fun z : C.supp => z ∈ S) hwyr) w.2
      exact hwv (Subtype.ext (hwyr.trans (hyS hyr)))
    have hOrig := hd (componentVertex C w.1) hwx hwy
    have hpart := casebi_component_neighbor_partition G Q C w.1
    have hl := hLow w hwu hwv
    rw [heq]
    omega
  let f : S → V := fun w => componentVertex C w.1
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (componentVertex_injective C he)
  have hns : ¬Function.Surjective f := by
    intro hs
    obtain ⟨w, hw⟩ := hs x
    exact w.1.1.2 (Eq.mpr (congrArg (fun z : V => z ∈ Q) hw) hxQ)
  have hlt : Fintype.card S < Fintype.card V := Fintype.card_lt_of_injective_not_surjective f hf hns
  have hroot : RootedTwoConnected (C.toSimpleGraph.induce S) u v :=
    ⟨huv, twoConnected_mono _ _ le_sup_left hS⟩
  let m := k - 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmk : m + 1 = k := by dsimp [m]; omega
  have hdeg' : NonrootDegreeAtLeast (C.toSimpleGraph.induce S) u v (m + 1) := by
    rw [hmk]; exact hdeg
  obtain ⟨a, d, P, hP⟩ := ih S (C.toSimpleGraph.induce S) u v m hlt hm hroot hdeg'
  let g : C.toSimpleGraph.induce S →g G :=
    { toFun := f
      map_rel' := fun e => e }
  have hmap := admissible_family_map (C.toSimpleGraph.induce S) G g hf u v m a d P hP
  refine ⟨a, d, (fun i => (P i).map g), hmap.1, ?_⟩
  intro i z hz
  obtain ⟨w, _hw, he⟩ := (hmap.2 i z).mp hz
  exact ⟨w.1, w.2, he⟩

theorem actual_hub_deleted_nonroot_bypass [Fintype V]
    (G : SimpleGraph V) (Q : Set V) (C : (G.induce Qᶜ).ConnectedComponent)
    (S : Set C.supp) [Fintype S] (hS : TwoConnected (C.toSimpleGraph.induce S))
    (u v w : S) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ P : G.Walk (componentVertex C u.1) (componentVertex C v.1), P.IsPath ∧
      ∀ z ∈ P.support, z ∈ componentRegion C S ∧ z ≠ componentVertex C w.1 := by
  classical
  obtain ⟨p, hp⟩ := (hS.2.2 w).exists_isPath ⟨u, huw⟩ ⟨v, hvw⟩
  let f : ((C.toSimpleGraph.induce S).induce {z : S | z ≠ w}) →g G :=
    { toFun := fun z => componentVertex C z.1.1
      map_rel' := fun e => e }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (componentVertex_injective C he))
  refine ⟨p.map f, (Walk.isPath_map_iff_of_injective hf).mpr hp, ?_⟩
  intro z hz
  rw [Walk.support_map] at hz
  obtain ⟨r, _hr, he⟩ := List.mem_map.mp hz
  have he' : componentVertex C r.1.1 = z := he
  refine ⟨⟨r.1.1, r.1.2, he'⟩, ?_⟩
  intro hzw
  exact r.2 (Subtype.ext (componentVertex_injective C (he'.trans hzw)))

#print axioms maximal_region_nonroot_neighbors_stay
#print axioms maximal_hub_low_Q_original_family
#print axioms actual_hub_deleted_nonroot_bypass
end TaskH.Gao
