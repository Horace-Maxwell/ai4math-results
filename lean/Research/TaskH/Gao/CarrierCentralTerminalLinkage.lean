import Research.TaskH.Gao.CarrierTerminalBranches
import Research.TaskH.Gao.TwoTerminalRouteCertificate
import Research.TaskH.Gao.PathConcatenation
import Research.TaskH.Gao.UnorderedLinkage.TwoSetLinkage

/-! Real exterior terminal tails are spliced with internally obtained unordered
central paths. All support statements are about the full original walks. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem carrier_terminal_routes_of_actual_central_paths [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : (carrierAttachment G S hS C).1 ≠ (carrierAttachment G S hS D).1)
    (w y : S)
    (L : (G.induce S).Walk (carrierAttachment G S hS C) w)
    (R : (G.induce S).Walk (carrierAttachment G S hS D) y)
    (hL : L.IsPath) (hR : R.IsPath) (hLR : L.support.Disjoint R.support) :
    TwoTerminalRoutes G w.1 y.1 := by
  classical
  let a := carrierAttachment G S hS C
  let d := carrierAttachment G S hS D
  let EC := componentRegion C Set.univ
  let ED := componentRegion D Set.univ
  let TC := EC ∪ {a.1}
  let TD := ED ∪ {d.1}
  have hne : C ≠ D := fun he => hCD (congrArg (fun C => (carrierAttachment G S hS C).1) he)
  have hEC : Disjoint EC S := componentRegion_disjoint C Set.univ
  have hED : Disjoint ED S := componentRegion_disjoint D Set.univ
  have hRegions : Disjoint EC ED := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u, _hu, he⟩ ⟨v, _hv, hev⟩
    have huv : u.1 = v.1 := Subtype.ext (he.trans hev.symm)
    have hvC : v.1 ∈ C.supp :=
      Eq.mp (congrArg (fun a : {v : V // v ∉ S} => a ∈ C.supp) huv) u.2
    exact hne (ConnectedComponent.eq_of_common_vertex hvC v.2)
  have hDis : Disjoint TC TD := by
    apply Set.disjoint_left.mpr
    rintro z (hzC | heC) (hzD | heD)
    · exact Set.disjoint_left.mp hRegions hzC hzD
    · exact Set.disjoint_left.mp hEC hzC
        (Eq.mpr (congrArg (fun z : V => z ∈ S) heD) d.2)
    · exact Set.disjoint_left.mp hED hzD
        (Eq.mpr (congrArg (fun z : V => z ∈ S) heC) a.2)
    · exact hCD (heC.symm.trans heD)
  obtain ⟨I, b, hI, hIC, hIB, P, hP, hPS, hPB⟩ :=
    carrier_terminal_in_actual_outside_component G S hS hG C
  obtain ⟨J, c, hJ, hJD, hJB, Q, hQ, hQS, hQB⟩ :=
    carrier_terminal_in_actual_outside_component G S hS hG D
  let f : G.induce S →g G := (Embedding.induce S).toHom
  let l : G.Walk a.1 w.1 := L.map f
  let r : G.Walk d.1 y.1 := R.map f
  have hmap : ∀ {v t : S} (p : (G.induce S).Walk v t) (z : V),
      z ∈ (p.map f).support ↔ ∃ q ∈ p.support, q.1 = z := by
    intro v t p z
    rw [Walk.support_map]
    constructor
    · intro hz
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hz
      have he' : q.1 = z := he
      exact ⟨q, hq, he'⟩
    · rintro ⟨q, hq, he⟩
      apply List.mem_map.mpr
      have he' : f q = z := he
      exact ⟨q, hq, he'⟩
  have hls : ∀ z ∈ l.support, z ∈ S := by
    intro z hz
    obtain ⟨v, _hv, he⟩ := (hmap L z).mp hz
    exact Eq.mp (congrArg (fun z : V => z ∈ S) he) v.2
  have hrs : ∀ z ∈ r.support, z ∈ S := by
    intro z hz
    obtain ⟨v, _hv, he⟩ := (hmap R z).mp hz
    exact Eq.mp (congrArg (fun z : V => z ∈ S) he) v.2
  have hsep : ∀ z ∈ l.support, z ∈ r.support → False := by
    intro z hzL hzR
    obtain ⟨u, hu, he⟩ := (hmap L z).mp hzL
    obtain ⟨v, hv, hev⟩ := (hmap R z).mp hzR
    have huv : u = v := Subtype.ext (he.trans hev.symm)
    exact List.disjoint_left.mp hLR hu
      (Eq.mpr (congrArg (fun v : S => v ∈ R.support) huv) hv)
  have hPC : ∀ z ∈ P.support, z ∈ S → z = a.1 := by
    intro z hz hzS
    rcases (hPS z hz).1 with hzC | he
    · exact False.elim (Set.disjoint_left.mp hEC hzC hzS)
    · exact he
  have hQD : ∀ z ∈ Q.support, z ∈ S → z = d.1 := by
    intro z hz hzS
    rcases (hQS z hz).1 with hzD | he
    · exact False.elim (Set.disjoint_left.mp hED hzD hzS)
    · exact he
  have hPl : ∀ z ∈ P.support, z ∈ l.support → z = a.1 :=
    fun z hzP hzl => hPC z hzP (hls z hzl)
  have hQr : ∀ z ∈ Q.support, z ∈ r.support → z = d.1 :=
    fun z hzQ hzr => hQD z hzQ (hrs z hzr)
  have hPr : ∀ z ∈ P.support, z ∈ r.support → False := by
    intro z hzP hzr
    have he := hPC z hzP (hrs z hzr)
    exact hsep a.1 l.start_mem_support
      (Eq.mp (congrArg (fun z : V => z ∈ r.support) he) hzr)
  have hlQ : ∀ z ∈ l.support, z ∈ Q.support → False := by
    intro z hzl hzQ
    have he := hQD z hzQ (hls z hzl)
    exact hsep d.1
      (Eq.mp (congrArg (fun z : V => z ∈ l.support) he) hzl) r.start_mem_support
  have hPQ : ∀ z ∈ P.support, z ∈ Q.support → False := by
    intro z hzP hzQ
    exact Set.disjoint_left.mp hDis (hPS z hzP).1 (hQS z hzQ).1
  have hIJ : Disjoint (fragmentBlock I b) (fragmentBlock J c) :=
    Set.disjoint_left.mpr (fun _ hzI hzJ => Set.disjoint_left.mp hDis (hIB hzI) (hJB hzJ))
  have hlpath : l.IsPath := (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hL
  have hrpath : r.IsPath := (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hR
  refine ⟨I, J, b, c, hI, hJ, hIJ, P.append l, Q.append r,
    append_isPath_of_only_common_endpoint hP hlpath hPl,
    append_isPath_of_only_common_endpoint hQ hrpath hQr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hzI
    rcases (Walk.mem_support_append_iff P l).mp hz with hzP | hzl
    · exact (hPS z hzP).2 hzI
    · exact Set.disjoint_left.mp hEC (hIC hzI) (hls z hzl)
  · intro z hz hzJ
    rcases (Walk.mem_support_append_iff Q r).mp hz with hzQ | hzr
    · exact (hQS z hzQ).2 hzJ
    · exact Set.disjoint_left.mp hED (hJD hzJ) (hrs z hzr)
  · intro z hzU hzV
    rcases (Walk.mem_support_append_iff P l).mp hzU with hzP | hzl
    · rcases (Walk.mem_support_append_iff Q r).mp hzV with hzQ | hzr
      · exact hPQ z hzP hzQ
      · exact hPr z hzP hzr
    · rcases (Walk.mem_support_append_iff Q r).mp hzV with hzQ | hzr
      · exact hlQ z hzl hzQ
      · exact hsep z hzl hzr
  · intro z hz hzB
    rcases (Walk.mem_support_append_iff P l).mp hz with hzP | hzl
    · exact hPB z hzP hzB
    · rcases hzB with he | hzI
      · exact he
      · exact False.elim (Set.disjoint_left.mp hEC (hIC hzI) (hls z hzl))
  · intro z hz hzB
    rcases (Walk.mem_support_append_iff Q r).mp hz with hzQ | hzr
    · exact hQB z hzQ hzB
    · rcases hzB with he | hzJ
      · exact he
      · exact False.elim (Set.disjoint_left.mp hED (hJD hzJ) (hrs z hzr))
  · intro z hz hzB
    rcases (Walk.mem_support_append_iff P l).mp hz with hzP | hzl
    · exact Set.disjoint_left.mp hDis (hPS z hzP).1 (hJB hzB)
    · rcases hJB hzB with hzD | he
      · exact Set.disjoint_left.mp hED hzD (hls z hzl)
      · exact hsep d.1
          (Eq.mp (congrArg (fun z : V => z ∈ l.support) he) hzl) r.start_mem_support
  · intro z hz hzB
    rcases (Walk.mem_support_append_iff Q r).mp hz with hzQ | hzr
    · exact Set.disjoint_left.mp hDis (hIB hzB) (hQS z hzQ).1
    · rcases hIB hzB with hzC | he
      · exact Set.disjoint_left.mp hEC hzC (hrs z hzr)
      · exact hsep a.1 l.start_mem_support
          (Eq.mp (congrArg (fun z : V => z ∈ r.support) he) hzr)

/-- All central linkages are obtained internally; pair-unseparated is not
replaced by connectedness of every deletion of the whole original graph. -/
theorem terminal_routes_from_intrinsic_terminal_free_pair [Fintype V]
    (G : SimpleGraph V) (w y : V) (hwy : w ≠ y)
    (hG : G.Connected) (hV : 3 ≤ Fintype.card V)
    (hGw : (G.induce {v | v ≠ w}).Connected)
    (hGy : (G.induce {v | v ≠ y}).Connected)
    (hpair : ∀ (z : V) (hwz : w ≠ z) (hyz : y ≠ z),
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ =
        (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩)
    (hwavoid : ∀ I b, TerminalFragment G I b → w ∉ I)
    (hyavoid : ∀ I b, TerminalFragment G I b → y ∉ I) :
    TwoTerminalRoutes G w y := by
  classical
  obtain ⟨S, hS, iS, hTwo, _hGreat, C, D, hCD⟩ :=
    central_greatest_dual_attachment_carrier_exists G w y hwy hG hV hGw hGy
      hpair hwavoid hyavoid
  let : Fintype S := iS
  let wr : S := ⟨w, hS.1⟩
  let yr : S := ⟨y, hS.2.1⟩
  have hCD' : carrierAttachment G S hS.2.2 C ≠ carrierAttachment G S hS.2.2 D :=
    fun he => hCD (congrArg Subtype.val he)
  have hwy' : wr ≠ yr := fun he => hwy (congrArg Subtype.val he)
  rcases UnorderedLinkage.ordinary_two_connected_unordered_two_set_linkage
    (G.induce S) hTwo (carrierAttachment G S hS.2.2 C)
      (carrierAttachment G S hS.2.2 D) wr yr hCD' hwy' with h | h
  · obtain ⟨L, R, hL, hR, hLR⟩ := h
    exact carrier_terminal_routes_of_actual_central_paths G S hS.2.2 hG C D hCD wr yr
      L R hL hR hLR
  · obtain ⟨L, R, hL, hR, hLR⟩ := h
    exact carrier_terminal_routes_of_actual_central_paths G S hS.2.2 hG D C hCD.symm wr yr
      R L hR hL hLR.symm

#print axioms carrier_terminal_routes_of_actual_central_paths
#print axioms terminal_routes_from_intrinsic_terminal_free_pair
end TaskH.Gao
