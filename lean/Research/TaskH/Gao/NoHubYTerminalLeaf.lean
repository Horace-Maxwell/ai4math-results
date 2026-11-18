import Research.TaskH.Gao.TerminalRegionSeparation
import Research.TaskH.Gao.ActualQualifiedRouteHub

/-! A genuine nontrivial y-terminal block is an intrinsic qualified route hub.
The simple path and its two distinct core points are constructed internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem terminal_noncut_external_point_outside_block
    (G : SimpleGraph V) (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (y q : V) (hyI : y ∉ I) (hqy : q ≠ y) (hqI : q ∉ I)
    (hyNoncut : (G.induce {v | v ≠ y}).Connected) : y ∉ fragmentBlock I b := by
  rintro (hyb | hyI')
  · obtain ⟨r, hrI⟩ := hI.1
    have hrb : r ≠ b := fun he => hI.2.1
      (Eq.mp (congrArg (fun v : V => v ∈ I) he) hrI)
    have hqb : q ≠ b := fun he => hqy (he.trans hyb.symm)
    have hdel : (G.induce {v | v ≠ b}).Connected :=
      Eq.mp (congrArg (fun z : V => (G.induce {v | v ≠ z}).Connected) hyb) hyNoncut
    obtain ⟨p⟩ := hdel ⟨r, hrb⟩ ⟨q, hqb⟩
    exact hqI (terminal_walk_stays_without_boundary G I b hI p hrI)
  · exact hyI hyI'

theorem nontrivial_y_terminal_actual_qualified_hub [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (J : Set V) (bt y : V) (hJ : TerminalFragment G J bt)
    (hyJ : y ∈ J) (hyB : y ∉ fragmentBlock I b) (hJ2 : 2 ≤ J.ncard) :
    ActualQualifiedRouteHub G I b y (fragmentBlock J bt) := by
  classical
  let S : Set V := fragmentBlock J bt
  let : Fintype S := Fintype.ofFinite _
  have hS : TwoConnected (G.induce S) := terminalFragment_twoConnected G J bt hJ hJ2
  have hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S := by
    intro T iT hST hT
    exact @terminal_block_inclusion_maximal V _ G J bt hJ T iT hT hST
  have hne : S ≠ fragmentBlock I b := by
    intro he
    have hyS : y ∈ S := Or.inr hyJ
    exact hyB (Eq.mp (congrArg (fun T : Set V => y ∈ T) he) hyS)
  have hcut : S ∩ {z | ¬(G.induce {v | v ≠ z}).Connected} ⊆ ({bt} : Set V) := by
    rintro z ⟨hzS, hzCut⟩
    rcases hzS with he | hzJ
    · exact he
    · have hzNoncut : (G.induce {v | v ≠ z}).Connected := by
        rcases hJ with ⟨_hne, _hbt, _hclosed, _hJC, _hcomp, _hBC, hglobal, _hdel⟩
        exact hglobal z hzJ
      exact False.elim (hzCut hzNoncut)
  have hcap : (S ∩ {z | ¬(G.induce {v | v ≠ z}).Connected}).ncard ≤ 2 := by
    have hc := Set.ncard_le_ncard hcut
    rw [Set.ncard_singleton] at hc
    omega
  have hdis : Disjoint S I := terminal_twoConnected_region_avoids_interior
    G I b hI S hS y (Or.inr hyJ) hyB
  obtain ⟨r, hrI⟩ := hI.1
  have hrS : r ∉ S := fun hr => Set.disjoint_left.mp hdis hr hrI
  obtain ⟨p, hp⟩ := hG.exists_isPath r y
  have hybt : y ≠ bt := fun he => hJ.2.1
    (Eq.mp (congrArg (fun v : V => v ∈ J) he) hyJ)
  have hrbt : r ≠ bt := fun he => hrS (Or.inl he)
  have hbtMem : bt ∈ p.support := by
    by_contra hn
    have hs : ∀ z ∈ p.reverse.support, z ≠ bt := by
      intro z hz he
      have hzP : z ∈ p.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hz
      exact hn (Eq.mp (congrArg (fun z : V => z ∈ p.support) he) hzP)
    let q : (G.induce {v | v ≠ bt}).Walk ⟨y, hybt⟩ ⟨r, hrbt⟩ :=
      p.reverse.induce {v | v ≠ bt} hs
    exact hrS (Or.inr (terminal_walk_stays_without_boundary G J bt hJ q hyJ))
  refine ⟨⟨inferInstance, hS⟩, hmax, hne, hcap, r, hrI, p, hp,
    bt, Or.inl rfl, y, Or.inr hyJ, hybt.symm, hbtMem, p.end_mem_support⟩

theorem no_actual_qualified_hub_y_terminal_singleton [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (J : Set V) (bt y : V) (hJ : TerminalFragment G J bt)
    (hyJ : y ∈ J) (hyB : y ∉ fragmentBlock I b)
    (hnoHub : ¬∃ S : Set V, ActualQualifiedRouteHub G I b y S) :
    J = {y} ∧ G.neighborSet y = {bt} ∧ G.Adj y bt := by
  classical
  have hn2 : ¬2 ≤ J.ncard := by
    intro hJ2
    exact hnoHub ⟨fragmentBlock J bt,
      nontrivial_y_terminal_actual_qualified_hub G hG I b hI J bt y hJ hyJ hyB hJ2⟩
  have hp : 0 < J.ncard := (Set.ncard_pos (Set.toFinite J)).mpr hJ.1
  have hone : J.ncard = 1 := by omega
  obtain ⟨a, hJa⟩ := Set.ncard_eq_one.mp hone
  have hya : y = a := by
    rw [hJa] at hyJ
    exact hyJ
  have hJy : J = {y} := hJa.trans (congrArg (fun z : V => ({z} : Set V)) hya.symm)
  have hOne : TerminalFragment G {y} bt :=
    Eq.mp (congrArg (fun L : Set V => TerminalFragment G L bt) hJy) hJ
  obtain ⟨eyb, _hbridge, hNy, _hBlock⟩ := terminalFragment_singleton_bridge G y bt hG hOne
  exact ⟨hJy, hNy, eyb⟩

#print axioms terminal_noncut_external_point_outside_block
#print axioms nontrivial_y_terminal_actual_qualified_hub
#print axioms no_actual_qualified_hub_y_terminal_singleton
end TaskH.Gao
