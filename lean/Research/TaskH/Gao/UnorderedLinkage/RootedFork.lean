import Research.TaskH.Gao.UnorderedLinkage.PathContact

/-! A real three-path fork is constructed internally from ordinary two-connectivity. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

def IsFork (S : Set V) {x c a b : V}
    (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ T.IsPath ∧ P.IsPath ∧ Q.IsPath ∧
    (∀ z ∈ T.support, z ∉ S) ∧ HitsOnly P S a ∧ HitsOnly Q S b ∧
    MeetsOnly T P c ∧ MeetsOnly T Q c ∧ MeetsOnly P Q c

theorem fork_swap (S : Set V) {x c a b : V}
    (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b) (hf : IsFork S T P Q) :
    IsFork S T Q P := by
  rcases hf with ⟨ha, hb, hab, hT, hP, hQ, hTS, hPS, hQS, hTP, hTQ, hPQ⟩
  refine ⟨hb, ha, hab.symm, hT, hQ, hP, hTS, hQS, hPS, hTQ, hTP, ?_⟩
  intro z hzQ hzP
  exact hPQ z hzP hzQ

/-- Actual ordinary two-connectivity supplies an actual fork, not a supplied branching oracle. -/
theorem ordinary_two_connected_fork_exists [Fintype V] (G : SimpleGraph V)
    (hG : _root_.TaskH.Fan.TwoConnected G) (x : V) (S : Set V)
    (hxS : x ∉ S) (hS : ∃ a ∈ S, ∃ b ∈ S, a ≠ b) :
    ∃ (c a b : V) (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b),
      IsFork S T P Q := by
  classical
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hS
  obtain ⟨U₀, hU₀⟩ := hG.2.1.exists_isPath x a₀
  obtain ⟨a, U, ha, hU, _, hUhit⟩ := first_contact U₀ hU₀ S ha₀
  obtain ⟨b', hb', hb'a⟩ : ∃ b' ∈ S, b' ≠ a := by
    by_cases he : a = a₀
    · exact ⟨b₀, hb₀, by simpa only [he] using hab₀.symm⟩
    · exact ⟨a₀, ha₀, fun h => he h.symm⟩
  have hxa : x ≠ a := by
    intro he
    apply hxS
    simpa only [he] using ha
  obtain ⟨R₀, hR₀, hR₀avoid⟩ := deleted_connected_path (hG.2.2 a) hxa hb'a
  obtain ⟨b, R, hb, hR, hRsub, hRhit⟩ := first_contact R₀ hR₀ S hb'
  have hRavoid : ∀ z ∈ R.support, z ≠ a := fun z hz => hR₀avoid z (hRsub hz)
  obtain ⟨c, Q, hcU, hQ, hQsub, hQhit⟩ :=
    last_contact R hR {z | z ∈ U.support} U.start_mem_support
  have hcS : c ∉ S := by
    intro hcs
    have he := hUhit c hcU hcs
    exact hRavoid c (hQsub Q.start_mem_support) he
  have hac : a ≠ c := by
    intro he
    apply hcS
    simpa only [he] using ha
  let T := U.takeUntil c hcU
  let P := U.dropUntil c hcU
  have haT : a ∉ T.support := Walk.endpoint_notMem_support_takeUntil hU hcU hac
  have hTS : ∀ z ∈ T.support, z ∉ S := by
    intro z hz hzs
    have he := hUhit z (U.support_takeUntil_subset_support hcU hz) hzs
    exact haT (Eq.mp (congrArg (fun w : V => w ∈ T.support) he) hz)
  have hab : a ≠ b := by
    exact (hRavoid b R.end_mem_support).symm
  refine ⟨c, a, b, T, P, Q, ha, hb, hab, hU.takeUntil hcU,
    hU.dropUntil hcU, hQ, hTS, ?_, ?_, split_meets_only U hU hcU, ?_, ?_⟩
  · intro z hz hzs
    exact hUhit z (U.support_dropUntil_subset_support hcU hz) hzs
  · intro z hz hzs
    exact hRhit z (hQsub hz) hzs
  · intro z hzT hzQ
    exact hQhit z hzQ (U.support_takeUntil_subset_support hcU hzT)
  · intro z hzP hzQ
    exact hQhit z hzQ (U.support_dropUntil_subset_support hcU hzP)
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.IsFork
#print axioms TaskH.Gao.UnorderedLinkage.fork_swap
#print axioms TaskH.Gao.UnorderedLinkage.ordinary_two_connected_fork_exists
