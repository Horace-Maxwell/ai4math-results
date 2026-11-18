import Research.TaskH.Gao.UnorderedLinkage.RootedFork

/-! Strict actual trunk shortening, with every complete support intersection checked. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

/-- Rerouting at an actual old left-arm contact; endpoint order is not prescribed. -/
theorem fork_reroute_left [DecidableEq V] (S : Set V) {x c a b d t : V}
    (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b) (hf : IsFork S T P Q)
    (E : G.Walk d t) (hE : E.IsPath) (hd : d ∈ T.support)
    (hET : MeetsOnly E T d) (hES : HitsOnly E S t)
    (hEP : MeetsOnly E P t) (hEQ : MeetsOnly E Q t)
    (hEc : c ∉ E.support) (ht : t ∈ P.support) :
    ∃ (L : G.Walk x d) (A : G.Walk d a) (B : G.Walk d b),
      IsFork S L A B ∧ L.length < T.length := by
  rcases hf with ⟨ha, hb, hab, hT, hP, hQ, hTS, hPS, hQS, hTP, hTQ, hPQ⟩
  have hdc : d ≠ c := by
    intro he
    apply hEc
    simpa only [he] using E.start_mem_support
  have htc : t ≠ c := by
    intro he
    apply hEc
    simpa only [he] using E.end_mem_support
  let L := T.takeUntil d hd
  let D := T.dropUntil d hd
  let U := P.dropUntil t ht
  have hL := hT.takeUntil hd
  have hD := hT.dropUntil hd
  have hU := hP.dropUntil ht
  have hcL : c ∉ L.support := Walk.endpoint_notMem_support_takeUntil hT hd hdc.symm
  have hcU : c ∉ U.support := start_not_in_tail P hP ht htc
  have hEU : (E.append U).IsPath :=
    _root_.TaskH.Fan.isPath_append_of_support_intersection E U hE hU
      (fun z hzE hzU => hEP z hzE (P.support_dropUntil_subset_support ht hzU))
  have hDQ : (D.append Q).IsPath :=
    _root_.TaskH.Fan.isPath_append_of_support_intersection D Q hD hQ
      (fun z hzD hzQ => hTQ z (T.support_dropUntil_subset_support hd hzD) hzQ)
  refine ⟨L, E.append U, D.append Q, ?_, T.length_takeUntil_lt_length hd hdc⟩
  refine ⟨ha, hb, hab, hL, hEU, hDQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hzL
    exact hTS z (T.support_takeUntil_subset_support hd hzL)
  · intro z hz hzs
    rcases (Walk.mem_support_append_iff E U).mp hz with hzE | hzU
    · have he := hES z hzE hzs
      have hzP : z ∈ P.support := by rw [he]; exact ht
      exact hPS z hzP hzs
    · exact hPS z (P.support_dropUntil_subset_support ht hzU) hzs
  · intro z hz hzs
    rcases (Walk.mem_support_append_iff D Q).mp hz with hzD | hzQ
    · exact False.elim (hTS z (T.support_dropUntil_subset_support hd hzD) hzs)
    · exact hQS z hzQ hzs
  · intro z hzL hz
    rcases (Walk.mem_support_append_iff E U).mp hz with hzE | hzU
    · exact hET z hzE (T.support_takeUntil_subset_support hd hzL)
    · have he := hTP z (T.support_takeUntil_subset_support hd hzL)
        (P.support_dropUntil_subset_support ht hzU)
      subst z
      exact False.elim (hcL hzL)
  · intro z hzL hz
    rcases (Walk.mem_support_append_iff D Q).mp hz with hzD | hzQ
    · exact split_meets_only T hT hd z hzL hzD
    · have he := hTQ z (T.support_takeUntil_subset_support hd hzL) hzQ
      subst z
      exact False.elim (hcL hzL)
  · intro z hzA hzB
    rcases (Walk.mem_support_append_iff E U).mp hzA with hzE | hzU
    · rcases (Walk.mem_support_append_iff D Q).mp hzB with hzD | hzQ
      · exact hET z hzE (T.support_dropUntil_subset_support hd hzD)
      · have he := hEQ z hzE hzQ
        have hzP : z ∈ P.support := by rw [he]; exact ht
        have hzc := hPQ z hzP hzQ
        have hcE : c ∈ E.support :=
          Eq.mp (congrArg (fun w : V => w ∈ E.support) hzc) hzE
        exact False.elim (hEc hcE)
    · rcases (Walk.mem_support_append_iff D Q).mp hzB with hzD | hzQ
      · have he := hTP z (T.support_dropUntil_subset_support hd hzD)
          (P.support_dropUntil_subset_support ht hzU)
        subst z
        exact False.elim (hcU hzU)
      · have he := hPQ z (P.support_dropUntil_subset_support ht hzU) hzQ
        subst z
        exact False.elim (hcU hzU)

/-- Rerouting when the new contact belongs to the target set but not the old left arm. -/
theorem fork_reroute_fresh [DecidableEq V] (S : Set V) {x c a b d t : V}
    (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b) (hf : IsFork S T P Q)
    (E : G.Walk d t) (hE : E.IsPath) (hd : d ∈ T.support)
    (hET : MeetsOnly E T d) (hES : HitsOnly E S t)
    (hEP : MeetsOnly E P t) (hEc : c ∉ E.support)
    (htS : t ∈ S) (htP : t ∉ P.support) :
    ∃ (L : G.Walk x d) (A : G.Walk d t) (B : G.Walk d a),
      IsFork S L A B ∧ L.length < T.length := by
  rcases hf with ⟨ha, _, _, hT, hP, _, hTS, hPS, _, hTP, _, _⟩
  have hdc : d ≠ c := by
    intro he
    apply hEc
    simpa only [he] using E.start_mem_support
  let L := T.takeUntil d hd
  let D := T.dropUntil d hd
  have hL := hT.takeUntil hd
  have hD := hT.dropUntil hd
  have hcL : c ∉ L.support := Walk.endpoint_notMem_support_takeUntil hT hd hdc.symm
  have hDP : (D.append P).IsPath :=
    _root_.TaskH.Fan.isPath_append_of_support_intersection D P hD hP
      (fun z hzD hzP => hTP z (T.support_dropUntil_subset_support hd hzD) hzP)
  have hta : t ≠ a := by
    intro he
    apply htP
    simpa only [he] using P.end_mem_support
  refine ⟨L, E, D.append P, ?_, T.length_takeUntil_lt_length hd hdc⟩
  refine ⟨htS, ha, hta, hL, hE, hDP, ?_, hES, ?_, ?_, ?_, ?_⟩
  · intro z hzL
    exact hTS z (T.support_takeUntil_subset_support hd hzL)
  · intro z hz hzs
    rcases (Walk.mem_support_append_iff D P).mp hz with hzD | hzP
    · exact False.elim (hTS z (T.support_dropUntil_subset_support hd hzD) hzs)
    · exact hPS z hzP hzs
  · intro z hzL hzE
    exact hET z hzE (T.support_takeUntil_subset_support hd hzL)
  · intro z hzL hz
    rcases (Walk.mem_support_append_iff D P).mp hz with hzD | hzP
    · exact split_meets_only T hT hd z hzL hzD
    · have he := hTP z (T.support_takeUntil_subset_support hd hzL) hzP
      subst z
      exact False.elim (hcL hzL)
  · intro z hzE hz
    rcases (Walk.mem_support_append_iff D P).mp hz with hzD | hzP
    · exact hET z hzE (T.support_dropUntil_subset_support hd hzD)
    · have he := hEP z hzE hzP
      subst z
      exact False.elim (htP hzP)

/-- A branch different from the actual root admits a strictly shorter actual fork. -/
theorem ordinary_fork_strict_reduction [Fintype V] (G : SimpleGraph V)
    (hG : _root_.TaskH.Fan.TwoConnected G) (S : Set V) {x c a b : V}
    (T : G.Walk x c) (P : G.Walk c a) (Q : G.Walk c b)
    (hf : IsFork S T P Q) (hcx : c ≠ x) :
    ∃ (d a' b' : V) (L : G.Walk x d) (A : G.Walk d a') (B : G.Walk d b'),
      IsFork S L A B ∧ L.length < T.length := by
  classical
  have hfSaved := hf
  obtain ⟨ha, _, _, _, _, _, hTS, _, _, _, _, _⟩ := hf
  have hcS : c ∉ S := hTS c T.end_mem_support
  have hac : a ≠ c := by
    intro he
    apply hcS
    simpa only [he] using ha
  let W : Set V := S ∪ {z | z ≠ c ∧ (z ∈ P.support ∨ z ∈ Q.support)}
  obtain ⟨R₀, hR₀, hR₀avoid⟩ := deleted_connected_path (hG.2.2 c) hcx.symm hac
  have haW : a ∈ W := Or.inl ha
  obtain ⟨t, R, htW, hR, hRsub, hRhit⟩ := first_contact R₀ hR₀ W haW
  obtain ⟨d, E, hd, hE, hEsub, hEhit⟩ :=
    last_contact R hR {z | z ∈ T.support} T.start_mem_support
  have hEc : c ∉ E.support := by
    intro hcE
    exact hR₀avoid c (hRsub (hEsub hcE)) rfl
  have hET : MeetsOnly E T d := hEhit
  have hES : HitsOnly E S t := by
    intro z hzE hzS
    exact hRhit z (hEsub hzE) (Or.inl hzS)
  have hEP : MeetsOnly E P t := by
    intro z hzE hzP
    have hzc : z ≠ c := by
      intro he
      apply hEc
      simpa only [he] using hzE
    exact hRhit z (hEsub hzE) (Or.inr ⟨hzc, Or.inl hzP⟩)
  have hEQ : MeetsOnly E Q t := by
    intro z hzE hzQ
    have hzc : z ≠ c := by
      intro he
      apply hEc
      simpa only [he] using hzE
    exact hRhit z (hEsub hzE) (Or.inr ⟨hzc, Or.inr hzQ⟩)
  by_cases htP : t ∈ P.support
  · obtain ⟨L, A, B, hnew, hshort⟩ := fork_reroute_left S T P Q hfSaved E hE hd
      hET hES hEP hEQ hEc htP
    exact ⟨d, a, b, L, A, B, hnew, hshort⟩
  by_cases htQ : t ∈ Q.support
  · obtain ⟨L, A, B, hnew, hshort⟩ := fork_reroute_left S T Q P
      (fork_swap S T P Q hfSaved) E hE hd hET hES hEQ hEP hEc htQ
    exact ⟨d, b, a, L, A, B, hnew, hshort⟩
  have htS : t ∈ S := by
    rcases htW with htS | ⟨_, htP' | htQ'⟩
    · exact htS
    · exact False.elim (htP htP')
    · exact False.elim (htQ htQ')
  obtain ⟨L, A, B, hnew, hshort⟩ := fork_reroute_fresh S T P Q hfSaved E hE hd
    hET hES hEP hEc htS htP
  exact ⟨d, t, a, L, A, B, hnew, hshort⟩
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.fork_reroute_left
#print axioms TaskH.Gao.UnorderedLinkage.fork_reroute_fresh
#print axioms TaskH.Gao.UnorderedLinkage.ordinary_fork_strict_reduction
