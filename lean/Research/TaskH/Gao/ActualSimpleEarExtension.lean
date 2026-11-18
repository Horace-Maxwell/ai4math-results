import Research.TaskH.Gao.CarrierAttachments
import Research.TaskH.Gao.PathConcatenation
import Research.TaskH.Gao.ActualSetCrossing

/-! A genuine simple external ear enlarges an actual ordinary two-connected
vertex carrier. Every deleted-point connection is constructed in the original graph. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem simple_ear_point_reaches_retained_core (G : SimpleGraph V)
    (S : Set V) (a b : V) (ha : a ∈ S) (hb : b ∈ S)
    (p : G.Walk a b) (hp : p.IsPath) (z t : V)
    (ht : t ∈ S ∪ {v | v ∈ p.support}) (htz : t ≠ z) :
    ∃ (r : V) (hrS : r ∈ S) (hrz : r ≠ z),
      (G.induce ((S ∪ {v | v ∈ p.support}) \ {z})).Reachable
        ⟨t, ht, htz⟩ ⟨r, Or.inl hrS, hrz⟩ := by
  classical
  rcases ht with htS | htp
  · exact ⟨t, htS, htz, Reachable.rfl⟩
  · let q := p.takeUntil t htp
    let r := p.dropUntil t htp
    have hsplit : (q.append r).IsPath := by
      change ((p.takeUntil t htp).append (p.dropUntil t htp)).IsPath
      rw [Walk.take_spec]
      exact hp
    have hqsub : ∀ v ∈ q.support, v ∈ p.support := p.support_takeUntil_subset_support htp
    have hrsub : ∀ v ∈ r.support, v ∈ p.support := p.support_dropUntil_subset_support htp
    by_cases hzq : z ∈ q.support
    · have hzr : z ∉ r.support := by
        intro hz
        exact (hsplit.ne_of_mem_support_of_append (Ne.symm htz) hzq hz) rfl
      have hbz : b ≠ z := fun he => hzr
        (Eq.mp (congrArg (fun v : V => v ∈ r.support) he) r.end_mem_support)
      have hs : ∀ v ∈ r.support, v ∈ (S ∪ {v | v ∈ p.support}) \ {z} := by
        intro v hv
        exact ⟨Or.inr (hrsub v hv), fun he => hzr
          (Eq.mp (congrArg (fun v : V => v ∈ r.support) he) hv)⟩
      exact ⟨b, hb, hbz, ⟨r.induce _ hs⟩⟩
    · have haz : a ≠ z := fun he => hzq
        (Eq.mp (congrArg (fun v : V => v ∈ q.support) he) q.start_mem_support)
      have hs : ∀ v ∈ q.reverse.support, v ∈ (S ∪ {v | v ∈ p.support}) \ {z} := by
        intro v hv
        have hvq : v ∈ q.support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using hv
        exact ⟨Or.inr (hqsub v hvq), fun he => hzq
          (Eq.mp (congrArg (fun v : V => v ∈ q.support) he) hvq)⟩
      exact ⟨a, ha, haz, ⟨q.reverse.induce _ hs⟩⟩

theorem twoConnected_union_simple_ear [Fintype V] (G : SimpleGraph V)
    (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S))
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) :
    ∃ iT : Fintype (S ∪ {v | v ∈ p.support} : Set V),
      @TwoConnected (S ∪ {v | v ∈ p.support} : Set V) iT
        (G.induce (S ∪ {v | v ∈ p.support})) := by
  classical
  let T : Set V := S ∪ {v | v ∈ p.support}
  let iT : Fintype T := Fintype.ofFinite _
  let f : S → T := fun v => ⟨v.1, Or.inl v.2⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun v : T => v.1) he)
  have hcard : 3 ≤ @Fintype.card T iT := hS.1.trans (Fintype.card_le_of_injective f hf)
  have hdeleted : ∀ z : V, (G.induce (S \ {z})).Connected := by
    intro z
    by_cases hzS : z ∈ S
    · let zr : S := ⟨z, hzS⟩
      let e : ((G.induce S).induce {v : S | v ≠ zr}) →g G.induce (S \ {z}) :=
        { toFun := fun v => ⟨v.1.1, v.1.2, fun he => v.2 (Subtype.ext he)⟩
          map_rel' := fun e => e }
      have he : Function.Surjective e := by
        intro v
        exact ⟨⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (congrArg Subtype.val h)⟩, Subtype.ext rfl⟩
      exact Connected.map e he (hS.2.2 zr)
    · let e : G.induce S →g G.induce (S \ {z}) :=
        { toFun := fun v => ⟨v.1, v.2, fun he => hzS
            (Eq.mp (congrArg (fun v : V => v ∈ S) he) v.2)⟩
          map_rel' := fun e => e }
      have he : Function.Surjective e := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext rfl⟩
      exact Connected.map e he hS.2.1
  have hflat : ∀ z : V, (G.induce (T \ {z})).Connected := by
    intro z
    have hex : ∃ r : V, r ∈ S ∧ r ≠ z := by
      by_cases haz : a = z
      · exact ⟨b, hb, fun he => hab (haz.trans he.symm)⟩
      · exact ⟨a, ha, haz⟩
    obtain ⟨r, hrS, hrz⟩ := hex
    refine { preconnected := ?_, nonempty := ⟨⟨r, Or.inl hrS, hrz⟩⟩ }
    intro v w
    obtain ⟨c, hcS, hcz, hv⟩ := simple_ear_point_reaches_retained_core G S a b ha hb p hp z v.1 v.2.1 v.2.2
    obtain ⟨d, hdS, hdz, hw⟩ := simple_ear_point_reaches_retained_core G S a b ha hb p hp z w.1 w.2.1 w.2.2
    let e : G.induce (S \ {z}) →g G.induce (T \ {z}) :=
      { toFun := fun q => ⟨q.1, Or.inl q.2.1, q.2.2⟩
        map_rel' := fun e => e }
    have hm := ((hdeleted z) ⟨c, hcS, hcz⟩ ⟨d, hdS, hdz⟩).map e
    exact hv.trans (hm.trans hw.symm)
  have hconn : (G.induce T).Connected := by
    let ar : T := ⟨a, Or.inl ha⟩
    let br : T := ⟨b, Or.inl hb⟩
    refine { preconnected := ?_, nonempty := ⟨ar⟩ }
    intro v w
    by_cases hva : v.1 = a
    · by_cases hwa : w.1 = a
      · have hv : v = ar := Subtype.ext hva
        have hw : w = ar := Subtype.ext hwa
        subst v; subst w; exact Reachable.rfl
      · have hwb : w.1 ≠ a := hwa
        have hba : b ≠ a := hab.symm
        have hvb : (G.induce T).Reachable ar br := by
          let e : G.induce S →g G.induce T := (G.induceHomOfLE Set.subset_union_left).toHom
          exact (hS.2.1 ⟨a, ha⟩ ⟨b, hb⟩).map e
        let e : G.induce (T \ {a}) →g G.induce T :=
          { toFun := fun q => ⟨q.1, q.2.1⟩, map_rel' := fun e => e }
        have hbw := ((hflat a) ⟨b, Or.inl hb, hba⟩ ⟨w.1, w.2, hwb⟩).map e
        have hv : v = ar := Subtype.ext hva
        subst v; exact hvb.trans hbw
    · by_cases hwa : w.1 = a
      · have hvb : (G.induce T).Reachable v br := by
          let e : G.induce (T \ {a}) →g G.induce T :=
            { toFun := fun q => ⟨q.1, q.2.1⟩, map_rel' := fun e => e }
          exact ((hflat a) ⟨v.1, v.2, hva⟩ ⟨b, Or.inl hb, hab.symm⟩).map e
        let e : G.induce S →g G.induce T :=
          { toFun := fun q => ⟨q.1, Or.inl q.2⟩, map_rel' := fun e => e }
        have hba := (hS.2.1 ⟨b, hb⟩ ⟨a, ha⟩).map e
        have hw : w = ar := Subtype.ext hwa
        subst w; exact hvb.trans hba
      · let e : G.induce (T \ {a}) →g G.induce T :=
          { toFun := fun q => ⟨q.1, q.2.1⟩, map_rel' := fun e => e }
        exact ((hflat a) ⟨v.1, v.2, hva⟩ ⟨w.1, w.2, hwa⟩).map e
  refine ⟨iT, hcard, hconn, ?_⟩
  intro z
  let e : G.induce (T \ {z.1}) ≃g (G.induce T).induce {v : T | v ≠ z} :=
    { toEquiv := {
        toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun he => v.2.2 (congrArg Subtype.val he)⟩
        invFun := fun v => ⟨v.1.1, v.1.2, fun he => v.2 (Subtype.ext he)⟩
        left_inv := by intro v; exact Subtype.ext rfl
        right_inv := by intro v; exact Subtype.ext (Subtype.ext rfl) }
      map_rel_iff' := by intro v w; rfl }
  exact e.connected_iff.mp (hflat z.1)

#print axioms simple_ear_point_reaches_retained_core
#print axioms twoConnected_union_simple_ear
end TaskH.Gao
