import Research.TaskH.Gao.G6ComponentAttachment

/-! A connected actual component with two roots: all deletion components have
an actual attachment to one root. This is a transparent local transport lemma. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {D W : Type u}

theorem g5_extension_rooted [Fintype W] (F : SimpleGraph D) (J : SimpleGraph W)
    (f : D → W) (U T : W) (hUT : U ≠ T)
    (hfi : Function.Injective f) (hfU : ∀ d, f d ≠ U) (hfT : ∀ d, f d ≠ T)
    (hf : ∀ {a b}, F.Adj a b → J.Adj (f a) (f b))
    (hcover : ∀ q, q = U ∨ q = T ∨ ∃ d, f d = q)
    (hF : F.Connected)
    (hU : ∃ d, J.Adj (f d) U) (hT : ∃ d, J.Adj (f d) T)
    (hcut : ∀ (z : D) (E : (F.induce {d | d ≠ z}).ConnectedComponent),
      ∃ (d : D) (hdz : d ≠ z), (⟨d, hdz⟩ : {d : D // d ≠ z}) ∈ E.supp ∧
        (J.Adj (f d) U ∨ J.Adj (f d) T)) :
    RootedTwoConnected J U T := by
  classical
  let K := J ⊔ SimpleGraph.edge U T
  have eUT : K.Adj U T := by
    right
    exact (SimpleGraph.edge_adj U T U T).mpr ⟨Or.inl ⟨rfl, rfl⟩, hUT⟩
  let fm : F →g K := { toFun := f, map_rel' := fun e => Or.inl (hf e) }
  obtain ⟨a, eaU⟩ := hU
  obtain ⟨b, ebT⟩ := hT
  have hto : ∀ q, K.Reachable q U := by
    intro q
    rcases hcover q with rfl | rfl | ⟨d, rfl⟩
    · exact Reachable.rfl
    · exact eUT.symm.reachable
    · exact ((hF d a).map fm).trans (show K.Adj (f a) U from Or.inl eaU).reachable
  have hconn : K.Connected := by
    refine { preconnected := ?_, nonempty := ⟨U⟩ }
    intro p q
    exact (hto p).trans (hto q).symm
  have hcard : 3 ≤ Fintype.card W :=
    Fintype.two_lt_card_iff.mpr ⟨U, T, f a, hUT, (hfU a).symm, (hfT a).symm⟩
  refine ⟨hUT, hcard, hconn, ?_⟩
  intro r
  let L := K.induce {q | q ≠ r}
  rcases hcover r with hr | hr | ⟨z, hr⟩
  · subst r
    let t : {q : W // q ≠ U} := ⟨T, hUT.symm⟩
    let m : F →g L := {
      toFun := fun d => ⟨f d, hfU d⟩
      map_rel' := fun e => Or.inl (hf e) }
    have ht : ∀ q : {q : W // q ≠ U}, L.Reachable q t := by
      intro q
      rcases hcover q.1 with he | he | ⟨d, hd⟩
      · exact False.elim (q.2 he)
      · have he' : q = t := Subtype.ext he
        exact Eq.mpr (congrArg (fun v => L.Reachable v t) he') Reachable.rfl
      · have he' : m d = q := Subtype.ext hd
        have em : L.Adj (m b) t := Or.inl ebT
        exact Eq.mp (congrArg (fun v => L.Reachable v t) he') (((hF d b).map m).trans em.reachable)
    refine { preconnected := ?_, nonempty := ⟨t⟩ }
    intro p q
    exact (ht p).trans (ht q).symm
  · subst r
    let u : {q : W // q ≠ T} := ⟨U, hUT⟩
    let m : F →g L := {
      toFun := fun d => ⟨f d, hfT d⟩
      map_rel' := fun e => Or.inl (hf e) }
    have ht : ∀ q : {q : W // q ≠ T}, L.Reachable q u := by
      intro q
      rcases hcover q.1 with he | he | ⟨d, hd⟩
      · have he' : q = u := Subtype.ext he
        exact Eq.mpr (congrArg (fun v => L.Reachable v u) he') Reachable.rfl
      · exact False.elim (q.2 he)
      · have he' : m d = q := Subtype.ext hd
        have em : L.Adj (m a) u := Or.inl eaU
        exact Eq.mp (congrArg (fun v => L.Reachable v u) he') (((hF d a).map m).trans em.reachable)
    refine { preconnected := ?_, nonempty := ⟨u⟩ }
    intro p q
    exact (ht p).trans (ht q).symm
  · subst r
    let u : {q : W // q ≠ f z} := ⟨U, (hfU z).symm⟩
    let t : {q : W // q ≠ f z} := ⟨T, (hfT z).symm⟩
    have eut : L.Adj u t := eUT
    let m : (F.induce {d | d ≠ z}) →g L := {
      toFun := fun d => ⟨f d.1, fun he => d.2 (hfi he)⟩
      map_rel' := fun e => Or.inl (hf e) }
    have ht : ∀ q : {q : W // q ≠ f z}, L.Reachable q u := by
      intro q
      rcases hcover q.1 with he | he | ⟨d, hd⟩
      · have he' : q = u := Subtype.ext he
        exact Eq.mpr (congrArg (fun v => L.Reachable v u) he') Reachable.rfl
      · have he' : q = t := Subtype.ext he
        exact Eq.mpr (congrArg (fun v => L.Reachable v u) he') eut.symm.reachable
      · have hdz : d ≠ z := fun he => q.2 (hd.symm.trans (congrArg f he))
        let E := (F.induce {d | d ≠ z}).connectedComponentMk ⟨d, hdz⟩
        obtain ⟨c, hcz, hcE, ec⟩ := hcut z E
        have hr : L.Reachable (m ⟨d, hdz⟩) (m ⟨c, hcz⟩) :=
          (E.reachable_of_mem_supp rfl hcE).map m
        have he' : m ⟨d, hdz⟩ = q := Subtype.ext hd
        have hend : L.Reachable (m ⟨c, hcz⟩) u := by
          rcases ec with ec | ec
          · exact (show L.Adj (m ⟨c, hcz⟩) u from Or.inl ec).reachable
          · exact (show L.Adj (m ⟨c, hcz⟩) t from Or.inl ec).reachable.trans eut.symm.reachable
        exact Eq.mp (congrArg (fun v => L.Reachable v u) he') (hr.trans hend)
    refine { preconnected := ?_, nonempty := ⟨u⟩ }
    intro p q
    exact (ht p).trans (ht q).symm

#print axioms g5_extension_rooted
end TaskH.Gao
