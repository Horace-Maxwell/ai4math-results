import Research.TaskH.Gao.UnorderedLinkage.RootedTwoFan

/-! The actual fresh degree-two root, all its deletions, and removal of its spokes. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u}

def pairRootGraph (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj p q := match p, q with
    | none, none => False
    | none, some v => v = a ∨ v = b
    | some v, none => v = a ∨ v = b
    | some v, some w => G.Adj v w
  symm := by
    constructor
    intro p q h
    cases p <;> cases q
    · exact h
    · exact h
    · exact h
    · exact G.symm.symm _ _ h
  loopless := by
    constructor
    intro p
    cases p with
    | none => exact id
    | some v => exact G.loopless.irrefl v

def pairRootOldHom (G : SimpleGraph V) (a b : V) : G →g pairRootGraph G a b where
  toFun := Option.some
  map_rel' := by intro v w e; exact e

theorem pairRootGraph_two_connected [Fintype V] (G : SimpleGraph V) (a b : V)
    (hG : _root_.TaskH.Fan.TwoConnected G) (hab : a ≠ b) :
    _root_.TaskH.Fan.TwoConnected (pairRootGraph G a b) := by
  classical
  let K := pairRootGraph G a b
  let f := pairRootOldHom G a b
  have ha : K.Adj none (some a) := Or.inl rfl
  have hbase : ∀ z : Option V, K.Reachable none z := by
    intro z
    cases z with
    | none => exact SimpleGraph.Reachable.refl _
    | some z => exact ha.reachable.trans ((hG.2.1 a z).map f)
  have hconn : K.Connected := by
    refine { preconnected := ?_, nonempty := ⟨none⟩ }
    intro u v
    exact (hbase u).symm.trans (hbase v)
  refine ⟨?_, hconn, ?_⟩
  · have hc := hG.1
    simp only [Fintype.card_option]
    omega
  · intro z
    cases z with
    | none =>
      let f₀ : G →g K.induce {q | q ≠ none} := {
        toFun := fun v => ⟨some v, by simp⟩
        map_rel' := by intro v w e; exact e }
      have hsur : Function.Surjective f₀ := by
        rintro ⟨q, hq⟩
        cases q with
        | none => exact False.elim (hq rfl)
        | some v => exact ⟨v, rfl⟩
      exact hG.2.1.map f₀ hsur
    | some z =>
      obtain ⟨s, hs, hsz⟩ : ∃ s : V, (s = a ∨ s = b) ∧ s ≠ z := by
        by_cases haz : a = z
        · exact ⟨b, Or.inr rfl, by simpa only [← haz] using hab.symm⟩
        · exact ⟨a, Or.inl rfl, haz⟩
      let fz : (G.induce {v | v ≠ z}) →g K.induce {q | q ≠ some z} := {
        toFun := fun v => ⟨some v.val, fun he => v.property (Option.some.inj he)⟩
        map_rel' := by intro v w e; exact e }
      let o : {q : Option V // q ≠ some z} :=
        ⟨some s, fun he => hsz (Option.some.inj he)⟩
      let n : {q : Option V // q ≠ some z} := ⟨none, by simp⟩
      have hspoke : (K.induce {q | q ≠ some z}).Adj n o := hs
      have hreach : ∀ q : {q : Option V // q ≠ some z},
          (K.induce {q | q ≠ some z}).Reachable o q := by
        rintro ⟨q, hq⟩
        cases q with
        | none => exact hspoke.reachable.symm
        | some v =>
          have hvz : v ≠ z := fun he => hq (congrArg Option.some he)
          exact ((hG.2.2 z) ⟨s, hsz⟩ ⟨v, hvz⟩).map fz
      refine { preconnected := ?_, nonempty := ⟨o⟩ }
      intro u v
      exact (hreach u).symm.trans (hreach v)

def unrootVertex : {q : Option V // q ≠ none} → V
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some v, _⟩ => v

theorem some_unrootVertex (q : {q : Option V // q ≠ none}) :
    some (unrootVertex q) = q.val := by
  rcases q with ⟨q, hq⟩
  cases q with
  | none => exact False.elim (hq rfl)
  | some v => rfl

theorem unrootVertex_injective : Function.Injective (unrootVertex (V := V)) := by
  intro q r he
  apply Subtype.ext
  exact (some_unrootVertex q).symm.trans
    ((congrArg Option.some he).trans (some_unrootVertex r))

def pairRootProjection (G : SimpleGraph V) (a b : V) :
    (pairRootGraph G a b).induce {q | q ≠ none} →g G where
  toFun := unrootVertex
  map_rel' := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ e
    cases p with
    | none => exact False.elim (hp rfl)
    | some p =>
      cases q with
      | none => exact False.elim (hq rfl)
      | some q => exact e

/-- Only old-old actual edges survive; complete output support maps into the given tail. -/
theorem pairRoot_root_free_path (G : SimpleGraph V) (a b u v : V)
    (r : (pairRootGraph G a b).Walk (some u) (some v))
    (hr : r.IsPath) (hn : none ∉ r.support) :
    ∃ p : G.Walk u v, p.IsPath ∧ ∀ z ∈ p.support, some z ∈ r.support := by
  let T : Set (Option V) := {q | q ≠ none}
  have hT : ∀ z ∈ r.support, z ∈ T := by
    intro z hz he
    subst z
    exact hn hz
  let ri := r.induce T hT
  have hm : ri.map (SimpleGraph.Embedding.induce T).toHom = r := Walk.map_induce r hT
  have hri : ri.IsPath := Walk.IsPath.of_map (hm.symm ▸ hr)
  let f := pairRootProjection G a b
  have hf : Function.Injective f := unrootVertex_injective
  refine ⟨ri.map f, (Walk.isPath_map_iff_of_injective (f := f) hf).mpr hri, ?_⟩
  intro z hz
  change z ∈ (ri.map f).support at hz
  rw [Walk.support_map] at hz
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hz
  have hq' : q.val ∈ (ri.map (SimpleGraph.Embedding.induce T).toHom).support := by
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hm] at hq'
  have hes : some z = q.val := (congrArg Option.some he).symm.trans (some_unrootVertex q)
  rw [hes]
  exact hq'

/-- Delete the artificial first spoke of a real positive root arm. -/
theorem pairRoot_arm_to_original (G : SimpleGraph V) (a b v : V)
    (R : (pairRootGraph G a b).Walk none (some v)) (hR : R.IsPath) :
    ∃ s : V, (s = a ∨ s = b) ∧ ∃ p : G.Walk s v,
      p.IsPath ∧ ∀ z ∈ p.support, some z ∈ R.support := by
  have hne : (none : Option V) ≠ some v := by intro he; cases he
  obtain ⟨q, e, r, rfl⟩ := Walk.exists_eq_cons_of_ne hne R
  cases q with
  | none => exact False.elim e
  | some s =>
    have ht := (Walk.cons_isPath_iff e r).mp hR
    obtain ⟨p, hp, hsub⟩ := pairRoot_root_free_path G a b s v r ht.1 ht.2
    refine ⟨s, e, p, hp, ?_⟩
    intro z hz
    exact List.mem_cons_of_mem none (hsub z hz)
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.pairRootGraph
#print axioms TaskH.Gao.UnorderedLinkage.pairRootOldHom
#print axioms TaskH.Gao.UnorderedLinkage.pairRootGraph_two_connected
#print axioms TaskH.Gao.UnorderedLinkage.unrootVertex
#print axioms TaskH.Gao.UnorderedLinkage.some_unrootVertex
#print axioms TaskH.Gao.UnorderedLinkage.unrootVertex_injective
#print axioms TaskH.Gao.UnorderedLinkage.pairRootProjection
#print axioms TaskH.Gao.UnorderedLinkage.pairRoot_root_free_path
#print axioms TaskH.Gao.UnorderedLinkage.pairRoot_arm_to_original
