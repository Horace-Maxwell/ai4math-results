import Research.TaskH.Fan.Identification

/-!
Actual arbitrary simple-path lifting from the one-root identification graph.
The only inverse graph map is on the induced exterior, where it is injective.
The collapsed vertex map itself is never treated as a graph homomorphism.
Independent quotient paths may lift to different actual boundary start vertices.
-/
set_option autoImplicit false

universe u

namespace TaskH.Fan

open SimpleGraph

variable {V : Type u}

/-- Removing the sole fresh root leaves exactly the separately tagged outside vertices. -/
def identificationExteriorValue (S : Set V)
    (a : {o : IdentificationVertex S // o ≠ none}) : {v : V // v ∉ S} :=
  match a with
  | ⟨none, h⟩ => (h rfl).elim
  | ⟨some v, _h⟩ => v

@[simp]
theorem identificationExteriorValue_some (S : Set V) (v : {a : V // a ∉ S})
    (h : (some v : IdentificationVertex S) ≠ none) :
    identificationExteriorValue S ⟨some v, h⟩ = v :=
  rfl

/-- This inverse on the actual exterior is injective, unlike the collapsed vertex map. -/
theorem identificationExteriorValue_injective (S : Set V) :
    Function.Injective (identificationExteriorValue S) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab' : a = b := hab
      apply Subtype.ext
      exact congrArg Option.some hab'

/-- A real graph map only from the root-deleted identification graph to the exterior. -/
def identificationExteriorHom (G : SimpleGraph V) (S : Set V) :
    (identificationGraph G S).induce {o : IdentificationVertex S | o ≠ none} →g
      G.induce {v : V | v ∉ S} where
  toFun := identificationExteriorValue S
  map_rel' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    cases a with
    | none => exact (ha rfl).elim
    | some a =>
      cases b with
      | none => exact (hb rfl).elim
      | some b =>
        change G.Adj a.1 b.1
        exact hab

/-- Every actual root-avoiding simple quotient path becomes a same-length exterior path. -/
theorem identification_exterior_path (G : SimpleGraph V) (S : Set V)
    (u v : {a : V // a ∉ S})
    (p : (identificationGraph G S).Walk (some u) (some v))
    (hp : p.IsPath) (hn : none ∉ p.support) :
    ∃ q : (G.induce {a : V | a ∉ S}).Walk u v,
      q.IsPath ∧ q.length = p.length := by
  let A : Set (IdentificationVertex S) := {o | o ≠ none}
  have hA : ∀ o ∈ p.support, o ∈ A := by
    intro o ho
    change o ≠ none
    intro he
    subst o
    exact hn ho
  let pi := p.induce A hA
  have hm : pi.map (SimpleGraph.Embedding.induce A).toHom = p :=
    Walk.map_induce p hA
  have hpi_map : (pi.map (SimpleGraph.Embedding.induce A).toHom).IsPath :=
    hm.symm ▸ hp
  have hpi : pi.IsPath := Walk.IsPath.of_map hpi_map
  let f := identificationExteriorHom G S
  have hf : Function.Injective f := identificationExteriorValue_injective S
  refine ⟨pi.map f, (Walk.isPath_map_iff_of_injective (f := f) hf).mpr hpi, ?_⟩
  have hm_length := congrArg
    (fun r : (identificationGraph G S).Walk (some u) (some v) => r.length) hm
  have hlen : pi.length = p.length :=
    (Walk.length_map (p := pi) (f := (SimpleGraph.Embedding.induce A).toHom)).symm.trans
      hm_length
  exact (Walk.length_map (p := pi) (f := f)).trans hlen

/-- An arbitrary simple fresh-root path has one genuine spoke and an entire root-free tail. -/
theorem identification_path_first_spoke (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S})
    (p : (identificationGraph G S).Walk none (some v)) (hp : p.IsPath) :
    ∃ u : {a : V // a ∉ S},
      ∃ h : (identificationGraph G S).Adj none (some u),
        ∃ t : (identificationGraph G S).Walk (some u) (some v),
          p = Walk.cons h t ∧ t.IsPath ∧ none ∉ t.support ∧
            p.length = t.length + 1 := by
  have hne : (none : IdentificationVertex S) ≠ some v := by
    intro he
    cases he
  obtain ⟨w, h, t, rfl⟩ := Walk.exists_eq_cons_of_ne hne p
  cases w with
  | none => exact False.elim h
  | some u =>
    have hc := (Walk.cons_isPath_iff h t).mp hp
    exact ⟨u, h, t, rfl, hc.1, hc.2, Walk.length_cons h t⟩

/-- Lift an arbitrary actual simple fresh-root path, preserving its whole length and support domain. -/
theorem identification_path_lift (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S})
    (p : (identificationGraph G S).Walk none (some v)) (hp : p.IsPath) :
    ∃ s ∈ S, ∃ q : G.Walk s v.1,
      q.IsPath ∧ q.length = p.length ∧
        ∀ a ∈ q.support, a = s ∨ a ∉ S := by
  obtain ⟨u, h, t, _hp_eq, ht, hn, hlen⟩ :=
    identification_path_first_spoke G S v p hp
  obtain ⟨te, hte, hte_len⟩ := identification_exterior_path G S u v t ht hn
  obtain ⟨s, hs, q, hq, hq_len, hq_support⟩ :=
    identification_spoke_lift G S u v te hte h
  refine ⟨s, hs, q, hq, ?_, hq_support⟩
  calc
    q.length = te.length + 1 := hq_len
    _ = t.length + 1 := congrArg (fun n : ℕ => n + 1) hte_len
    _ = p.length := hlen.symm

/-- Pair lifting selects each true S-start independently and retains both exact lengths and gap. -/
theorem identification_two_path_lift (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S})
    (p q : (identificationGraph G S).Walk none (some v))
    (hpq : TwoPathWitness p q) :
    ∃ s ∈ S, ∃ t ∈ S, ∃ P : G.Walk s v.1, ∃ Q : G.Walk t v.1,
      P.IsPath ∧ Q.IsPath ∧ 2 ≤ P.length ∧ 2 ≤ Q.length ∧
        (P.length + 1 = Q.length ∨ P.length + 2 = Q.length) ∧
        P.length = p.length ∧ Q.length = q.length ∧
        (∀ a ∈ P.support, a = s ∨ a ∉ S) ∧
        (∀ a ∈ Q.support, a = t ∨ a ∉ S) := by
  rcases hpq with ⟨hp, hq, hp2, hq2, hgap⟩
  obtain ⟨s, hs, P, hP, hPlen, hPS⟩ := identification_path_lift G S v p hp
  obtain ⟨t, ht, Q, hQ, hQlen, hQS⟩ := identification_path_lift G S v q hq
  refine ⟨s, hs, t, ht, P, Q, hP, hQ, ?_, ?_, ?_, hPlen, hQlen, hPS, hQS⟩
  · simpa only [hPlen] using hp2
  · simpa only [hQlen] using hq2
  · simpa only [hPlen, hQlen] using hgap

/-- Reverse transport handles an arbitrary simple path whose final endpoint is the fresh root. -/
theorem identification_path_lift_to_root (G : SimpleGraph V) (S : Set V)
    (u : {a : V // a ∉ S})
    (p : (identificationGraph G S).Walk (some u) none) (hp : p.IsPath) :
    ∃ s ∈ S, ∃ q : G.Walk u.1 s,
      q.IsPath ∧ q.length = p.length ∧
        ∀ a ∈ q.support, a = s ∨ a ∉ S := by
  obtain ⟨s, hs, q, hq, hq_len, hq_support⟩ :=
    identification_path_lift G S u p.reverse hp.reverse
  refine ⟨s, hs, q.reverse, hq.reverse, ?_, ?_⟩
  · simpa only [Walk.length_reverse] using hq_len
  · intro a ha
    have ha' : a ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using ha
    exact hq_support a ha'

#print axioms identificationExteriorValue
#print axioms identificationExteriorValue_some
#print axioms identificationExteriorValue_injective
#print axioms identificationExteriorHom
#print axioms identification_exterior_path
#print axioms identification_path_first_spoke
#print axioms identification_path_lift
#print axioms identification_two_path_lift
#print axioms identification_path_lift_to_root

end TaskH.Fan
