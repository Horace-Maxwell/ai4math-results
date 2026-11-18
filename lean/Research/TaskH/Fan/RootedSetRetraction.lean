import Research.TaskH.Fan.AdjEqConnectivity

/-!
A true induced-set retraction when only its distinguished root can have a
neighbor outside the set. Edges may collapse to equal vertices, so this is
used for connectivity, never for preserved walk lengths.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

noncomputable def rootedSetRetraction (S : Set V) (z : V) (hz : z ∈ S) : V → S := by
  classical
  exact fun v => if hv : v ∈ S then ⟨v, hv⟩ else ⟨z, hz⟩

@[simp]
theorem rootedSetRetraction_mem (S : Set V) (z : V) (hz : z ∈ S)
    (v : V) (hv : v ∈ S) : rootedSetRetraction S z hz v = ⟨v, hv⟩ := by
  classical
  simp only [rootedSetRetraction, dite_eq_left hv]

theorem rootedSetRetraction_surjective (S : Set V) (z : V) (hz : z ∈ S) :
    Function.Surjective (rootedSetRetraction S z hz) := by
  intro v
  exact ⟨v.1, rootedSetRetraction_mem S z hz v.1 v.2⟩

theorem rootedSetRetraction_adj_or_eq (K : SimpleGraph V) (S : Set V)
    (z : V) (hz : z ∈ S)
    (hc : ∀ a ∈ S, a ≠ z → ∀ b, K.Adj a b → b ∈ S)
    {a b : V} (hab : K.Adj a b) :
    rootedSetRetraction S z hz a = rootedSetRetraction S z hz b ∨
      (K.induce S).Adj (rootedSetRetraction S z hz a)
        (rootedSetRetraction S z hz b) := by
  classical
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · right
      change K.Adj (rootedSetRetraction S z hz a).val
        (rootedSetRetraction S z hz b).val
      simpa only [rootedSetRetraction, dite_eq_left ha, dite_eq_left hb] using hab
    · have haz : a = z := by
        by_contra haz
        exact hb (hc a ha haz b hab)
      subst a
      left
      simp only [rootedSetRetraction, dite_eq_left hz, dite_eq_right hb]
  · by_cases hb : b ∈ S
    · have hbz : b = z := by
        by_contra hbz
        exact ha (hc b hb hbz a hab.symm)
      subst b
      left
      simp only [rootedSetRetraction, dite_eq_right ha, dite_eq_left hz]
    · left
      simp only [rootedSetRetraction, dite_eq_right ha, dite_eq_right hb]

theorem rootedSet_connected (K : SimpleGraph V) (S : Set V) (z : V) (hz : z ∈ S)
    (hc : ∀ a ∈ S, a ≠ z → ∀ b, K.Adj a b → b ∈ S)
    (hK : K.Connected) : (K.induce S).Connected := by
  exact connected_of_surjective_adj_or_eq (rootedSetRetraction S z hz)
    (rootedSetRetraction_surjective S z hz)
    (rootedSetRetraction_adj_or_eq K S z hz hc) hK

noncomputable def rootedSetDeleteRetraction (S : Set V) (z : V) (hz : z ∈ S)
    (w : S) (hw : w.1 ≠ z) : {a : V // a ≠ w.1} → {b : S // b ≠ w} := by
  classical
  intro a
  refine ⟨rootedSetRetraction S z hz a.1, ?_⟩
  intro he
  by_cases ha : a.1 ∈ S
  · have hval : a.1 = w.1 := by
      simpa only [rootedSetRetraction, dite_eq_left ha] using congrArg Subtype.val he
    exact a.2 hval
  · have hval : z = w.1 := by
      simpa only [rootedSetRetraction, dite_eq_right ha] using congrArg Subtype.val he
    exact hw hval.symm

theorem rootedSetDeleteRetraction_surjective (S : Set V) (z : V) (hz : z ∈ S)
    (w : S) (hw : w.1 ≠ z) :
    Function.Surjective (rootedSetDeleteRetraction S z hz w hw) := by
  intro b
  have hb : b.1.1 ≠ w.1 := by
    intro he
    exact b.2 (Subtype.ext he)
  refine ⟨⟨b.1.1, hb⟩, ?_⟩
  apply Subtype.ext
  change rootedSetRetraction S z hz b.1.1 = b.1
  exact rootedSetRetraction_mem S z hz b.1.1 b.1.2

theorem rootedSetDeleteRetraction_adj_or_eq (K : SimpleGraph V) (S : Set V)
    (z : V) (hz : z ∈ S)
    (hc : ∀ a ∈ S, a ≠ z → ∀ b, K.Adj a b → b ∈ S)
    (w : S) (hw : w.1 ≠ z) {a b : {v : V // v ≠ w.1}}
    (hab : (K.induce {v | v ≠ w.1}).Adj a b) :
    rootedSetDeleteRetraction S z hz w hw a =
        rootedSetDeleteRetraction S z hz w hw b ∨
      ((K.induce S).induce {v | v ≠ w}).Adj
        (rootedSetDeleteRetraction S z hz w hw a)
        (rootedSetDeleteRetraction S z hz w hw b) := by
  rcases rootedSetRetraction_adj_or_eq K S z hz hc hab with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr he

theorem rootedSet_delete_connected (K : SimpleGraph V) (S : Set V)
    (z : V) (hz : z ∈ S)
    (hc : ∀ a ∈ S, a ≠ z → ∀ b, K.Adj a b → b ∈ S)
    (w : S) (hw : w.1 ≠ z) (hK : (K.induce {v | v ≠ w.1}).Connected) :
    ((K.induce S).induce {v | v ≠ w}).Connected := by
  exact connected_of_surjective_adj_or_eq (rootedSetDeleteRetraction S z hz w hw)
    (rootedSetDeleteRetraction_surjective S z hz w hw)
    (rootedSetDeleteRetraction_adj_or_eq K S z hz hc w hw) hK

theorem rootedSet_neighbor_ncard (K : SimpleGraph V) (S : Set V) (z : V)
    (hc : ∀ a ∈ S, a ≠ z → ∀ b, K.Adj a b → b ∈ S)
    (t : S) (ht : t.1 ≠ z) :
    (K.neighborSet t.1).ncard = ((K.induce S).neighborSet t).ncard := by
  apply Set.ncard_congr (fun a ha => (⟨a, hc t.1 t.2 ht a ha⟩ : S))
  · intro a ha
    exact ha
  · intro a b ha hb he
    exact congrArg Subtype.val he
  · intro b hb
    exact ⟨b.1, hb, Subtype.ext rfl⟩

#print axioms rootedSetRetraction
#print axioms rootedSetRetraction_mem
#print axioms rootedSetRetraction_surjective
#print axioms rootedSetRetraction_adj_or_eq
#print axioms rootedSet_connected
#print axioms rootedSetDeleteRetraction
#print axioms rootedSetDeleteRetraction_surjective
#print axioms rootedSetDeleteRetraction_adj_or_eq
#print axioms rootedSet_delete_connected
#print axioms rootedSet_neighbor_ncard
end TaskH.Fan
