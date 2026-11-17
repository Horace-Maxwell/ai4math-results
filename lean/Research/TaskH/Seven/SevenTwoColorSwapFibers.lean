import Research.TaskH.Seven.SevenTwoColorPaths

/-! Exact actual neighbor-fiber effect of a component exchange.  N may be the
actual neighbor set of a deleted root.  No assertion that a component meets
all pairs, or that arbitrary outside points are covered, is used. -/

set_option autoImplicit false
universe u v
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} {A : Type v} [DecidableEq A] {G : SimpleGraph V}

theorem twoColorSwap_eq_left_iff (c : G.Coloring A) (alpha beta : A) (a z : V) :
    twoColorSwap c alpha beta a z = alpha ↔
      if z ∈ twoColorComponent c alpha beta a then c z = beta else c z = alpha := by
  rw [twoColorSwap_apply]
  split_ifs <;> simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

theorem twoColorSwap_eq_right_iff (c : G.Coloring A) (alpha beta : A) (a z : V) :
    twoColorSwap c alpha beta a z = beta ↔
      if z ∈ twoColorComponent c alpha beta a then c z = alpha else c z = beta := by
  rw [twoColorSwap_apply]
  split_ifs <;> simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

theorem twoColorComponent_contains_neighbor (c : G.Coloring A) (alpha beta : A)
    {a p : V} (ha : c a = alpha) (hp : c p = beta) (hap : G.Adj a p) :
    p ∈ twoColorComponent c alpha beta a := by
  apply Relation.ReflTransGen.single
  exact ⟨hap, by rw [ha, hp, Equiv.swap_apply_left]⟩

theorem twoColorSwap_singleton_pair_fibers (c : G.Coloring A)
    (alpha beta : A) (a p q : V) (N : Set V)
    (ha : c a = alpha) (hp : c p = beta) (hap : G.Adj a p)
    (hsingle : ∀ z ∈ N, c z = alpha ↔ z = a)
    (hpair : ∀ z ∈ N, c z = beta ↔ z = p ∨ z = q)
    (hqout : q ∉ twoColorComponent c alpha beta a) :
    (∀ z ∈ N, twoColorSwap c alpha beta a z = alpha ↔ z = p) ∧
    (∀ z ∈ N, twoColorSwap c alpha beta a z = beta ↔ z = a ∨ z = q) := by
  have hain : a ∈ twoColorComponent c alpha beta a := Relation.ReflTransGen.refl
  have hpin := twoColorComponent_contains_neighbor c alpha beta ha hp hap
  constructor
  · intro z hz
    rw [twoColorSwap_eq_left_iff]
    by_cases hzin : z ∈ twoColorComponent c alpha beta a
    · rw [ite_eq_left hzin]
      constructor
      · intro hcol
        rcases (hpair z hz).mp hcol with he | he
        · exact he
        · subst z
          exact (hqout hzin).elim
      · intro he
        subst z
        exact hp
    · rw [ite_eq_right hzin]
      constructor
      · intro hcol
        have he := (hsingle z hz).mp hcol
        subst z
        exact (hzin hain).elim
      · intro he
        subst z
        exact (hzin hpin).elim
  · intro z hz
    rw [twoColorSwap_eq_right_iff]
    by_cases hzin : z ∈ twoColorComponent c alpha beta a
    · rw [ite_eq_left hzin]
      constructor
      · exact fun hcol => Or.inl ((hsingle z hz).mp hcol)
      · rintro (he | he)
        · subst z
          exact ha
        · subst z
          exact (hqout hzin).elim
    · rw [ite_eq_right hzin]
      constructor
      · intro hcol
        rcases (hpair z hz).mp hcol with he | he
        · subst z
          exact (hzin hpin).elim
        · exact Or.inr he
      · rintro (he | he)
        · subst z
          exact (hzin hain).elim
        · exact (hpair z hz).mpr (Or.inr he)

end TaskH.Seven
#print axioms TaskH.Seven.twoColorSwap_eq_left_iff
#print axioms TaskH.Seven.twoColorSwap_eq_right_iff
#print axioms TaskH.Seven.twoColorComponent_contains_neighbor
#print axioms TaskH.Seven.twoColorSwap_singleton_pair_fibers
