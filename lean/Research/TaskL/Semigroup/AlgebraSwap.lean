import Research.TaskL.Semigroup.AlgebraCore

namespace TaskL.Semigroup
open Challenge
noncomputable section

private theorem swap_closed {Q : AddSubmonoid ℕ} {u f : ℕ}
    (hQ : Irreducible Q) (hF : IsFrob Q f) (hu : 0 < u) (hlo : 2*u < f)
    (hAtom : ∀ a ∈ Q, ∀ b ∈ Q, a+b=u → a=0 ∨ b=0)
    (a b : ℕ) (ha : a=f-u ∨ a∈Q ∧ a≠u) (hb : b=f-u ∨ b∈Q ∧ b≠u) :
    a+b=f-u ∨ a+b∈Q ∧ a+b≠u := by
  have shift (q : ℕ) (hq : q∈Q) (hne : q≠u) :
      (f-u)+q=f-u ∨ (f-u)+q∈Q ∧ (f-u)+q≠u := by
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · exact Or.inl (by omega)
    · refine Or.inr ⟨?_, by omega⟩
      by_cases hlt : q < u
      · have hmiss : u-q ∉ Q := by
          intro hm
          have hj := hAtom q hq (u-q) hm (by omega)
          omega
        have hcomp := (complement_low hQ hF (show 2*(u-q)<f by omega)).2 hmiss
        rwa [show f-(u-q)=f-u+q by omega] at hcomp
      · exact hF.2 _ (by omega)
  rcases ha with rfl | ⟨ha, hane⟩ <;> rcases hb with rfl | ⟨hb,hbne⟩
  · exact Or.inr ⟨hF.2 _ (by omega), by omega⟩
  · exact shift _ hb hbne
  · rw [Nat.add_comm]
    exact shift _ ha hane
  · refine Or.inr ⟨Q.add_mem ha hb, ?_⟩
    intro eq
    have h := hAtom a ha b hb eq
    omega

theorem swap_at_low_atom {Q S : AddSubmonoid ℕ} {f u : ℕ}
    (hQ : Irreducible Q) (hF : IsFrob Q f) (hSQ : S≤Q) (hu : 0<u)
    (hlo : 2*u<f) (huS : u∉S)
    (hAtom : ∀ a ∈ Q, ∀ b ∈ Q, a+b=u → a=0 ∨ b=0) :
    ∃ Q' : AddSubmonoid ℕ, Irreducible Q' ∧ S≤Q' ∧ IsFrob Q' f ∧
      ∀ n : ℕ, n∈Q' ↔ n=f-u ∨ n∈Q ∧ n≠u := by
  let Q' : AddSubmonoid ℕ := {
    carrier := {n | n=f-u ∨ n∈Q ∧ n≠u}
    zero_mem' := Or.inr ⟨Q.zero_mem, by omega⟩
    add_mem' := fun {a b} ha hb => swap_closed hQ hF hu hlo hAtom a b ha hb }
  have hm (n : ℕ) : n∈Q' ↔ n=f-u ∨ n∈Q ∧ n≠u := Iff.rfl
  have hf' : IsFrob Q' f := by
    constructor
    · intro hf
      rcases (hm f).1 hf with he | ⟨he,_⟩
      · omega
      · exact hF.1 he
    · intro n hn
      exact (hm n).2 (Or.inr ⟨hF.2 n hn,by omega⟩)
  refine ⟨Q', irreducible_of_complement hf' ?_, ?_, hf', hm⟩
  · intro n hn
    rw [hm, hm]
    by_cases he : n=u
    · subst n
      simp [show u≠f-u by omega]
    · have h1 : n ≠ f-u := by omega
      have h2 : f-n ≠ f-u := by omega
      have h3 : f-n ≠ u := by omega
      simpa [h1,h2,h3,he] using complement_low hQ hF hn
  · intro n hn
    exact (hm n).2 (Or.inr ⟨hSQ hn, fun h => huS (h ▸ hn)⟩)

end
end TaskL.Semigroup
