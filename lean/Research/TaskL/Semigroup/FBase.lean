import Research.TaskL.Semigroup.Challenge

namespace TaskL.Semigroup
open Challenge

noncomputable section
open Classical

def gaps (S : AddSubmonoid ℕ) : Finset ℕ :=
  if h : Numerical S then h.toFinset else ∅

def Special (S : AddSubmonoid ℕ) (g : ℕ) : Prop :=
  g ∉ S ∧ g + g ∈ S ∧ ∀ s ∈ S, 0 < s → g + s ∈ S

def specials (S : AddSubmonoid ℕ) : Finset ℕ :=
  (gaps S).filter (Special S)

def frob (S : AddSubmonoid ℕ) : ℕ := (gaps S).sup id

def gapWeight (S : AddSubmonoid ℕ) : ℕ := ∑ g ∈ gaps S, (g + 1)

def Eligible (S : AddSubmonoid ℕ) (D : Finset (AddSubmonoid ℕ)) : Prop :=
  ∀ Q ∈ D, Irreducible Q ∧ S ≤ Q

def Cover (S : AddSubmonoid ℕ) (D : Finset (AddSubmonoid ℕ)) : Prop :=
  ∀ g, Special S g → ∃ Q ∈ D, g ∉ Q

variable {S Q : AddSubmonoid ℕ} {n g : ℕ}

theorem mem_gaps (hS : Numerical S) : g ∈ gaps S ↔ g ∉ S := by
  rw [gaps, dite_eq_left hS]
  exact Set.Finite.mem_toFinset _

theorem mem_specials (hS : Numerical S) : g ∈ specials S ↔ Special S g := by
  simp only [specials, Finset.mem_filter, mem_gaps hS]
  exact ⟨And.right, fun h ↦ ⟨h.1, h⟩⟩

theorem numerical_of_le (hS : Numerical S) (h : S ≤ Q) : Numerical Q :=
  hS.subset fun _ hn hs ↦ hn (h hs)

theorem le_frob (hS : Numerical S) (hg : g ∉ S) : g ≤ frob S :=
  Finset.le_sup (f := id) ((mem_gaps hS).2 hg)

theorem mem_of_frob_lt (hS : Numerical S) (h : frob S < n) : n ∈ S := by
  by_contra hn
  exact h.not_ge (le_frob hS hn)

theorem frob_notMem (hS : Numerical S) (h : S ≠ ⊤) : frob S ∉ S := by
  have hex : (gaps S).Nonempty := by
    by_contra hem
    apply h
    apply top_unique
    intro n _
    by_contra hn
    exact hem ⟨n, (mem_gaps hS).2 hn⟩
  have hm := Finset.sup_mem_of_nonempty (f := id) hex
  apply (mem_gaps hS).1
  simpa [frob] using hm

end
end TaskL.Semigroup
