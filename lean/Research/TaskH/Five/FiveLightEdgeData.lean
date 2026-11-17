import Research.TaskH.Five.FivePatternData

/-! Literal finite facts for light edges of a five-cycle. -/

namespace TaskH.Five

open SimpleGraph

def lightCycleIndices : Finset (Sym2 (Fin 5)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0)}

def lightChordEnds (i : Fin 5) : Fin 5 × Fin 5 :=
  ![(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)] i

def lightChord (i : Fin 5) : Sym2 (Fin 5) :=
  s((lightChordEnds i).1, (lightChordEnds i).2)

def lightIndexEdges (A : Finset (Fin 5)) : Finset (Sym2 (Fin 5)) :=
  lightCycleIndices ∪ A.image lightChord

def lightIndexCommon (E : Finset (Sym2 (Fin 5))) (u v : Fin 5) :
    Finset (Fin 5) :=
  Finset.univ.filter (fun j => s(u, j) ∈ E ∧ s(v, j) ∈ E)

/-- An outside common neighbor of `u,v`, appended to `a-b-u`, makes a gem
with hub `v`. The four indicated inside positions are distinct. -/
def LightGemHook (E : Finset (Sym2 (Fin 5))) (u v : Fin 5) : Prop :=
  ∃ a b : Fin 5, Function.Injective (![a, b, u, v] : Fin 4 → Fin 5) ∧
    s(a, b) ∈ E ∧ s(b, u) ∈ E ∧ s(v, a) ∈ E ∧
    s(v, b) ∈ E ∧ s(v, u) ∈ E

def LightIndexGem (E : Finset (Sym2 (Fin 5)))
    (g : Equiv.Perm (Fin 5)) : Prop :=
  s(g 0, g 1) ∈ E ∧ s(g 1, g 2) ∈ E ∧ s(g 2, g 3) ∈ E ∧
    s(g 0, g 4) ∈ E ∧ s(g 1, g 4) ∈ E ∧
    s(g 2, g 4) ∈ E ∧ s(g 3, g 4) ∈ E

theorem light_two_neighbors_determine_edge (A : Finset (Fin 5))
    (i j : Fin 5) (hcard : A.card ≤ 2)
    (hi : i ∈ A) (his : i + 1 ∈ A) (hj : j ∈ A) (hjs : j + 1 ∈ A) :
    i = j := by
  revert A i j
  decide +kernel

theorem light_one_chord_common_le_one (A : Finset (Fin 5)) (hA : A.card ≤ 1)
    (i : Fin 5) :
    (lightIndexCommon (lightIndexEdges A) i (i + 1)).card ≤ 1 := by
  revert A i
  decide +kernel

/-- The remaining two-disjoint-chord case supplies an explicit gem hook;
all other larger masks already contain a gem. Only the 32 chord masks are
being checked, with actual graph transport deferred to the next module. -/
theorem light_many_chords_hook_or_gem (A : Finset (Fin 5)) (hA : 2 ≤ A.card) :
    (∃ i : Fin 5,
      (lightIndexCommon (lightIndexEdges A) i (i + 1)).card ≤ 1 ∧
      (LightGemHook (lightIndexEdges A) i (i + 1) ∨
        LightGemHook (lightIndexEdges A) (i + 1) i)) ∨
    ∃ g : Equiv.Perm (Fin 5), LightIndexGem (lightIndexEdges A) g := by
  by_cases h0 : (0 : Fin 5) ∈ A <;>
    by_cases h1 : (1 : Fin 5) ∈ A <;>
    by_cases h2 : (2 : Fin 5) ∈ A <;>
    by_cases h3 : (3 : Fin 5) ∈ A <;>
    by_cases h4 : (4 : Fin 5) ∈ A
  · have hmask : A = ({0, 1, 2, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 1, 2, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 2, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 2, 1, 4, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 2) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(2, 1) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({0, 1, 2, 3} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 2, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({0, 1, 2, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 2} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![1, 2, 0, 4, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(1, 2) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(2, 0) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({0, 1, 2} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 1, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![1, 2, 3, 4, 0] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(1, 2) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(1, 0) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(2, 0) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(3, 0) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5)) ∧
      s(4, 0) ∈ lightIndexEdges ({0, 1, 3} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![1, 0, 3, 4, 2] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(1, 0) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(0, 2) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(3, 2) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5)) ∧
      s(4, 2) ∈ lightIndexEdges ({0, 1, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 1} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![1, 2, 3, 4, 0] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(1, 2) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(1, 0) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(2, 0) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(3, 0) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5)) ∧
      s(4, 0) ∈ lightIndexEdges ({0, 1} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 2, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 2, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 2, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 2, 3, 4, 1] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 2) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(0, 1) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(2, 1) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(3, 1) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5)) ∧
      s(4, 1) ∈ lightIndexEdges ({0, 2, 3} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 2, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 3, 4, 2] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(0, 2) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(3, 2) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5)) ∧
      s(4, 2) ∈ lightIndexEdges ({0, 2, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 2} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    refine Or.inl ⟨0, ?_, ?_⟩
    · decide +kernel
    · refine Or.inl ⟨3, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold Function.Injective
        decide +kernel
      all_goals decide +kernel
  · have hmask : A = ({0, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({0, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    refine Or.inl ⟨1, ?_, ?_⟩
    · decide +kernel
    · refine Or.inr ⟨4, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold Function.Injective
        decide +kernel
      all_goals decide +kernel
  · have hmask : A = ({0, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![1, 0, 4, 3, 2] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(1, 0) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(0, 2) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(4, 2) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5)) ∧
      s(3, 2) ∈ lightIndexEdges ({0, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({0} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA
  · have hmask : A = ({1, 2, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({1, 2, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({1, 2, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 4, 1, 2, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 4) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(4, 1) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({1, 2, 3} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({1, 2, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({1, 2, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({1, 2} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![2, 1, 0, 4, 3] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(2, 1) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(1, 0) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(1, 3) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(0, 3) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({1, 2} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({1, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({1, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({1, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    refine Or.inl ⟨0, ?_, ?_⟩
    · decide +kernel
    · refine Or.inr ⟨3, 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold Function.Injective
        decide +kernel
      all_goals decide +kernel
  · have hmask : A = ({1, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    refine Or.inl ⟨2, ?_, ?_⟩
    · decide +kernel
    · refine Or.inl ⟨0, 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold Function.Injective
        decide +kernel
      all_goals decide +kernel
  · have hmask : A = ({1} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA
  · have hmask : A = ({2, 3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({2, 3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({2, 3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 4, 3, 2, 1] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 4) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(4, 3) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(3, 2) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(0, 1) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(4, 1) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(3, 1) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5)) ∧
      s(2, 1) ∈ lightIndexEdges ({2, 3} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({2, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    refine Or.inl ⟨1, ?_, ?_⟩
    · decide +kernel
    · refine Or.inl ⟨4, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold Function.Injective
        decide +kernel
      all_goals decide +kernel
  · have hmask : A = ({2} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA
  · have hmask : A = ({3, 4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    let g : Equiv.Perm (Fin 5) := Equiv.ofBijective
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by
        unfold Function.Bijective Function.Injective Function.Surjective
        decide +kernel)
    refine Or.inr ⟨g, ?_⟩
    change s(0, 1) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(1, 2) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(2, 3) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(0, 4) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(1, 4) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(2, 4) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5)) ∧
      s(3, 4) ∈ lightIndexEdges ({3, 4} : Finset (Fin 5))
    decide +kernel
  · have hmask : A = ({3} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA
  · have hmask : A = ({4} : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA
  · have hmask : A = (∅ : Finset (Fin 5)) := by
      ext i
      fin_cases i <;> simp_all
    subst A
    norm_num at hA

end TaskH.Five

#print axioms TaskH.Five.lightCycleIndices
#print axioms TaskH.Five.lightChordEnds
#print axioms TaskH.Five.lightChord
#print axioms TaskH.Five.lightIndexEdges
#print axioms TaskH.Five.lightIndexCommon
#print axioms TaskH.Five.LightGemHook
#print axioms TaskH.Five.LightIndexGem
#print axioms TaskH.Five.light_two_neighbors_determine_edge
#print axioms TaskH.Five.light_one_chord_common_le_one
#print axioms TaskH.Five.light_many_chords_hook_or_gem
