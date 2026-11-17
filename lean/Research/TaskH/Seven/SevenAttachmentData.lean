import Research.TaskH.Seven.CycleSeven

/-! A genuine seven-cycle may replace one of its vertices by an outside
common neighbor of its two cyclic neighbors. Only seven-index tables are
used below; no graph or cycle-count table is assumed. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem heptagon_adj_succ {f : Fin 7 → V} (hf : IsHeptagon G f) (i : Fin 7) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2.2

theorem isHeptagon_of_injective_adj_succ (f : Fin 7 → V)
    (hf : Function.Injective f) (ha : ∀ i : Fin 7, G.Adj (f i) (f (i + 1))) :
    IsHeptagon G f :=
  ⟨hf, ha 0, ha 1, ha 2, ha 3, ha 4, ha 5, ha 6⟩

theorem finSeven_succ_ne (i : Fin 7) : i + 1 ≠ i := by
  revert i
  decide +kernel

theorem finSeven_eq_prev_of_succ_eq (j i : Fin 7) (h : j + 1 = i) : j = i + 6 := by
  have ht : ∀ j i : Fin 7, j + 1 = i → j = i + 6 := by decide +kernel
  exact ht j i h

theorem seven_index_replacement_bound (A : Finset (Fin 7)) (q : Fin 7)
    (h : ∀ i : Fin 7, i + 6 ∈ A → i + 1 ∈ A → i = q) : A.card ≤ 4 := by
  revert A q
  decide +kernel

def heptagonReplace (f : Fin 7 → V) (y : V) (i : Fin 7) : Fin 7 → V :=
  fun j => if j = i then y else f j

theorem heptagonReplace_injective (f : Fin 7 → V) (hf : Function.Injective f)
    (y : V) (hyout : ∀ j, y ≠ f j) (i : Fin 7) :
    Function.Injective (heptagonReplace f y i) := by
  intro j k he
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · exact hk.symm
    · have hh : y = f k := by
        simpa only [heptagonReplace, ite_true, ite_eq_right hk] using he
      exact (hyout k hh).elim
  · by_cases hk : k = i
    · subst k
      have hh : f j = y := by
        simpa only [heptagonReplace, ite_eq_right hj, ite_true] using he
      exact (hyout j hh.symm).elim
    · apply hf
      simpa only [heptagonReplace, ite_eq_right hj, ite_eq_right hk] using he

theorem heptagonReplace_isHeptagon (f : Fin 7 → V) (hf : IsHeptagon G f)
    (y : V) (hyout : ∀ j, y ≠ f j) (i : Fin 7)
    (hprev : G.Adj y (f (i + 6))) (hnext : G.Adj y (f (i + 1))) :
    IsHeptagon G (heptagonReplace f y i) := by
  apply isHeptagon_of_injective_adj_succ _ (heptagonReplace_injective f hf.1 y hyout i)
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [heptagonReplace, ite_true, ite_eq_right (finSeven_succ_ne i)]
      using hnext
  · by_cases hs : j + 1 = i
    · have hp : j = i + 6 := finSeven_eq_prev_of_succ_eq j i hs
      have hh : G.Adj (f j) y := by simpa only [hp] using hprev.symm
      simpa only [heptagonReplace, ite_eq_right hj, ite_eq_left hs] using hh
    · simpa only [heptagonReplace, ite_eq_right hj, ite_eq_right hs]
        using heptagon_adj_succ hf j

theorem heptagon_walk_support (f : Fin 7 → V) (hf : IsHeptagon G f) (i : Fin 7) :
    f i ∈ (heptagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1
      hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2).support := by
  fin_cases i <;> simp [heptagonWalk, Walk.support_cons]

end TaskH.Seven

#print axioms TaskH.Seven.heptagon_adj_succ
#print axioms TaskH.Seven.isHeptagon_of_injective_adj_succ
#print axioms TaskH.Seven.finSeven_succ_ne
#print axioms TaskH.Seven.finSeven_eq_prev_of_succ_eq
#print axioms TaskH.Seven.seven_index_replacement_bound
#print axioms TaskH.Seven.heptagonReplace
#print axioms TaskH.Seven.heptagonReplace_injective
#print axioms TaskH.Seven.heptagonReplace_isHeptagon
#print axioms TaskH.Seven.heptagon_walk_support
