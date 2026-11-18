import Research.TaskH.General.OrderedSingletonDonorOriginal

/-! An original fiber-boundary consequence: each color different from two
actual singleton neighbor colors has an actual root neighbor adjacent to the
second singleton center. This is joint coverage of singleton centers by the
real root-neighbor color fiber, not a supplied coverage hypothesis. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_singleton_color_fiber_touches (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (γ : Fin k) (hγa : γ ≠ c ⟨a, hva.ne.symm⟩)
    (hγb : γ ≠ c ⟨b, hvb.ne.symm⟩) :
    ∃ (z : V) (hzv : z ≠ v), G.Adj v z ∧ c ⟨z, hzv⟩ = γ ∧ G.Adj z b := by
  let D : Fin 1 → Fin k := fun _ => γ
  obtain ⟨p, _, hlen, _, hword, _⟩ := equality_original_ordered_singleton_donor
    hk hcrit hcount hva hvb c haunique hbunique habcolor (by omega) D
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hγa) (fun _ => hγb)
  obtain ⟨hz, hc⟩ := hword ⟨0, by omega⟩
  have hfirst : G.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have hlast : p.getVert 2 = b := by
    rw [show (2 : ℕ) = p.length by omega, Walk.getVert_length]
  have hh : G.Adj (p.getVert 1) b := by
    simpa only [hlast] using p.adj_getVert_succ (i := 1) (by omega)
  exact ⟨p.getVert 1, hz, hfirst, hc, hh⟩

end TaskH.General

#print axioms TaskH.General.equality_original_singleton_color_fiber_touches
