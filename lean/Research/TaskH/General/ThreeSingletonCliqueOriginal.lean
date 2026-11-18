import Research.TaskH.General.OrderedSingletonDonorOriginal

/-! A genuine original q≥3 structure branch: any two singleton centers with
an actual third singleton of a different color are adjacent. The real edge
is obtained as the last edge of an internally generated length-two donor.
No clique, edge, donor, or color-permutation oracle is assumed. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_three_singleton_centers_adjacent (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b d : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hvd : G.Adj v d)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (hdunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨d, hvd.ne.symm⟩ → z = d)
    (hab : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (had : c ⟨a, hva.ne.symm⟩ ≠ c ⟨d, hvd.ne.symm⟩)
    (hbd : c ⟨b, hvb.ne.symm⟩ ≠ c ⟨d, hvd.ne.symm⟩) : G.Adj b d := by
  let D : Fin 1 → Fin k := fun _ => c ⟨b, hvb.ne.symm⟩
  obtain ⟨p, _, hlen, _, hword, _⟩ := equality_original_ordered_singleton_donor
    hk hcrit hcount hva hvd c haunique hdunique had (by omega) D
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hab.symm) (fun _ => hbd)
  obtain ⟨hz, hc⟩ := hword ⟨0, by omega⟩
  have hfirst : G.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have he : p.getVert 1 = b := hbunique (p.getVert 1) hz hfirst hc
  have hlast : p.getVert 2 = d := by
    rw [show (2 : ℕ) = p.length by omega, Walk.getVert_length]
  have hh := p.adj_getVert_succ (i := 1) (by omega)
  simpa only [he, hlast] using hh

end TaskH.General

#print axioms TaskH.General.equality_original_three_singleton_centers_adjacent
