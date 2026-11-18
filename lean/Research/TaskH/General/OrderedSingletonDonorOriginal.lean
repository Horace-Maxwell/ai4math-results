import Research.TaskH.General.OrderedColorRanks
import Research.TaskH.General.SingletonRetainedOriginal

/-! Actual ordered-list donors from one fixed whole deleted-vertex coloring.
The full permutation, original supplying cycle, retained endpoint, prefix,
length and every interior color are obtained internally. No donor/path oracle
is added to the original criticality and exact-count hypotheses. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k s : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Any prescribed injective list avoiding the two actual singleton colors
is the exact interior color word of an actual original donor. -/
theorem equality_original_ordered_singleton_donor (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (hsk : s + 2 ≤ k) (D : Fin s → Fin k) (hD : Function.Injective D)
    (hDa : ∀ i, D i ≠ c ⟨a, hva.ne.symm⟩)
    (hDb : ∀ i, D i ≠ c ⟨b, hvb.ne.symm⟩) :
    ∃ p : G.Walk v b, p.IsPath ∧ p.length = s + 1 ∧ a ∉ p.support ∧
      (∀ i : Fin s, ∃ hz : p.getVert (i.val + 1) ≠ v,
        c ⟨p.getVert (i.val + 1), hz⟩ = D i) ∧
      (∀ (z : V) (hzv : z ≠ v), z ∈ p.support → z ≠ b →
        ∃ i : Fin s, c ⟨z, hzv⟩ = D i) := by
  obtain ⟨π, hπa, hπb, hπD⟩ := exists_ordered_color_ranks hsk
    (c ⟨a, hva.ne.symm⟩) (c ⟨b, hvb.ne.symm⟩) habcolor D hD hDa hDb
  have hrank : ((finRotate k) ^ (s + 1)) (π (c ⟨a, hva.ne.symm⟩)) =
      π (c ⟨b, hvb.ne.symm⟩) := by
    rw [hπa, hπb]
    exact rotate_pow_zero_rank (by omega) (s + 1) (by omega)
  obtain ⟨p, hp, hlen, _, ha, hword⟩ := equality_original_singleton_ranked_donor
    hk hcrit hcount hva hvb c haunique hbunique habcolor π (s + 1) (by omega) hrank
  have hcolors : ∀ i : Fin s, ∃ hz : p.getVert (i.val + 1) ≠ v,
      c ⟨p.getVert (i.val + 1), hz⟩ = D i := by
    intro i
    have hi := i.isLt
    obtain ⟨hz, hw⟩ := hword (i.val + 1) (by omega) (by omega)
    refine ⟨hz, π.injective ?_⟩
    calc
      π (c ⟨p.getVert (i.val + 1), hz⟩) =
          ((finRotate k) ^ (i.val + 1)) (π (c ⟨a, hva.ne.symm⟩)) := hw
      _ = ⟨i.val + 1, by omega⟩ := by
        rw [hπa]
        exact rotate_pow_zero_rank (by omega) (i.val + 1) (by omega)
      _ = π (D i) := (hπD i).symm
  refine ⟨p, hp, hlen, ha, hcolors, ?_⟩
  intro z hzv hzp hzb
  obtain ⟨n, hnz, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hzp
  have hn0 : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    subst n
    exact hzv (by simpa only [Walk.getVert_zero] using hnz.symm)
  have hnl : n < p.length := by
    by_contra hh
    have he : n = p.length := by omega
    exact hzb (by simpa only [he, Walk.getVert_length] using hnz.symm)
  let i : Fin s := ⟨n - 1, by omega⟩
  obtain ⟨hz, hc⟩ := hcolors i
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hv : p.getVert (i.val + 1) = z := by rw [hi]; exact hnz
  refine ⟨i, ?_⟩
  have he : (⟨p.getVert (i.val + 1), hz⟩ : {z : V // z ≠ v}) = ⟨z, hzv⟩ :=
    Subtype.ext hv
  exact (congrArg c he).symm.trans hc

end TaskH.General

#print axioms TaskH.General.equality_original_ordered_singleton_donor
