import Research.TaskH.General.ShortSingletonSpokeOriginal

/-! A real two-color-path consequence of the completed short-spoke branch.
For any actual simple path in G-v from a singleton center to another neighbor
of v, if the old coloring uses at most its singleton color and one other
color, and the path has at least two edges, its length is at least k-1.
This is the lower-length half needed for locked Kempe rows; no Kempe swap,
whole-class upper bound, existence of locked rows, or minimum degree is claimed. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_two_color_singleton_path_long (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b z : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {w | w ≠ v}).Coloring (Fin k))
    (haunique : ∀ (w : V) (hwv : w ≠ v), G.Adj v w →
      c ⟨w, hwv⟩ = c ⟨a, hva.ne.symm⟩ → w = a)
    (hbunique : ∀ (w : V) (hwv : w ≠ v), G.Adj v w →
      c ⟨w, hwv⟩ = c ⟨b, hvb.ne.symm⟩ → w = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (q : G.Walk b z) (hq : q.IsPath) (havoid : v ∉ q.support)
    (hzv : G.Adj z v) (hlen : 2 ≤ q.length) (γ : Fin k)
    (htwo : ∀ (w : V) (hwv : w ≠ v), w ∈ q.support →
      c ⟨w, hwv⟩ = c ⟨b, hvb.ne.symm⟩ ∨ c ⟨w, hwv⟩ = γ) :
    k - 1 ≤ q.length := by
  classical
  by_contra hshort
  let r := q.concat hzv
  have hr : r.IsPath := hq.concat havoid hzv
  have hrlen : r.length = q.length + 1 := Walk.length_concat q hzv
  have hshortR : r.length + 1 ≤ k := by omega
  have hword := equality_original_short_singleton_spoke_rainbow hk hcrit hcount
    hva hvb c haunique hbunique habcolor r hr (by omega) hshortR
  let S : Finset (Fin k) := {c ⟨b, hvb.ne.symm⟩, γ}
  have hsub : Finset.univ.image (deletedPathColorWord c r hr) ⊆ S := by
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    have hne := path_getVert_before_end_ne r hr i
    have hm : r.getVert i.val ∈ q.support := by
      have hh := r.getVert_mem_support i.val
      change r.getVert i.val ∈ (q.concat hzv).support at hh
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hh
      exact hh.resolve_right hne
    change c ⟨r.getVert i.val, _⟩ ∈ S
    simpa only [S, Finset.mem_insert, Finset.mem_singleton] using htwo _ hne hm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hword, Finset.card_univ, Fintype.card_fin] at hcard
  have hS : S.card ≤ 2 := by
    have hh := Finset.card_insert_le (c ⟨b, hvb.ne.symm⟩) ({γ} : Finset (Fin k))
    simpa only [S, Finset.card_singleton] using hh
  omega

end TaskH.General

#print axioms TaskH.General.equality_original_two_color_singleton_path_long
