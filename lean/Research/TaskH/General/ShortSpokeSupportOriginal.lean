import Research.TaskH.General.ShortSingletonSpokeOriginal

/-! Support-level transport of the actual short-spoke color-word theorem.
No cycle-shortening operation is applied to the original prescribed path. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_short_spoke_support_rainbow (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (q : G.Walk b v) (hq : q.IsPath) (hL2 : 2 ≤ q.length)
    (hLk : q.length + 1 ≤ k)
    {p p' : V} (hp : p ∈ q.support) (hp' : p' ∈ q.support)
    (hpv : p ≠ v) (hp'v : p' ≠ v)
    (hcolor : c ⟨p, hpv⟩ = c ⟨p', hp'v⟩) : p = p' := by
  obtain ⟨n, hn, hnL⟩ := Walk.mem_support_iff_exists_getVert.mp hp
  obtain ⟨m, hm, hmL⟩ := Walk.mem_support_iff_exists_getVert.mp hp'
  have hnlt : n < q.length := by
    by_contra hh
    have he : n = q.length := by omega
    exact hpv (by simpa only [he, Walk.getVert_length] using hn.symm)
  have hmlt : m < q.length := by
    by_contra hh
    have he : m = q.length := by omega
    exact hp'v (by simpa only [he, Walk.getVert_length] using hm.symm)
  let i : Fin q.length := ⟨n, hnlt⟩
  let j : Fin q.length := ⟨m, hmlt⟩
  have hi : deletedPathColorWord c q hq i = c ⟨p, hpv⟩ :=
    congrArg c (Subtype.ext hn)
  have hj : deletedPathColorWord c q hq j = c ⟨p', hp'v⟩ :=
    congrArg c (Subtype.ext hm)
  have he := equality_original_short_singleton_spoke_rainbow hk hcrit hcount
    hva hvb c haunique hbunique habcolor q hq hL2 hLk
    (hi.trans (hcolor.trans hj.symm))
  have heval : n = m := congrArg Fin.val he
  exact hn.symm.trans ((congrArg q.getVert heval).trans hm)

end TaskH.General

#print axioms TaskH.General.equality_original_short_spoke_support_rainbow
