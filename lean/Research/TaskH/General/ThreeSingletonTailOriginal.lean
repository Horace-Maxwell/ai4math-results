import Research.TaskH.General.OrderedSingletonDonorOriginal

/-! A third actual singleton removes the root edge from an ordered donor.
Every interior position and every interior color are retained explicitly. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k s : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_three_singleton_tail (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b h : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hvh : G.Adj v h)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (hhunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨h, hvh.ne.symm⟩ → z = h)
    (hab : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (hah : c ⟨a, hva.ne.symm⟩ ≠ c ⟨h, hvh.ne.symm⟩)
    (hbh : c ⟨b, hvb.ne.symm⟩ ≠ c ⟨h, hvh.ne.symm⟩)
    (hsk : s + 3 ≤ k) (D : Fin s → Fin k) (hD : Function.Injective D)
    (hDa : ∀ i, D i ≠ c ⟨a, hva.ne.symm⟩)
    (hDb : ∀ i, D i ≠ c ⟨b, hvb.ne.symm⟩)
    (hDh : ∀ i, D i ≠ c ⟨h, hvh.ne.symm⟩) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = s + 1 ∧
      v ∉ q.support ∧ h ∉ q.support ∧
      (∀ i : Fin s, ∃ hz : q.getVert (i.val + 1) ≠ v,
        c ⟨q.getVert (i.val + 1), hz⟩ = D i) ∧
      (∀ (z : V) (hzv : z ≠ v), z ∈ q.support → z ≠ a → z ≠ b →
        ∃ i : Fin s, c ⟨z, hzv⟩ = D i) := by
  classical
  let E : Fin (s + 1) → Fin k := Fin.cons (c ⟨a, hva.ne.symm⟩) D
  have hE : Function.Injective E := by
    apply Fin.cons_injective_of_injective _ hD
    rintro ⟨i, hi⟩
    exact hDa i hi
  have hEh : ∀ i, E i ≠ c ⟨h, hvh.ne.symm⟩ := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [E, Fin.cons_zero] using hah
    | succ i => simpa only [E, Fin.cons_succ] using hDh i
  have hEb : ∀ i, E i ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [E, Fin.cons_zero] using hab
    | succ i => simpa only [E, Fin.cons_succ] using hDb i
  obtain ⟨p, hp, hplen, hhp, hword, _⟩ :=
    equality_original_ordered_singleton_donor hk hcrit hcount hvh hvb c
      hhunique hbunique hbh.symm (by omega) E hE hEh hEb
  obtain ⟨w, e, q, rfl⟩ := Walk.exists_eq_cons_of_ne hvb.ne p
  obtain ⟨hwv, hwc⟩ := hword 0
  have hwcolor : c ⟨w, e.ne.symm⟩ = c ⟨a, hva.ne.symm⟩ := by
    have hzero : (Walk.cons e q).getVert ((0 : Fin (s + 1)).val + 1) = w := by
      change q.getVert 0 = w
      exact Walk.getVert_zero q
    have hsubzero : (⟨(Walk.cons e q).getVert ((0 : Fin (s + 1)).val + 1), hwv⟩ :
        {z : V // z ≠ v}) = ⟨w, e.ne.symm⟩ := Subtype.ext hzero
    have hca : c ⟨(Walk.cons e q).getVert ((0 : Fin (s + 1)).val + 1), hwv⟩ =
        c ⟨a, hva.ne.symm⟩ := hwc
    exact (congrArg (fun t : {z : V // z ≠ v} => c t) hsubzero).symm.trans hca
  have hwa : w = a := haunique w e.ne.symm e hwcolor
  subst w
  have hq : q.IsPath := hp.of_cons
  have hvq : v ∉ q.support := (Walk.cons_isPath_iff e q).mp hp |>.2
  have hhq : h ∉ q.support := by
    intro hh
    apply hhp
    exact List.mem_cons_of_mem _ hh
  have hqlen : q.length = s + 1 := by
    simp only [Walk.length_cons] at hplen
    omega
  have hqword : ∀ i : Fin s, ∃ hz : q.getVert (i.val + 1) ≠ v,
      c ⟨q.getVert (i.val + 1), hz⟩ = D i := by
    intro i
    obtain ⟨hz, hc⟩ := hword i.succ
    refine ⟨by simpa only [Fin.val_succ, Nat.add_assoc, Walk.getVert_cons_succ] using hz, ?_⟩
    simpa only [Fin.val_succ, Nat.add_assoc, Walk.getVert_cons_succ, E, Fin.cons_succ] using hc
  refine ⟨q, hq, hqlen, hvq, hhq, hqword, ?_⟩
  intro z hzv hzq hza hzb
  obtain ⟨n, hnz, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
  have hn0 : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    exact hza (by simpa only [he, Walk.getVert_zero] using hnz.symm)
  have hnl : n < q.length := by
    by_contra hh
    have he : n = q.length := by omega
    exact hzb (by simpa only [he, Walk.getVert_length] using hnz.symm)
  let i : Fin s := ⟨n - 1, by omega⟩
  obtain ⟨hz, hc⟩ := hqword i
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hv : q.getVert (i.val + 1) = z := by rw [hi]; exact hnz
  refine ⟨i, ?_⟩
  have he : (⟨q.getVert (i.val + 1), hz⟩ : {z : V // z ≠ v}) = ⟨z, hzv⟩ :=
    Subtype.ext hv
  exact (congrArg c he).symm.trans hc

end TaskH.General

#print axioms TaskH.General.equality_original_three_singleton_tail
