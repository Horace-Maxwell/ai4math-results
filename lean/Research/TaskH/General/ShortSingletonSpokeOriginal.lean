import Research.TaskH.General.OrderedSingletonDonorOriginal
import Research.TaskH.General.FiniteColorAvoidance

/-! A complete original short-spoke structure branch. For two actual singleton
neighbor colors in one fixed whole G-v coloring, every simple b-v path with
2 ≤ length and length+1 ≤ k is rainbow off v. Its edge vb is a real spoke,
not a chord. The complementary donor and actual k-cycle are built internally;
no palette-capacity, donor, rainbow, or target-cycle oracle is an input. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem path_getVert_before_end_ne {a v : V} (q : G.Walk a v) (hq : q.IsPath)
    (i : Fin q.length) : q.getVert i.val ≠ v := by
  intro he
  have hi := (hq.getVert_eq_end_iff (Nat.le_of_lt i.isLt)).mp he
  have := i.isLt
  omega

/-- The complete actual color word of a path before its deleted endpoint. -/
def deletedPathColorWord {a v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (q : G.Walk a v) (hq : q.IsPath) (i : Fin q.length) : Fin k :=
  c ⟨q.getVert i.val, path_getVert_before_end_ne q hq i⟩

omit [Fintype V] in
theorem deletedPathColorWord_support_palette {a v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (q : G.Walk a v) (hq : q.IsPath) (z : V) (hzv : z ≠ v)
    (hzq : z ∈ q.support) :
    c ⟨z, hzv⟩ ∈ Finset.univ.image (deletedPathColorWord c q hq) := by
  classical
  obtain ⟨n, hnz, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
  have hnl : n < q.length := by
    by_contra hh
    have he : n = q.length := by omega
    exact hzv (by simpa only [he, Walk.getVert_length] using hnz.symm)
  refine Finset.mem_image.mpr ⟨⟨n, hnl⟩, Finset.mem_univ _, ?_⟩
  apply congrArg c
  exact Subtype.ext hnz

/-- Every short actual spoke cycle through either singleton edge is rainbow
off the deleted root, under the original criticality and equality count. -/
theorem equality_original_short_singleton_spoke_rainbow (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (q : G.Walk b v) (hq : q.IsPath) (hL2 : 2 ≤ q.length)
    (hLk : q.length + 1 ≤ k) :
    Function.Injective (deletedPathColorWord c q hq) := by
  classical
  by_contra hnot
  let F := deletedPathColorWord c q hq
  let T := Finset.univ.image F
  have hTle : T.card ≤ q.length := by
    simpa only [T, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le : (Finset.univ.image F).card ≤ (Finset.univ : Finset (Fin q.length)).card)
  have hTlt : T.card < q.length := by
    by_contra hh
    have heq : (Finset.univ.image F).card = (Finset.univ : Finset (Fin q.length)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      change T.card = q.length
      omega
    have hi := Finset.card_image_iff.mp heq
    apply hnot
    intro i j hij
    exact hi (Finset.mem_univ _) (Finset.mem_univ _) hij
  let α := c ⟨a, hva.ne.symm⟩
  let β := c ⟨b, hvb.ne.symm⟩
  let S := insert α T
  let s := k - (q.length + 1)
  have hSle : S.card ≤ T.card + 1 := Finset.card_insert_le _ _
  have hcap : s + S.card ≤ k := by dsimp [s]; omega
  obtain ⟨D, hD, hDS⟩ := exists_color_list_avoiding_palette S hcap
  have hβT : β ∈ T := by
    refine Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    change c ⟨q.getVert 0, _⟩ = c ⟨b, hvb.ne.symm⟩
    apply congrArg c
    apply Subtype.ext
    exact q.getVert_zero
  have hDa : ∀ i, D i ≠ α := by
    intro i he
    apply hDS i
    rw [he]
    exact Finset.mem_insert_self _ _
  have hDb : ∀ i, D i ≠ β := by
    intro i he
    apply hDS i
    rw [he]
    exact Finset.mem_insert_of_mem hβT
  obtain ⟨p, hp, hplen, _, _, hcover⟩ := equality_original_ordered_singleton_donor
    hk hcrit hcount hva hvb c haunique hbunique habcolor (by dsimp [s]; omega)
    D hD hDa hDb
  have hpv : v ∉ p.support.tail := by
    have hh := hp.support_nodup
    rw [← p.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hqb : b ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzP hzQ
    have hzv : z ≠ v := by intro he; subst z; exact hpv hzP
    have hzb : z ≠ b := by intro he; subst z; exact hqb hzQ
    obtain ⟨i, hci⟩ := hcover z hzv (List.mem_of_mem_tail hzP) hzb
    apply hDS i
    apply Finset.mem_insert_of_mem
    rw [← hci]
    exact deletedPathColorWord_support_palette c q hq z hzv (List.mem_of_mem_tail hzQ)
  let w := p.append q
  have hw : w.IsCycle := hp.isCycle_append hq hdisj (Or.inr (by omega))
  have hwlen : w.length = k := by
    change (p.append q).length = k
    rw [Walk.length_append, hplen]
    dsimp [s]
    omega
  apply hnot
  intro i j hij
  have hiq : q.getVert i.val ∈ w.support :=
    Walk.support_subset_support_append_right p q (q.getVert_mem_support i.val)
  have hjq : q.getVert j.val ∈ w.support :=
    Walk.support_subset_support_append_right p q (q.getVert_mem_support j.val)
  have he : q.getVert i.val = q.getVert j.val :=
    equality_original_cycle_support_rainbow hk hcrit hcount c w hw hwlen hiq hjq
      (path_getVert_before_end_ne q hq i) (path_getVert_before_end_ne q hq j) hij
  apply Fin.ext
  exact hq.getVert_injOn (by change i.val ≤ q.length; omega)
    (by change j.val ≤ q.length; omega) he

end TaskH.General

#print axioms TaskH.General.path_getVert_before_end_ne
#print axioms TaskH.General.deletedPathColorWord
#print axioms TaskH.General.deletedPathColorWord_support_palette
#print axioms TaskH.General.equality_original_short_singleton_spoke_rainbow
