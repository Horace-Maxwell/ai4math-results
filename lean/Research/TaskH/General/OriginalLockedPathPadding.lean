import Research.TaskH.General.OriginalKempePathTransport

/-! The donor is chosen internally from the ORIGINAL equality graph.
For x>=k its s=2k-x-3 unused colors exist and give an actual C_(2k).
No padding assertion is made at x=k-1, where the palette would be too small. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_two_color_path_no_long_padding (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (a b q : {z : V // z ≠ v}) (hva : G.Adj v a.val) (hvb : G.Adj v b.val)
    (hqb : G.Adj q.val b.val)
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c a → z = a.val)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c b → z = b.val)
    (habcolor : c a ≠ c b) (hqa : c q ≠ c a) (hqbcolor : c q ≠ c b)
    (p : (G.induce {z | z ≠ v}).Walk a q) (hp : p.IsPath)
    (hf : _root_.TaskH.Follows p c (Equiv.swap (c a) (c q)))
    (hupper : p.length ≤ 2 * k - 5) : p.length < k := by
  classical
  by_contra hn
  have hlarge : k ≤ p.length := by omega
  let s := 2 * k - p.length - 3
  have hsk : s + 3 ≤ k := by dsimp [s]; omega
  let S : Finset (Fin k) := {c a, c b, c q}
  have hS : S.card ≤ 3 := by
    calc
      S.card ≤ ({c b, c q} : Finset (Fin k)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 3 := by
        have hh := Finset.card_insert_le (c b) ({c q} : Finset (Fin k))
        simp only [Finset.card_singleton] at hh
        omega
  obtain ⟨D, hD, hDS⟩ := exists_color_list_avoiding_palette S (by omega : s + S.card ≤ k)
  have hDa : ∀ i, D i ≠ c a := by
    intro i he
    apply hDS i
    rw [he]
    exact Finset.mem_insert_self (c a) {c b, c q}
  have hDb : ∀ i, D i ≠ c b := by
    intro i he
    apply hDS i
    rw [he]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hDq : ∀ i, D i ≠ c q := by
    intro i he
    apply hDS i
    rw [he]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨d, hd, hdlen, _, _, hdcover⟩ := equality_original_ordered_singleton_donor
    (by omega) hcrit hcount hvb hva c hbunique haunique habcolor.symm (by omega)
    D hD hDb hDa
  let L := originalDeletedLift v p
  have hL : L.IsPath := originalDeletedLift_isPath v p hp
  have hbL : b.val ∉ L.support := by
    intro hm
    obtain ⟨w, hw, hc | hc⟩ := originalDeletedLift_mem_colors v c (c q) p hf hm
    · have he : w = b := Subtype.ext hw
      exact habcolor (hc.symm.trans (congrArg c he))
    · have he : w = b := Subtype.ext hw
      exact hqbcolor (hc.symm.trans (congrArg c he))
  let R : G.Walk a.val v := (L.concat hqb).concat hvb.symm
  have hvL : v ∉ L.support := originalDeletedLift_avoids_root v p
  have hvLb : v ∉ (L.concat hqb).support := by
    rw [Walk.support_concat, List.mem_append, List.mem_singleton]
    exact fun hh => hh.elim hvL (fun he => b.property he.symm)
  have hR : R.IsPath := (hL.concat hbL hqb).concat hvLb hvb.symm
  have hLiftLen : L.length = p.length := by
    change (p.map (originalDeletedHom (G := G) v)).length = p.length
    exact Walk.length_map (originalDeletedHom (G := G) v) p
  have hRlen : R.length = p.length + 2 := by
    change ((L.concat hqb).concat hvb.symm).length = p.length + 2
    rw [Walk.length_concat, Walk.length_concat, hLiftLen]
  have hRcolors : ∀ (z : V) (hzv : z ≠ v), z ∈ R.support →
      c ⟨z, hzv⟩ = c a ∨ c ⟨z, hzv⟩ = c b ∨ c ⟨z, hzv⟩ = c q := by
    intro z hzv hz
    change z ∈ ((L.concat hqb).concat hvb.symm).support at hz
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | he
    · rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | he
      · obtain ⟨w, hw, hc | hc⟩ := originalDeletedLift_mem_colors v c (c q) p hf hz
        · exact Or.inl ((congrArg c (Subtype.ext hw)).symm.trans hc)
        · exact Or.inr (Or.inr ((congrArg c (Subtype.ext hw)).symm.trans hc))
      · exact Or.inr (Or.inl (congrArg c (Subtype.ext he)))
    · exact False.elim (hzv he)
  have hdv : v ∉ d.support.tail := by
    have hh := hd.support_nodup
    rw [← d.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hRa : a.val ∉ R.support.tail := by
    have hh := hR.support_nodup
    rw [← R.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hdisj : d.support.tail.Disjoint R.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzd hzR
    have hzv : z ≠ v := fun he => hdv (he ▸ hzd)
    have hza : z ≠ a.val := fun he => hRa (he ▸ hzR)
    obtain ⟨i, hci⟩ := hdcover z hzv (List.mem_of_mem_tail hzd) hza
    rcases hRcolors z hzv (List.mem_of_mem_tail hzR) with hc | hc | hc
    · exact hDa i (hci.symm.trans hc)
    · exact hDb i (hci.symm.trans hc)
    · exact hDq i (hci.symm.trans hc)
  let C := d.append R
  have hC : C.IsCycle := hd.isCycle_append hR hdisj (Or.inr (by omega))
  have hClen : C.length = 2 * k := by
    change (d.append R).length = 2 * k
    rw [Walk.length_append, hdlen, hRlen]
    dsimp [s]
    omega
  have he := GoodCycles.equality_shortCycles_from_critical_count (by omega) hcrit hcount
    C hC (by rw [hClen]; exact dvd_mul_left k 2)
  omega

/-- Original hypotheses force EVERY actual locked opposite-side row to have
the exceptional length k-1. In particular any such row forces k even. -/
theorem equality_original_locked_path_exact_even (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (a b q : {z : V // z ≠ v}) (hva : G.Adj v a.val) (hvb : G.Adj v b.val)
    (hvq : G.Adj v q.val) (hqb : G.Adj q.val b.val)
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c a → z = a.val)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c b → z = b.val)
    (habcolor : c a ≠ c b) (hqa : c q ≠ c a) (hqbcolor : c q ≠ c b)
    (haq : ¬G.Adj a.val q.val)
    (hreach : q ∈ _root_.TaskH.Seven.twoColorComponent c (c a) (c q) a) :
    ∃ p : (G.induce {z | z ≠ v}).Walk a q,
      p.IsPath ∧ _root_.TaskH.Follows p c (Equiv.swap (c a) (c q)) ∧
      p.length = k - 1 ∧ k % 2 = 0 := by
  obtain ⟨p, hp, hf, hodd, hlo, hup⟩ := equality_original_locked_path_range
    (by omega) hcrit hcount c a b q hva hvb hvq haunique hbunique habcolor hqa haq hreach
  have hlt := equality_original_two_color_path_no_long_padding hk hcrit hcount
    c a b q hva hvb hqb haunique hbunique habcolor hqa hqbcolor p hp hf hup
  exact ⟨p, hp, hf, by omega, by omega⟩

end TaskH.General
#print axioms TaskH.General.equality_original_two_color_path_no_long_padding
#print axioms TaskH.General.equality_original_locked_path_exact_even
