import Research.TaskH.General.OriginalLockedPathPadding

/-! Two actual opposite-side locked rows in different non-singleton colors
cannot coexist. Their simple paths are chosen internally; the four old colors
give genuine support disjointness and close the actual C_(2k). -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_two_distinct_locked_rows_impossible (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (a b q t : {z : V // z ≠ v}) (hva : G.Adj v a.val) (hvb : G.Adj v b.val)
    (hvq : G.Adj v q.val) (hvt : G.Adj v t.val)
    (hqb : G.Adj q.val b.val) (hta : G.Adj t.val a.val)
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c a → z = a.val)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c b → z = b.val)
    (habcolor : c a ≠ c b) (hqa : c q ≠ c a) (hqbcolor : c q ≠ c b)
    (htaColor : c t ≠ c a) (htb : c t ≠ c b) (hqt : c q ≠ c t)
    (haq : ¬G.Adj a.val q.val) (hbt : ¬G.Adj b.val t.val)
    (hreachA : q ∈ _root_.TaskH.Seven.twoColorComponent c (c a) (c q) a)
    (hreachB : t ∈ _root_.TaskH.Seven.twoColorComponent c (c b) (c t) b) : False := by
  classical
  obtain ⟨p, hp, hf, hplen, _⟩ := equality_original_locked_path_exact_even hk hcrit hcount
    c a b q hva hvb hvq hqb haunique hbunique habcolor hqa hqbcolor haq hreachA
  obtain ⟨r, hr, hg, hrlen, _⟩ := equality_original_locked_path_exact_even hk hcrit hcount
    c b a t hvb hva hvt hta hbunique haunique habcolor.symm htb htaColor hbt hreachB
  let L := originalDeletedLift v p
  let M := originalDeletedLift v r
  have hL : L.IsPath := originalDeletedLift_isPath v p hp
  have hM : M.IsPath := originalDeletedLift_isPath v r hr
  have hdisj : L.support.Disjoint M.support := by
    apply List.disjoint_left.mpr
    intro z hzL hzM
    obtain ⟨w, hw, hc | hc⟩ := originalDeletedLift_mem_colors v c (c q) p hf hzL
    · obtain ⟨w', hw', hc' | hc'⟩ := originalDeletedLift_mem_colors v c (c t) r hg hzM
      · exact habcolor (hc.symm.trans ((congrArg c (Subtype.ext (hw.trans hw'.symm))).trans hc'))
      · exact htaColor ((hc.symm.trans ((congrArg c (Subtype.ext (hw.trans hw'.symm))).trans hc')).symm)
    · obtain ⟨w', hw', hc' | hc'⟩ := originalDeletedLift_mem_colors v c (c t) r hg hzM
      · exact hqbcolor (hc.symm.trans ((congrArg c (Subtype.ext (hw.trans hw'.symm))).trans hc'))
      · exact hqt (hc.symm.trans ((congrArg c (Subtype.ext (hw.trans hw'.symm))).trans hc'))
  have hbL : b.val ∉ L.support := by
    intro hh
    exact List.disjoint_left.mp hdisj hh M.start_mem_support
  have haM : a.val ∉ M.support := by
    intro hh
    exact List.disjoint_left.mp hdisj L.start_mem_support hh
  let P := L.concat hqb
  let R := M.concat hta
  have hP : P.IsPath := hL.concat hbL hqb
  have hR : R.IsPath := hM.concat haM hta
  have hPa : a.val ∉ P.support.tail := by
    have hh := hP.support_nodup
    rw [← P.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have hRb : b.val ∉ R.support.tail := by
    have hh := hR.support_nodup
    rw [← R.cons_tail_support, List.nodup_cons] at hh
    exact hh.1
  have htails : P.support.tail.Disjoint R.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzP hzR
    have hsP := List.mem_of_mem_tail hzP
    have hsR := List.mem_of_mem_tail hzR
    change z ∈ (L.concat hqb).support at hsP
    change z ∈ (M.concat hta).support at hsR
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hsP hsR
    rcases hsP with hzL | he
    · rcases hsR with hzM | he
      · exact List.disjoint_left.mp hdisj hzL hzM
      · exact hPa (he ▸ hzP)
    · exact hRb (he ▸ hzR)
  have hL_length : L.length = p.length := by
    change (p.map (originalDeletedHom (G := G) v)).length = p.length
    exact Walk.length_map (originalDeletedHom (G := G) v) p
  have hM_length : M.length = r.length := by
    change (r.map (originalDeletedHom (G := G) v)).length = r.length
    exact Walk.length_map (originalDeletedHom (G := G) v) r
  have hP_length : P.length = k := by
    change (L.concat hqb).length = k
    rw [Walk.length_concat, hL_length, hplen]
    omega
  have hR_length : R.length = k := by
    change (M.concat hta).length = k
    rw [Walk.length_concat, hM_length, hrlen]
    omega
  let C := P.append R
  have hC : C.IsCycle := hP.isCycle_append hR htails (Or.inl (by
    rw [hP_length]
    omega))
  have hClen : C.length = 2 * k := by
    change (P.append R).length = 2 * k
    rw [Walk.length_append, hP_length, hR_length]
    omega
  have he := GoodCycles.equality_shortCycles_from_critical_count (by omega) hcrit hcount
    C hC (by rw [hClen]; exact dvd_mul_left k 2)
  omega

end TaskH.General
#print axioms TaskH.General.equality_original_two_distinct_locked_rows_impossible
