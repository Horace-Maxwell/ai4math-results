import Research.TaskP.RectangleDefect.RectCounts

namespace TaskP.RectangleDefect
open Challenge

def heavy {k : ℕ} (T : ℕ) (m : Counts k) : Finset (Fin k) :=
  Finset.univ.filter (fun i => T ≤ m i)

private def pivot {k : ℕ} (hk : 0 < k) (J : Finset (Fin k)) : Fin k :=
  if h : J.Nonempty then J.min' h else ⟨0,hk⟩

private theorem off_pivot {k : ℕ} (hk : 0 < k) (J : Finset (Fin k)) {e : ℕ}
    (h : J.card ≤ e+1) : (J.erase (pivot hk J)).card ≤ e := by
  by_cases hn : J.Nonempty
  · have hm : pivot hk J ∈ J := by unfold pivot; split <;> solve_by_elim [Finset.min'_mem]
    rw [Finset.card_erase_of_mem hm];omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

private theorem forced_entry {k : ℕ} (j : Fin k) {m m' : Counts k} (h : area m = area m')
    (he : ∀ i, i ≠ j → m i = m' i) : m j = m' j := by
  unfold area at h
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase Finset.univ (fun i => (i.val+1)*m' i) (Finset.mem_univ j)] at h
  have hs : ∑ i ∈ Finset.univ.erase j, (i.val+1)*m i =
      ∑ i ∈ Finset.univ.erase j, (i.val+1)*m' i := Finset.sum_congr rfl fun i hi => by
    rw [he i (Finset.mem_erase.mp hi).1]
  rw [hs] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < j.val+1) (Nat.add_right_cancel h)

private def smallCode {k : ℕ} (T : ℕ) (m : Counts k) (i : Fin k) : Fin (T+1) :=
  if h : m i < T then ⟨m i,by omega⟩ else 0

private def bigCode {k n e : ℕ} (hk : 0 < k) (J : Finset (Fin k))
    (m : Counts k) (hm : area m = 2*n) (j : Fin e) : Fin (2*n+1) :=
  let E := J.erase (pivot hk J)
  if h : j.val < E.card then
    let i := E.orderEmbOfFin rfl ⟨j.val,h⟩
    ⟨m i,by have := entry_le_area m i;omega⟩
  else 0

private theorem big_recovers {k n e : ℕ} (hk : 0 < k) (J : Finset (Fin k)) (hc : J.card ≤ e+1)
    {m m' : Counts k} {hm : area m=2*n} {hm' : area m'=2*n}
    (eq : bigCode (e:=e) hk J m hm = bigCode hk J m' hm') {i : Fin k}
    (hi : i ∈ J.erase (pivot hk J)) : m i = m' i := by
  let E := J.erase (pivot hk J)
  let ie := (E.orderIsoOfFin rfl).symm ⟨i,hi⟩
  have hmax : E.card ≤ e := off_pivot hk J hc
  let j : Fin e := ⟨ie.val,lt_of_lt_of_le ie.isLt hmax⟩
  have hj : j.val < E.card := ie.isLt
  have hp : E.orderEmbOfFin rfl ie = i := congrArg Subtype.val ((E.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)
  have r := congrArg Fin.val (congrFun eq j)
  have hj' : j.val < (J.erase (pivot hk J)).card := hj
  have hp' : (J.erase (pivot hk J)).orderEmbOfFin rfl ⟨j.val,hj'⟩ = i := hp
  simpa [bigCode,hj',hp'] using r

theorem count_with_sparse_heavy {k T e n : ℕ} (hk : 0 < k)
    (bound : ∀ m ∈ failures k n, (heavy T m).card ≤ e+1) :
    defect k n ≤ 2^k * (T+1)^k * (2*n+1)^e := by
  classical
  let K := Finset (Fin k) × (Fin k → Fin (T+1)) × (Fin e → Fin (2*n+1))
  let enc (x : failures k n) : K :=
    (heavy T x.1,smallCode T x.1,bigCode hk (heavy T x.1) x.1 x.2.1)
  have inj : Function.Injective enc := by
    intro x y eq
    have J : heavy T x.1 = heavy T y.1 := congrArg Prod.fst eq
    have sm : smallCode T x.1 = smallCode T y.1 := congrArg (fun t : K => t.2.1) eq
    have big : bigCode hk (heavy T x.1) x.1 x.2.1 = bigCode (e:=e) hk (heavy T x.1) y.1 y.2.1 := by
      simpa only [enc,J] using congrArg (fun t : K => t.2.2) eq
    let j := pivot hk (heavy T x.1)
    have other (i : Fin k) (hi : i ≠ j) : x.1 i = y.1 i := by
      by_cases hm : i ∈ heavy T x.1
      · exact big_recovers hk _ (bound x.1 x.2) big (Finset.mem_erase.mpr ⟨hi,hm⟩)
      · have hy : i ∉ heavy T y.1 := J ▸ hm
        simp [heavy] at hm hy
        simpa [smallCode,hm,hy] using congrArg Fin.val (congrFun sm i)
    apply Subtype.ext
    funext i
    by_cases hi : i=j
    · subst i
      exact forced_entry j (x.2.1.trans y.2.1.symm) other
    · exact other i hi
  rw [defect_eq_failures,← Nat.card_coe_set_eq]
  have h := Nat.card_le_card_of_injective enc inj
  simpa [K,Nat.card_eq_fintype_card,mul_assoc] using h

end TaskP.RectangleDefect
