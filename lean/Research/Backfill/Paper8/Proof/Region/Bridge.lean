import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Region.Enum
import Research.Backfill.Paper8.Proof.Real.Main

/-!
# Region search: trees and multisets (agent `region`)

The multiset `msOf T` of a tree `T = [(b₁, k₁), …]` and its data (`B`, `k_b`, `b*`, `|m|`, `∑ m`,
`sq`, `ν`, `M`, the value of `R`), then the equivalence of `InRegion (msOf T)` with the choice
conditions that define `enum` (using Lemma 4.1, proved in `Research.Backfill.Paper8.Proof.Real`). Consequence: the region
`ℛ` is the image of `enum` under `msOf`, which is injective on `enum`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial

namespace P8Region

/-- The multiset of branch sizes of the tree `T`. -/
def msOf (T : List (ℕ × ℕ)) : Multiset ℕ := (T.map (fun p => Multiset.replicate p.2 p.1)).sum

theorem msOf_cons (p : ℕ × ℕ) (T : List (ℕ × ℕ)) :
    msOf (p :: T) = Multiset.replicate p.2 p.1 + msOf T := by
  simp [msOf]

theorem kOf_cons (p : ℕ × ℕ) (T : List (ℕ × ℕ)) (x : ℕ) :
    kOf (p :: T) x = (if p.1 = x then p.2 else 0) + kOf T x := by
  simp [kOf]

theorem count_msOf (T : List (ℕ × ℕ)) (x : ℕ) : (msOf T).count x = kOf T x := by
  induction T with
  | nil => simp [msOf, kOf]
  | cons p T ih =>
    rw [msOf_cons, Multiset.count_add, Multiset.count_replicate, ih, kOf_cons]

theorem kb_msOf (T : List (ℕ × ℕ)) (x : ℕ) : kb (msOf T) x = kOf T x := count_msOf T x

theorem kOf_eq_zero {T : List (ℕ × ℕ)} {x : ℕ} (hx : x ∉ T.map Prod.fst) : kOf T x = 0 := by
  induction T with
  | nil => simp [kOf]
  | cons p T ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [kOf_cons, ih hx.2]
    simp [Ne.symm hx.1]

theorem kOf_of_mem {T : List (ℕ × ℕ)} (hT : (T.map Prod.fst).Nodup) {p : ℕ × ℕ} (hp : p ∈ T) :
    kOf T p.1 = p.2 := by
  induction T with
  | nil => simp at hp
  | cons q T ih =>
    rw [List.map_cons, List.nodup_cons] at hT
    rw [kOf_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [kOf_eq_zero hT.1]
      simp
    · have hne : q.1 ≠ p.1 := fun h => hT.1 (h ▸ List.mem_map_of_mem hp)
      rw [ih hT.2 hp]
      simp [hne]

theorem kOf_pos_iff {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) (x : ℕ) :
    0 < kOf T x ↔ x ∈ T.map Prod.fst := by
  induction T with
  | nil => simp [kOf]
  | cons p T ih =>
    have hp := hpos p List.mem_cons_self
    have ih' := ih (fun q hq => hpos q (List.mem_cons_of_mem _ hq))
    rw [kOf_cons, List.map_cons, List.mem_cons, ← ih']
    by_cases h : p.1 = x
    · simp only [h, ite_true, true_or, iff_true]
      omega
    · simp only [h, ite_false, zero_add]
      constructor
      · intro h'
        exact Or.inr h'
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'

theorem mem_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) (x : ℕ) :
    x ∈ msOf T ↔ x ∈ T.map Prod.fst := by
  rw [← Multiset.count_pos, count_msOf, kOf_pos_iff hpos]

theorem Bset_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) :
    Bset (msOf T) = (T.map Prod.fst).toFinset := by
  ext x
  rw [Bset, Multiset.mem_toFinset, mem_msOf hpos, List.mem_toFinset]

theorem card_msOf (T : List (ℕ × ℕ)) : Multiset.card (msOf T) = sumK T := by
  induction T with
  | nil => simp [msOf, sumK]
  | cons p T ih =>
    rw [msOf_cons, Multiset.card_add, Multiset.card_replicate, ih]
    simp [sumK]

theorem sum_msOf (T : List (ℕ × ℕ)) : (msOf T).sum = (T.map (fun p => p.1 * p.2)).sum := by
  induction T with
  | nil => simp [msOf]
  | cons p T ih =>
    rw [msOf_cons, Multiset.sum_add, Multiset.sum_replicate, ih]
    simp [mul_comm]

theorem sup_toFinset (l : List ℕ) : l.toFinset.sup id = bsOf l := by
  induction l with
  | nil => simp [bsOf]
  | cons a l ih =>
    rw [List.toFinset_cons, Finset.sup_insert, ih]
    simp [bsOf]

theorem bstar_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) :
    bstar (msOf T) = bsOf (T.map Prod.fst) := by
  rw [bstar, Bset_msOf hpos, sup_toFinset]

theorem le_bsOf {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ bsOf l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [bsOf, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem bsOf_le {l : List ℕ} {c : ℕ} (h : ∀ x ∈ l, x ≤ c) : bsOf l ≤ c := by
  induction l with
  | nil => simp [bsOf]
  | cons a l ih =>
    simp only [bsOf, List.foldr_cons] at ih ⊢
    exact max_le (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem sqCountB_toFinset (Bl : List ℕ) (bs : ℕ) : sqCountB Bl.toFinset bs = sqC Bl bs := by
  have h : (Finset.Icc 1 bs).filter (fun q => q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ Bl.toFinset) =
      ((List.range' 1 bs).filter (fun q => q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ Bl)).toFinset := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter,
      List.mem_range'_1, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
  rw [sqCountB, h, List.toFinset_card_of_nodup ((List.nodup_range' ..).filter _), sqC]

theorem nuB_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) (hnd : (T.map Prod.fst).Nodup) :
    nuB (Bset (msOf T)) (bstar (msOf T)) = nuC (T.map Prod.fst) := by
  rw [nuB, nuC, bstar_msOf hpos, Bset_msOf hpos, sqCountB_toFinset,
    List.toFinset_card_of_nodup hnd]

theorem MB_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2) (hnd : (T.map Prod.fst).Nodup) :
    MB (Bset (msOf T)) (bstar (msOf T)) = MC (T.map Prod.fst) := by
  rw [MB, MC, nuB_msOf hpos hnd, Bset_msOf hpos, List.toFinset_card_of_nodup hnd]

theorem card_Bset_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2)
    (hnd : (T.map Prod.fst).Nodup) : (Bset (msOf T)).card = T.length := by
  rw [Bset_msOf hpos, List.toFinset_card_of_nodup hnd, List.length_map]

/-- `PS` computes the two parts of `R(t)`. -/
theorem PS_eq (t : ℤ) (κ : ℕ → ℕ) : ∀ (T : List (ℕ × ℕ)), (T.map Prod.fst).Nodup →
    (∀ p ∈ T, κ p.1 = p.2) →
    PS t T = (∏ b ∈ (T.map Prod.fst).toFinset, (t - (b : ℤ)),
      ∑ b ∈ (T.map Prod.fst).toFinset,
        (κ b : ℤ) * ∏ b' ∈ ((T.map Prod.fst).toFinset).erase b, (t - (b' : ℤ)))
  | [], _, _ => by simp [PS]
  | p :: T, hnd, hκ => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := PS_eq t κ T hnd.2 (fun q hq => hκ q (List.mem_cons_of_mem _ hq))
    have hnot : p.1 ∉ (T.map Prod.fst).toFinset := by
      rw [List.mem_toFinset]
      exact hnd.1
    rw [PS, ih, PSstep, List.map_cons, List.toFinset_cons, Finset.prod_insert hnot,
      Finset.sum_insert hnot, Finset.erase_insert hnot, hκ p List.mem_cons_self]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hne : p.1 ≠ b := fun h => hnot (h ▸ hb)
    have hnot' : p.1 ∉ ((T.map Prod.fst).toFinset).erase b :=
      fun h => hnot (Finset.mem_of_mem_erase h)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert hnot']
    ring

/-- `evalR T t = R(t)` for the multiset of `T`. -/
theorem eval_secular_msOf {T : List (ℕ × ℕ)} (hpos : ∀ p ∈ T, 1 ≤ p.2)
    (hnd : (T.map Prod.fst).Nodup) (t : ℤ) : (secular (msOf T)).eval t = evalR T t := by
  have h := PS_eq t (kOf T) T hnd (fun p hp => kOf_of_mem hnd hp)
  rw [evalR, h, secular, Bset_msOf hpos]
  simp [eval_prod, eval_finsetSum, kb_msOf]

/-- `|ℒ_β(k)| = Lof β k` (Lemma 4.1). -/
theorem ncard_Lset {β k : ℕ} (hβ : 1 ≤ β) (hk : 1 ≤ k) : (Lset β k).ncard = Lof β k := by
  obtain ⟨h2, h1, h11⟩ := P8Real.check_Lemma_4_1 β k hβ hk
  rcases Nat.lt_or_ge β 2 with hb | hb
  · obtain rfl : β = 1 := by omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      rw [(h11 rfl rfl).2]
      rfl
    · rw [(h1 rfl hk2).2]
      simp [Lof, show k ≠ 1 by omega]
  · rw [(h2 hb).2]
    simp [Lof, show β ≠ 1 by omega]

theorem sub_one_le_Lof {β k : ℕ} (hβ : 1 ≤ β) : k - 1 ≤ Lof β k := by
  unfold Lof
  by_cases h1 : β = 1
  · subst h1
    by_cases hk : k = 1 <;> simp [hk]
  · have h2 : 2 * k ≤ k * β := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left k (by omega)
    simp only [h1, ite_false]
    split_ifs <;> omega

theorem one_le_of_mem_choices {Bl : List ℕ} {b k : ℕ} (h : k ∈ choices Bl b) : 1 ≤ k := by
  unfold choices at h
  split_ifs at h
  · exact (List.mem_range'_1.1 h).1
  · exact (List.mem_range'_1.1 (List.mem_filter.1 h).1).1

/-- `InRegion (msOf T)` is the choice condition of `enum`. -/
theorem inRegion_msOf_iff {T : List (ℕ × ℕ)} (hsub : (T.map Prod.fst).Sublist (List.range 13))
    (hbs : 2 ≤ bsOf (T.map Prod.fst)) (hpos : ∀ p ∈ T, 1 ≤ p.2) :
    InRegion (msOf T) ↔ ∀ p ∈ T, p.2 ∈ choices (T.map Prod.fst) p.1 := by
  have hnd : (T.map Prod.fst).Nodup := List.nodup_range.sublist hsub
  have h12 : bsOf (T.map Prod.fst) ≤ 12 := by
    apply bsOf_le
    intro x hx
    have := List.mem_range.1 (hsub.subset hx)
    omega
  unfold InRegion
  rw [nuB_msOf hpos hnd, MB_msOf hpos hnd, bstar_msOf hpos, Bset_msOf hpos,
    List.toFinset_card_of_nodup hnd]
  simp only [kb_msOf]
  constructor
  · rintro ⟨-, -, hL, h0⟩ p hp
    have hk := kOf_of_mem hnd hp
    have hp1 := hpos p hp
    unfold choices
    split_ifs with hb
    · rw [List.mem_range'_1]
      have hk0 : kOf T 0 = p.2 := hb ▸ hk
      have := h0 (by rw [hk0]; exact hp1)
      rw [hk0] at this
      omega
    · rw [List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
      have hmem : p.1 ∈ (T.map Prod.fst).toFinset :=
        List.mem_toFinset.2 (List.mem_map_of_mem hp)
      have h1 := hL p.1 hmem (by omega)
      rw [hk, ncard_Lset (by omega) hp1] at h1
      have h2 := sub_one_le_Lof (k := p.2) (show 1 ≤ p.1 by omega)
      exact ⟨⟨hp1, by omega⟩, h1⟩
  · intro hc
    refine ⟨hbs, h12, ?_, ?_⟩
    · intro β hβ hβ1
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hβ)
      have hk := kOf_of_mem hnd hp
      rw [hk, ncard_Lset hβ1 (hpos p hp)]
      have h := hc p hp
      unfold choices at h
      split_ifs at h with hb
      · omega
      · exact of_decide_eq_true (List.mem_filter.1 h).2
    · intro h0
      have hmem : 0 ∈ T.map Prod.fst := (kOf_pos_iff hpos 0).1 (by omega)
      obtain ⟨p, hp, hp0⟩ := List.mem_map.1 hmem
      have hk := kOf_of_mem hnd hp
      rw [hp0] at hk
      have h := hc p hp
      unfold choices at h
      split_ifs at h
      rw [List.mem_range'_1] at h
      rw [hk]
      omega

theorem pos_of_mem_enum {T : List (ℕ × ℕ)} (hT : T ∈ enum) : ∀ p ∈ T, 1 ≤ p.2 :=
  fun p hp => one_le_of_mem_choices (((mem_enum T).1 hT).2.2 p hp)

theorem nodup_of_mem_enum {T : List (ℕ × ℕ)} (hT : T ∈ enum) : (T.map Prod.fst).Nodup :=
  List.nodup_range.sublist ((mem_enum T).1 hT).1

theorem inRegion_of_mem_enum {T : List (ℕ × ℕ)} (hT : T ∈ enum) : InRegion (msOf T) := by
  obtain ⟨h1, h2, h3⟩ := (mem_enum T).1 hT
  exact (inRegion_msOf_iff h1 h2 (pos_of_mem_enum hT)).2 h3

theorem exists_mem_enum {m : Multiset ℕ} (hm : InRegion m) : ∃ T ∈ enum, msOf T = m := by
  set Bl : List ℕ := (List.range 13).filter (fun b => b ∈ m) with hBl
  set T : List (ℕ × ℕ) := Bl.map (fun b => (b, m.count b)) with hT
  have hfst : T.map Prod.fst = Bl := by
    rw [hT, List.map_map]
    exact List.map_id'' (fun _ => rfl) Bl
  have hsub : Bl.Sublist (List.range 13) := List.filter_sublist
  have hnd : (T.map Prod.fst).Nodup := hfst ▸ List.nodup_range.sublist hsub
  have hpos : ∀ p ∈ T, 1 ≤ p.2 := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    have := (List.mem_filter.1 hb).2
    exact Multiset.count_pos.2 (of_decide_eq_true this)
  have hle : ∀ x ∈ m, x < 13 := by
    intro x hx
    have h1 : x ≤ bstar m := Finset.le_sup (f := id) (Multiset.mem_toFinset.2 hx)
    have h2 := hm.2.1
    omega
  have hms : msOf T = m := by
    ext x
    rw [count_msOf]
    by_cases hx : x ∈ m
    · have hxT : (x, m.count x) ∈ T :=
        List.mem_map.2 ⟨x, List.mem_filter.2 ⟨List.mem_range.2 (hle x hx), decide_eq_true hx⟩, rfl⟩
      exact kOf_of_mem hnd hxT
    · rw [Multiset.count_eq_zero.2 hx]
      apply kOf_eq_zero
      rw [hfst, List.mem_filter]
      intro h
      exact hx (of_decide_eq_true h.2)
  refine ⟨T, ?_, hms⟩
  have hbs : 2 ≤ bsOf (T.map Prod.fst) := by
    rw [← bstar_msOf hpos, hms]
    exact hm.1
  rw [mem_enum]
  refine ⟨hfst ▸ hsub, hbs, ?_⟩
  exact (inRegion_msOf_iff (hfst ▸ hsub) hbs hpos).1 (hms ▸ hm)

theorem eq_map_kOf {T : List (ℕ × ℕ)} (hnd : (T.map Prod.fst).Nodup) :
    T = (T.map Prod.fst).map (fun b => (b, kOf T b)) := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id T]
  refine List.map_congr_left (fun p hp => ?_)
  simp [kOf_of_mem hnd hp]

theorem msOf_injOn : Set.InjOn msOf {T | T ∈ enum} := by
  intro T₁ h₁ T₂ h₂ h
  have hs₁ := ((mem_enum T₁).1 h₁).1
  have hs₂ := ((mem_enum T₂).1 h₂).1
  have hBl : T₁.map Prod.fst = T₂.map Prod.fst := by
    apply (List.pairwise_lt_range.sublist hs₁).eq_of_mem_iff (List.pairwise_lt_range.sublist hs₂)
    intro x
    rw [← mem_msOf (pos_of_mem_enum h₁), ← mem_msOf (pos_of_mem_enum h₂), h]
  have hk : ∀ b, kOf T₁ b = kOf T₂ b := by
    intro b
    rw [← count_msOf, ← count_msOf, h]
  rw [eq_map_kOf (nodup_of_mem_enum h₁), eq_map_kOf (nodup_of_mem_enum h₂), hBl]
  simp only [hk]

theorem regionR_eq : regionR = msOf '' {T | T ∈ enum} := by
  ext m
  constructor
  · intro hm
    obtain ⟨T, hT, rfl⟩ := exists_mem_enum hm
    exact ⟨T, hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact inRegion_of_mem_enum hT

end P8Region
