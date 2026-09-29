import Research.Backfill.Paper3.Proof.TS.Switch

/-!
# The 2-switch theorem

Two simple graphs on the same finite vertex set with the same degree at every vertex are joined by
a sequence of 2-switches (Hakimi; Fulkerson–Hoffman–McAndrew). Proof (after Berge): fix the
neighbourhoods of the vertices one at a time. With the vertices of `S` already fixed (`G` and `H`
agree on every pair meeting `S`) and `w ∉ S`, a 2-switch in `G` or in `H` that avoids `S` reduces
the number of vertices on which the neighbourhoods of `w` differ (`exchange`, `reduce`).
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

variable {V : Type*} [Fintype V]

/-- Reachability by 2-switches. -/
abbrev Reach (G H : SimpleGraph V) : Prop := Relation.ReflTransGen TwoSwitchStep G H

/-- `G` and `H` have the same number of neighbours at every vertex. -/
def SameDeg (G H : SimpleGraph V) : Prop := ∀ v, (nbr G v).card = (nbr H v).card

/-- `G` and `H` agree on every pair meeting `S`. -/
def AgreeOn (S : Finset V) (G H : SimpleGraph V) : Prop := ∀ s ∈ S, ∀ t, G.Adj s t ↔ H.Adj s t

open Classical in
/-- The vertices `t` on which the neighbourhoods of `w` in `G` and `H` differ. -/
noncomputable def dis (G H : SimpleGraph V) (w : V) : Finset V :=
  univ.filter fun t => ¬ (G.Adj w t ↔ H.Adj w t)

theorem mem_dis {G H : SimpleGraph V} {w t : V} : t ∈ dis G H w ↔ ¬ (G.Adj w t ↔ H.Adj w t) := by
  simp [dis]

theorem SameDeg.symm {G H : SimpleGraph V} (h : SameDeg G H) : SameDeg H G := fun v => (h v).symm

omit [Fintype V] in
theorem AgreeOn.symm {S : Finset V} {G H : SimpleGraph V} (h : AgreeOn S G H) : AgreeOn S H G :=
  fun s hs t => (h s hs t).symm

theorem dis_comm (G H : SimpleGraph V) (w : V) : dis G H w = dis H G w := by
  ext t
  rw [mem_dis, mem_dis]
  exact not_congr Iff.comm

variable [DecidableEq V]

/-- The number of neighbours of `v` outside `S`. -/
noncomputable def rdeg (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  ((nbr G v).filter (· ∉ S)).card

/-- Graphs with the same degrees that agree on the pairs meeting `S` have the same number of
neighbours outside `S` at every vertex. -/
theorem rdeg_eq {G H : SimpleGraph V} {S : Finset V} (hD : SameDeg G H) (hA : AgreeOn S G H)
    (v : V) : rdeg G S v = rdeg H S v := by
  have e1 := card_filter_add_card_filter_not (s := nbr G v) (· ∈ S)
  have e2 := card_filter_add_card_filter_not (s := nbr H v) (· ∈ S)
  have e3 : (nbr G v).filter (· ∈ S) = (nbr H v).filter (· ∈ S) := by
    ext t
    simp only [mem_filter, mem_nbr]
    constructor
    · rintro ⟨h, ht⟩
      exact ⟨((hA t ht v).1 h.symm).symm, ht⟩
    · rintro ⟨h, ht⟩
      exact ⟨((hA t ht v).2 h.symm).symm, ht⟩
  rw [e3] at e1
  have := hD v
  unfold rdeg
  omega

/-- The exchange lemma: if `w ~ y`, `w ≁ x` and `x` has at least as many neighbours outside `S`
as `y`, then some `z ∉ S` is a neighbour of `x` and not of `y`, `z ≠ y`. -/
theorem exchange (K : SimpleGraph V) (S : Finset V) {w x y : V} (hwS : w ∉ S) (hxS : x ∉ S)
    (hwx : w ≠ x) (hwy : K.Adj w y) (hnwx : ¬ K.Adj w x) (hle : rdeg K S y ≤ rdeg K S x) :
    ∃ z, z ∉ S ∧ K.Adj x z ∧ ¬ K.Adj y z ∧ z ≠ y := by
  by_contra hcon
  push Not at hcon
  have hle' : ((nbr K y).filter (· ∉ S)).card ≤ ((nbr K x).filter (· ∉ S)).card := hle
  have hwB : w ∈ (nbr K y).filter (· ∉ S) := mem_filter.2 ⟨mem_nbr.2 hwy.symm, hwS⟩
  by_cases hxy : K.Adj x y
  · have hxB : x ∈ ((nbr K y).filter (· ∉ S)).erase w :=
      mem_erase.2 ⟨hwx.symm, mem_filter.2 ⟨mem_nbr.2 hxy.symm, hxS⟩⟩
    have hsub : (nbr K x).filter (· ∉ S) ⊆
        insert y ((((nbr K y).filter (· ∉ S)).erase w).erase x) := by
      intro z hz
      rw [mem_filter, mem_nbr] at hz
      rw [mem_insert, mem_erase, mem_erase]
      by_cases hzy : z = y
      · exact Or.inl hzy
      · refine Or.inr ⟨hz.1.ne', ?_, ?_⟩
        · rintro rfl
          exact hnwx hz.1.symm
        · refine mem_filter.2 ⟨mem_nbr.2 ?_, hz.2⟩
          by_contra hyz
          exact hzy (hcon z hz.2 hz.1 hyz)
    have h1 := card_le_card hsub
    have h2 := card_insert_le y ((((nbr K y).filter (· ∉ S)).erase w).erase x)
    have h3 := card_erase_of_mem hxB
    have h4 := card_erase_of_mem hwB
    have h5 : 0 < (((nbr K y).filter (· ∉ S)).erase w).card := card_pos.2 ⟨x, hxB⟩
    omega
  · have hsub : (nbr K x).filter (· ∉ S) ⊆ ((nbr K y).filter (· ∉ S)).erase w := by
      intro z hz
      rw [mem_filter, mem_nbr] at hz
      rw [mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact hnwx hz.1.symm
      · refine mem_filter.2 ⟨mem_nbr.2 ?_, hz.2⟩
        by_contra hyz
        have := hcon z hz.2 hz.1 hyz
        subst this
        exact hxy hz.1
    have h1 := card_le_card hsub
    have h4 := card_erase_of_mem hwB
    have h5 : 0 < ((nbr K y).filter (· ∉ S)).card := card_pos.2 ⟨w, hwB⟩
    omega

/-- One reduction step: a 2-switch in `G` avoiding `S` that makes the neighbourhood of `w` closer
to that in `H`. -/
theorem reduce {S : Finset V} {w x y : V} {G H : SimpleGraph V} (hw : w ∉ S) (hD : SameDeg G H)
    (hA : AgreeOn S G H) (hGy : G.Adj w y) (hHy : ¬ H.Adj w y) (hGx : ¬ G.Adj w x)
    (hHx : H.Adj w x) (hle : rdeg G S y ≤ rdeg G S x) :
    ∃ G', TwoSwitchStep G G' ∧ SameDeg G' H ∧ AgreeOn S G' H ∧
      (dis G' H w).card < (dis G H w).card := by
  have hxS : x ∉ S := fun hx => hGx ((hA x hx w).2 hHx.symm).symm
  have hyS : y ∉ S := fun hy => hHy ((hA y hy w).1 hGy.symm).symm
  have hwx : w ≠ x := hHx.ne
  have hyx : y ≠ x := by
    rintro rfl
    exact hGx hGy
  obtain ⟨z, hzS, hxz, hyz, hzy⟩ := exchange G S hw hxS hwx hGy hGx hle
  have hs : IsSwitch G w y z x := ⟨hGy, hxz.symm, hwx, hzy, hGx, fun h => hyz h.symm⟩
  refine ⟨twoSwitch G w y z x, hs.step, fun v => (hs.card_nbr v).trans (hD v), ?_, ?_⟩
  · intro s hsS t
    have hsw : s ≠ w := fun h => hw (h ▸ hsS)
    have hsy : s ≠ y := fun h => hyS (h ▸ hsS)
    have hsz : s ≠ z := fun h => hzS (h ▸ hsS)
    have hsx : s ≠ x := fun h => hxS (h ▸ hsS)
    rw [twoSwitch_adj_of_ne hsw hsy hsz hsx]
    exact hA s hsS t
  · apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, ?_, ?_⟩
      · rw [mem_dis]
        exact fun h => hGx (h.2 hHx)
      · rw [mem_dis, hs.adj_u₁, not_not]
        exact ⟨fun _ => hHx, fun _ => Or.inr rfl⟩
    · intro t ht
      rw [mem_dis, hs.adj_u₁] at ht
      rw [mem_dis]
      by_cases htx : t = x
      · subst htx
        exact absurd ⟨fun _ => hHx, fun _ => Or.inr rfl⟩ ht
      by_cases hty : t = y
      · subst hty
        refine absurd ⟨fun h => ?_, fun h => absurd h hHy⟩ ht
        rcases h with ⟨-, h⟩ | h
        · exact absurd rfl h
        · exact absurd h hyx
      have : ((G.Adj w t ∧ t ≠ y) ∨ t = x) ↔ G.Adj w t := by tauto
      rwa [this] at ht

/-- Fixing the neighbourhood of one more vertex `w`. -/
theorem fix_vertex {S : Finset V} {w : V} (hw : w ∉ S) :
    ∀ (n : ℕ) (G H : SimpleGraph V), (dis G H w).card ≤ n → SameDeg G H → AgreeOn S G H →
      ∃ G' H', Reach G G' ∧ Reach H H' ∧ SameDeg G' H' ∧ AgreeOn (insert w S) G' H' := by
  have base : ∀ G H : SimpleGraph V, dis G H w = ∅ → AgreeOn S G H →
      AgreeOn (insert w S) G H := by
    intro G H h0 hA s hs t
    rcases mem_insert.1 hs with rfl | hs
    · by_contra h
      have : t ∈ dis G H s := mem_dis.2 h
      rw [h0] at this
      exact absurd this (notMem_empty t)
    · exact hA s hs t
  intro n
  induction n with
  | zero =>
    intro G H hn hD hA
    exact ⟨G, H, .refl, .refl, hD, base G H (card_eq_zero.1 (Nat.le_zero.1 hn)) hA⟩
  | succ n ih =>
    intro G H hn hD hA
    by_cases h0 : dis G H w = ∅
    · exact ⟨G, H, .refl, .refl, hD, base G H h0 hA⟩
    have hne : nbr G w ≠ nbr H w := by
      intro h
      obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 h0
      rw [mem_dis] at ht
      apply ht
      rw [← mem_nbr, ← mem_nbr, h]
    obtain ⟨x, hGx, hHx⟩ : ∃ x, ¬ G.Adj w x ∧ H.Adj w x := by
      by_contra hc
      push Not at hc
      apply hne
      refine (eq_of_subset_of_card_le ?_ (hD w).le).symm
      intro t ht
      rw [mem_nbr] at ht ⊢
      by_contra h
      exact hc t h ht
    obtain ⟨y, hGy, hHy⟩ : ∃ y, G.Adj w y ∧ ¬ H.Adj w y := by
      by_contra hc
      push Not at hc
      apply hne
      refine eq_of_subset_of_card_le ?_ (hD w).ge
      intro t ht
      rw [mem_nbr] at ht ⊢
      exact hc t ht
    rcases le_total (rdeg G S y) (rdeg G S x) with hle | hle
    · obtain ⟨G', hst, hD', hA', hlt⟩ := reduce hw hD hA hGy hHy hGx hHx hle
      obtain ⟨G'', H'', r1, r2, hD'', hA''⟩ := ih G' H (by omega) hD' hA'
      exact ⟨G'', H'', .head hst r1, r2, hD'', hA''⟩
    · rw [rdeg_eq hD hA, rdeg_eq hD hA] at hle
      obtain ⟨H', hst, hD', hA', hlt⟩ := reduce hw hD.symm hA.symm hHx hGx hHy hGy hle
      rw [dis_comm H' G, dis_comm H G] at hlt
      obtain ⟨G'', H'', r1, r2, hD'', hA''⟩ := ih G H' (by omega) hD'.symm hA'.symm
      exact ⟨G'', H'', r1, .head hst r2, hD'', hA''⟩

/-- Graphs with the same degrees that agree on the pairs meeting `S` are joined by 2-switches;
induction on the number of vertices outside `S`. -/
theorem reach_of_agree : ∀ (n : ℕ) (S : Finset V), (univ \ S).card = n →
    ∀ G H : SimpleGraph V, SameDeg G H → AgreeOn S G H → Reach G H := by
  intro n
  induction n with
  | zero =>
    intro S hS G H _ hA
    have hSu : ∀ v, v ∈ S := by
      intro v
      by_contra hv
      have : v ∈ univ \ S := mem_sdiff.2 ⟨mem_univ v, hv⟩
      rw [card_eq_zero.1 hS] at this
      exact absurd this (notMem_empty v)
    have : G = H := by
      ext a b
      exact hA a (hSu a) b
    subst this
    exact .refl
  | succ n ih =>
    intro S hS G H hD hA
    obtain ⟨w, hw⟩ : (univ \ S).Nonempty := card_pos.1 (by omega)
    have hwS : w ∉ S := (mem_sdiff.1 hw).2
    obtain ⟨G', H', r1, r2, hD', hA'⟩ := fix_vertex hwS _ G H le_rfl hD hA
    have hcard : (univ \ insert w S).card = n := by
      rw [sdiff_insert, card_erase_of_mem hw, hS]
      rfl
    exact r1.trans ((ih _ hcard G' H' hD' hA').trans (reach_symm r2))

/-- **The 2-switch theorem** (`TwoSwitchConnected`). -/
theorem twoSwitchConnected : TwoSwitchConnected := by
  intro V _ _ G H _ _ hdeg
  refine reach_of_agree _ ∅ rfl G H ?_ (fun s hs => absurd hs (notMem_empty s))
  intro v
  rw [card_nbr_eq_degree, card_nbr_eq_degree, hdeg v]

end P3TS
