import Research.Backfill.Paper8.Proof.Region.Bridge
import Research.Backfill.Paper8.Proof.Orb.Counts
import Research.Backfill.Paper8.Proof.Orb.Main
import Research.Backfill.Paper8.Proof.Spec.Secular

/-!
# Region search: soundness of the test `critT` (agent `region`)

For a tree `T` of `enum`: `N_I ≤ NIc T` (by `N_I = #{q ≥ 1 : R(q²) = 0}` of agent `orb` and the
bound `R(t) > 0` for `t > b* + k` of agent `spec`), `N_I + 2 N_II + N_ei ≤ r` (Lemma 3.3(d) for
a multiset, agent `orb`), and `2 N_II < r` when `|R(0)|` is not a square (agent `orb`). Hence
`critT T = true` gives (a′) or (b′) for the multiset of `T`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial

namespace P8Region

theorem msOf_ne_zero {T : List (ℕ × ℕ)} (hT : T ∈ enum) : msOf T ≠ 0 := by
  have hbs := ((mem_enum T).1 hT).2.1
  cases T with
  | nil => simp [bsOf] at hbs
  | cons p T =>
    have hp : p.1 ∈ msOf (p :: T) :=
      (mem_msOf (pos_of_mem_enum hT) p.1).2 (List.mem_map_of_mem List.mem_cons_self)
    intro h
    rw [h] at hp
    simp at hp

/-- `N_I ≤ NIc T` for the trees of the region. -/
theorem NI_le_NIc {T : List (ℕ × ℕ)} (hT : T ∈ enum)
    (h48 : bsOf (T.map Prod.fst) + sumK T ≤ 48) :
    NI (msOf T) ≤ NIc T (bsOf (T.map Prod.fst) + sumK T) := by
  have hpos := pos_of_mem_enum hT
  have hnd := nodup_of_mem_enum hT
  have hne := msOf_ne_zero hT
  obtain ⟨-, hNI⟩ := P8Orb.NI_eq P8Orb.secularMonic (msOf T) hne
  rw [hNI]
  set lim := bsOf (T.map Prod.fst) + sumK T with hlim
  set S : List ℕ := (List.range' 1 6).filter
    (fun q => q * q ≤ lim ∧ evalR T ((q * q : ℕ) : ℤ) = 0) with hS
  have hsub : {q : ℕ | 1 ≤ q ∧ (secular (msOf T)).eval ((q : ℤ) ^ 2) = 0} ⊆
      (S.toFinset : Set ℕ) := by
    rintro q ⟨hq1, hq⟩
    have hU : ((q : ℝ) ^ 2) ≤ (bstar (msOf T) : ℝ) + (Multiset.card (msOf T) : ℝ) := by
      refine not_lt.1 (fun h => ?_)
      have hpos' := P8Spec.aeval_secular_pos (msOf T) ((q : ℝ) ^ 2) h
      have h0 : aeval ((q : ℝ) ^ 2) (secular (msOf T)) = 0 := by
        rw [← P8Spec.eval_map_secular]
        have := Polynomial.eval_intCast_map (Int.castRingHom ℝ) (secular (msOf T)) ((q : ℤ) ^ 2)
        push_cast at this
        rw [this, hq]
        simp
      rw [h0] at hpos'
      exact lt_irrefl _ hpos'
    rw [bstar_msOf hpos, card_msOf] at hU
    have hU' : q * q ≤ lim := by
      rw [hlim]
      have : ((q * q : ℕ) : ℝ) ≤ ((bsOf (T.map Prod.fst) + sumK T : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    have hq6 : q < 7 := by
      by_contra h7
      have : 7 * 7 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hev : evalR T ((q * q : ℕ) : ℤ) = 0 := by
      rw [← eval_secular_msOf hpos hnd]
      have : ((q * q : ℕ) : ℤ) = (q : ℤ) ^ 2 := by push_cast; ring
      rw [this, hq]
    rw [Finset.mem_coe, List.mem_toFinset, hS, List.mem_filter, List.mem_range'_1]
    exact ⟨⟨hq1, by omega⟩, decide_eq_true ⟨hU', hev⟩⟩
  calc {q : ℕ | 1 ≤ q ∧ (secular (msOf T)).eval ((q : ℤ) ^ 2) = 0}.ncard
      ≤ (S.toFinset : Set ℕ).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = S.toFinset.card := Set.ncard_coe_finset _
    _ = S.length := List.toFinset_card_of_nodup ((List.nodup_range' ..).filter _)
    _ = NIc T lim := rfl

theorem not_isSquare_of_notSq {z : ℤ} (h : notSq z = true) : ¬ IsSquare |z| := by
  rintro ⟨r, hr⟩
  have hn : z.natAbs = r.natAbs * r.natAbs := by
    have := congrArg Int.natAbs hr
    rwa [Int.natAbs_abs, Int.natAbs_mul] at this
  have hle : r.natAbs ≤ z.natAbs := by
    rw [hn]
    exact Nat.le_mul_self _
  have hany : (List.range (z.natAbs + 1)).any (fun q => q * q = z.natAbs) = true :=
    List.any_eq_true.2 ⟨r.natAbs, List.mem_range.2 (by omega), decide_eq_true hn.symm⟩
  rw [notSq, hany] at h
  exact absurd h (by decide)

/-- Soundness of `critT`: (a′) or (b′) for the multiset of a tree of the region. -/
theorem crit_of_critT {T : List (ℕ × ℕ)} (hT : T ∈ enum)
    (h48 : bsOf (T.map Prod.fst) + sumK T ≤ 48) (hc : critT T = true) :
    CritA (msOf T) ∨ CritB (msOf T) := by
  have hpos := pos_of_mem_enum hT
  have hnd := nodup_of_mem_enum hT
  have hne := msOf_ne_zero hT
  have hNI := NI_le_NIc hT h48
  obtain ⟨-, -, hd⟩ := P8Orb.orbit_count P8Orb.secularMonic (msOf T) hne
  rw [card_Bset_msOf hpos hnd] at hd
  have hmemB : ∀ p ∈ T, p.1 ∈ Bset (msOf T) := fun p hp => by
    rw [Bset_msOf hpos]
    exact List.mem_toFinset.2 (List.mem_map_of_mem hp)
  simp only [critT, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hc
  rcases hc with (⟨p, hp, hp1, hL⟩ | ⟨hk0, hB⟩) | ⟨⟨hni0, hsq⟩, p, hp, hp1, hL⟩
  · left
    refine ⟨p.1, hmemB p hp, hp1, ?_⟩
    unfold CritAat
    rw [kb_msOf, kOf_of_mem hnd hp, ncard_Lset hp1 (hpos p hp)]
    omega
  · right
    refine ⟨by rw [kb_msOf]; exact hk0, ?_⟩
    rw [kb_msOf]
    omega
  · left
    have hII := P8Orb.two_NII_lt_of_not_isSquare P8Orb.secularMonic (msOf T) hne
      (by rw [eval_secular_msOf hpos hnd]; exact not_isSquare_of_notSq hsq)
    rw [card_Bset_msOf hpos hnd] at hII
    refine ⟨p.1, hmemB p hp, hp1, ?_⟩
    unfold CritAat
    rw [kb_msOf, kOf_of_mem hnd hp, ncard_Lset hp1 (hpos p hp)]
    omega

end P8Region
