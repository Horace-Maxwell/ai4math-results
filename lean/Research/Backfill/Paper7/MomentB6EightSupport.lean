import Research.Backfill.Paper7.MomentB6SevenSupport

/-! Source-only candidate. MomentB6SevenSupport is explicitly pending here.
Its mass-exhaustion lemma is reused rather than replaced by an assumed shape.
The full original Z=8 slice retains six ordered coordinates, all21 catalog
entries, Q=0/1 and the original bounded-q weights and total budget. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6TwoPointUnit (M : ℕ) (i j : Fin 6) : Fin 6 → ℕ :=
  fun k => if k = i then M else if k = j then 1 else 0
#print axioms Paper7MomentCounts.b6TwoPointUnit

theorem b6TwoPointUnit_sum (M : ℕ) (i j : Fin 6) (hij : i ≠ j) :
    (∑ k, b6TwoPointUnit M i j k) = M + 1 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp [b6TwoPointUnit,hij.symm]
  · intro k _hk hne
    simp [b6TwoPointUnit,hne.1,hne.2]
#print axioms Paper7MomentCounts.b6TwoPointUnit_sum

theorem b6TwoPointUnit_sq_sum (M : ℕ) (i j : Fin 6) (hij : i ≠ j) :
    (∑ k, (b6TwoPointUnit M i j k : ℤ)^2) = (M : ℤ)^2 + 1 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp [b6TwoPointUnit,hij.symm]
  · intro k _hk hne
    simp [b6TwoPointUnit,hne.1,hne.2]
#print axioms Paper7MomentCounts.b6TwoPointUnit_sq_sum

theorem b6_mass_one_above_vertex (z : Fin 6 → ℕ) (M : ℕ)
    (hZ : (∑ k, z k) = M + 1) (i : Fin 6) (hi : z i = M) :
    ∃ j, i ≠ j ∧ z = b6TwoPointUnit M i j := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hrest : (∑ k ∈ Finset.univ.erase i, z k) = 1 := by omega
  have hex : ∃ j, j ∈ Finset.univ.erase i ∧ z j = 1 := by
    by_contra hn
    have hz : ∀ j ∈ Finset.univ.erase i, z j = 0 := by
      intro j hj
      have hb := Finset.single_le_sum (s := Finset.univ.erase i) (f := z)
        (fun _ _ => Nat.zero_le _) hj
      have hne : z j ≠ 1 := fun h => hn ⟨j,hj,h⟩
      omega
    have hs : (∑ k ∈ Finset.univ.erase i, z k) = 0 := Finset.sum_eq_zero hz
    omega
  obtain ⟨j,hj,hjone⟩ := hex
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  refine ⟨j,hji.symm,?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [b6TwoPointUnit,hi]
  · by_cases hkj : k = j
    · subst k
      simp [b6TwoPointUnit,hji,hjone]
    · have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
      have hz := b6_nat_mass_exhausted (Finset.univ.erase i) z j hj
        (hrest.trans hjone.symm) k hk hkj
      simp [b6TwoPointUnit,hki,hkj,hz]
#print axioms Paper7MomentCounts.b6_mass_one_above_vertex

theorem b6_sq_sum_of_mass_at_one (z : Fin 6 → ℕ) (i : Fin 6)
    (hZ : (∑ k, z k) = z i) : (∑ k, (z k : ℤ)^2) = (z i : ℤ)^2 := by
  apply Finset.sum_eq_single i
  · intro k _hk hki
    have hz := b6_nat_mass_exhausted Finset.univ z i (Finset.mem_univ i)
      hZ k (Finset.mem_univ k) hki
    simp [hz]
  · intro hn
    exact False.elim (hn (Finset.mem_univ i))
#print axioms Paper7MomentCounts.b6_sq_sum_of_mass_at_one

theorem b6FeatureCatalog_m4_le_116 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hM : sm.2 ≤ 116) : sm = (9,72) ∨ sm = (13,84) ∨ sm = (17,96) := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_m4_le_116

def b6EightMomentGuard (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  (Q ≤ 1 ∧ (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 48) ∨
    (3 ≤ Q ∧ (∑ i, (z i : ℤ)^2) + 2*(Q : ℤ) = 60)
#print axioms Paper7MomentCounts.b6EightMomentGuard

theorem b6_zq_accept_total_eight_iff (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 8) (hQ : Q ≤ 8) :
    b6ZQAccept z Q ↔ b6EightMomentGuard z Q := by
  have hZi : ((∑ i, z i : ℕ) : ℤ) = 8 := by exact_mod_cast hZ
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg Q
  have hmax : max (Q : ℤ) 2 ≤ (Q : ℤ) + 2 := max_le (by omega) (by omega)
  have hleft : (Q : ℤ) ≤ max (Q : ℤ) 2 := le_max_left _ _
  have hu := b6_zq_theta_upper z Q (by omega)
  rw [hZi] at hu
  constructor
  · intro hg
    obtain ⟨sm,hsm,hM,hS,hload⟩ := hg.2.2
    have h116 : sm.2 ≤ 116 := by nlinarith only [hu,hM,hZi]
    have hc := b6FeatureCatalog_m4_le_116 sm hsm h116
    rw [hZ] at hS hload
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hS hload
    rcases hc with rfl | rfl | rfl
    · norm_num only [Prod.fst] at hload
      omega
    · refine Or.inl ⟨?_,?_⟩
      · by_contra hn
        have htwo : (2 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast (show 2 ≤ Q by omega)
        rw [max_eq_left htwo] at hload
        norm_num only [Prod.fst] at hload
        omega
      · norm_num only [Prod.snd] at hM
        nlinarith only [hM,hZi]
    · refine Or.inr ⟨?_,?_⟩
      · norm_num only [Prod.fst] at hS
        exact_mod_cast (show (3 : ℤ) ≤ (Q : ℤ) by omega)
      · norm_num only [Prod.snd] at hM
        nlinarith only [hM,hZi]
  · intro hg
    refine ⟨by omega,by omega,?_⟩
    rcases hg with ⟨hone,he⟩ | ⟨hthree,he⟩
    · have htwo : (Q : ℤ) ≤ 2 := by exact_mod_cast (show Q ≤ 2 by omega)
      refine ⟨(13,84),by norm_num [b6FeatureCatalog],?_,?_,?_⟩
      · norm_num only [Prod.snd]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
      · rw [hZ,max_eq_right htwo]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
    · have hthreeI : (3 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hthree
      refine ⟨(17,96),by norm_num [b6FeatureCatalog],?_,?_,?_⟩
      · norm_num only [Prod.snd]
        nlinarith only [he,hZi]
      · rw [hZ]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
      · rw [hZ]
        norm_num only [Prod.fst,Nat.cast_add,Nat.cast_ofNat]
        omega
#print axioms Paper7MomentCounts.b6_zq_accept_total_eight_iff

theorem b6_total_eight_cap_six_sq_bound (z : Fin 6 → ℕ)
    (hZ : (∑ i, z i) = 8) (hcap : ∀ i, z i ≤ 6) :
    (∑ i, (z i : ℤ)^2) ≤ 40 := by
  by_cases hsix : ∃ i, z i = 6
  · obtain ⟨i,hi⟩ := hsix
    have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
    have hrest : (∑ k ∈ Finset.univ.erase i, z k) = 2 := by omega
    have hrestI : (∑ k ∈ Finset.univ.erase i, (z k : ℤ)) = 2 := by exact_mod_cast hrest
    have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ.erase i)
      (f := fun k => (z k : ℤ)) (fun k _hk => Int.natCast_nonneg (z k))
    rw [hrestI] at hs
    have he2 := Finset.sum_erase_add Finset.univ (fun k => (z k : ℤ)^2) (Finset.mem_univ i)
    have hiI : (z i : ℤ) = 6 := by exact_mod_cast hi
    nlinarith only [hs,he2,hiI]
  · have hfive : ∀ i, z i ≤ 5 := by
      intro i
      have hn : z i ≠ 6 := fun h => hsix ⟨i,h⟩
      have hc := hcap i
      omega
    have hterm (i : Fin 6) : (z i : ℤ)^2 ≤ 5*(z i : ℤ) := by
      have h0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
      have h5 : (z i : ℤ) ≤ 5 := by exact_mod_cast hfive i
      nlinarith only [h0,h5]
    have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
    have hZi : (∑ i, (z i : ℤ)) = 8 := by exact_mod_cast hZ
    rw [← Finset.mul_sum,hZi] at hs
    norm_num at hs
    exact hs
#print axioms Paper7MomentCounts.b6_total_eight_cap_six_sq_bound

theorem b6_eight_guard_has_large_coordinate (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 8) (hQ : Q ≤ 8) (hg : b6EightMomentGuard z Q) :
    ∃ i, 7 ≤ z i := by
  by_contra hn
  have hc : ∀ i, z i ≤ 6 := by
    intro i
    have hni : ¬ 7 ≤ z i := fun h => hn ⟨i,h⟩
    omega
  have hs := b6_total_eight_cap_six_sq_bound z hZ hc
  have hQi : (Q : ℤ) ≤ 8 := by exact_mod_cast hQ
  rcases hg with ⟨hone,he⟩ | ⟨_hthree,he⟩
  · have honeI : (Q : ℤ) ≤ 1 := by exact_mod_cast hone
    nlinarith only [hs,honeI,he]
  · nlinarith only [hs,hQi,he]
#print axioms Paper7MomentCounts.b6_eight_guard_has_large_coordinate

theorem b6_eight_guard_complete_shape (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ i, z i) = 8) (hQ : Q ≤ 8) (hg : b6EightMomentGuard z Q) :
    ∃ i j, i ≠ j ∧ z = b6TwoPointUnit 7 i j ∧ Q = 5 := by
  obtain ⟨i,hi⟩ := b6_eight_guard_has_large_coordinate z Q hZ hQ hg
  have hib : z i ≤ 8 := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 6)))
      (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have he : z i = 7 ∨ z i = 8 := by omega
  rcases he with hi | hi
  · obtain ⟨j,hij,hz⟩ := b6_mass_one_above_vertex z 7 hZ i hi
    refine ⟨i,j,hij,hz,?_⟩
    rw [hz] at hg
    unfold b6EightMomentGuard at hg
    rw [b6TwoPointUnit_sq_sum 7 i j hij] at hg
    rcases hg with ⟨_hone,he⟩ | ⟨_hthree,he⟩ <;> omega
  · have hs := b6_sq_sum_of_mass_at_one z i (hZ.trans hi.symm)
    have hiI : (z i : ℤ) = 8 := by exact_mod_cast hi
    have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
    rcases hg with ⟨_hone,he⟩ | ⟨_hthree,he⟩ <;>
      nlinarith only [hs,hiI,hQ0,he]
#print axioms Paper7MomentCounts.b6_eight_guard_complete_shape

theorem b6_eight_shape_accept (i j : Fin 6) (hij : i ≠ j) :
    b6ZQAccept (b6TwoPointUnit 7 i j) 5 := by
  apply (b6_zq_accept_total_eight_iff _ _ (b6TwoPointUnit_sum 7 i j hij) (by decide)).mpr
  simp [b6EightMomentGuard,b6TwoPointUnit_sq_sum 7 i j hij]
#print axioms Paper7MomentCounts.b6_eight_shape_accept

end Paper7MomentCounts
