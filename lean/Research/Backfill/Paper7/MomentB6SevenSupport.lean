import Research.Backfill.Paper7.MomentB6LabelledSevenRoute

/-! Source-only candidate. The imported route has actual producer641. The support proof
uses the original six ordered coordinates, all21 catalog entries via the route,
and the original Q capacity. No support table or numerical total is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6SevenSingle (i : Fin 6) : Fin 6 → ℕ := fun k => if k = i then 7 else 0
#print axioms Paper7MomentCounts.b6SevenSingle

def b6SevenDouble (i j : Fin 6) : Fin 6 → ℕ :=
  fun k => if k = i then 6 else if k = j then 1 else 0
#print axioms Paper7MomentCounts.b6SevenDouble

theorem b6SevenSingle_sum (i : Fin 6) : (∑ k, b6SevenSingle i k) = 7 := by
  simp [b6SevenSingle]
#print axioms Paper7MomentCounts.b6SevenSingle_sum

theorem b6SevenSingle_sq_sum (i : Fin 6) :
    (∑ k, (b6SevenSingle i k : ℤ)^2) = 49 := by
  simp [b6SevenSingle]
#print axioms Paper7MomentCounts.b6SevenSingle_sq_sum

theorem b6SevenDouble_sum (i j : Fin 6) (hij : i ≠ j) :
    (∑ k, b6SevenDouble i j k) = 7 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp [b6SevenDouble, hij.symm]
  · intro k _hk hne
    simp [b6SevenDouble, hne.1, hne.2]
#print axioms Paper7MomentCounts.b6SevenDouble_sum

theorem b6SevenDouble_sq_sum (i j : Fin 6) (hij : i ≠ j) :
    (∑ k, (b6SevenDouble i j k : ℤ)^2) = 37 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp [b6SevenDouble, hij.symm]
  · intro k _hk hne
    simp [b6SevenDouble, hne.1, hne.2]
#print axioms Paper7MomentCounts.b6SevenDouble_sq_sum

theorem b6_nat_mass_exhausted (s : Finset (Fin 6)) (z : Fin 6 → ℕ)
    (i : Fin 6) (hi : i ∈ s) (hs : (∑ k ∈ s, z k) = z i)
    (j : Fin 6) (hj : j ∈ s) (hji : j ≠ i) : z j = 0 := by
  have he := Finset.sum_erase_add s z hi
  have hz : (∑ k ∈ s.erase i, z k) = 0 := by omega
  have hm : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji,hj⟩
  have hb := Finset.single_le_sum (s := s.erase i) (f := z)
    (fun _ _ => Nat.zero_le _) hm
  omega
#print axioms Paper7MomentCounts.b6_nat_mass_exhausted

theorem b6_total_seven_with_seven (z : Fin 6 → ℕ) (hZ : (∑ k, z k) = 7)
    (i : Fin 6) (hi : z i = 7) : z = b6SevenSingle i := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [b6SevenSingle, hi]
  · have hz := b6_nat_mass_exhausted Finset.univ z i (Finset.mem_univ i)
      (hZ.trans hi.symm) k (Finset.mem_univ k) hk
    simp [b6SevenSingle, hk, hz]
#print axioms Paper7MomentCounts.b6_total_seven_with_seven

theorem b6_total_seven_with_six (z : Fin 6 → ℕ) (hZ : (∑ k, z k) = 7)
    (i : Fin 6) (hi : z i = 6) : ∃ j, i ≠ j ∧ z = b6SevenDouble i j := by
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
    simp [b6SevenDouble,hi]
  · by_cases hkj : k = j
    · subst k
      simp [b6SevenDouble,hji,hjone]
    · have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
      have hz := b6_nat_mass_exhausted (Finset.univ.erase i) z j hj
        (hrest.trans hjone.symm) k hk hkj
      simp [b6SevenDouble,hki,hkj,hz]
#print axioms Paper7MomentCounts.b6_total_seven_with_six

theorem b6_seven_guard_has_large_coordinate (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ k, z k) = 7) (hQ : Q ≤ 7) (hg : b6SevenMomentGuard z Q) :
    ∃ i, 6 ≤ z i := by
  by_contra hn
  have hb : ∀ i, z i ≤ 5 := by
    intro i
    have hni : ¬ 6 ≤ z i := fun h => hn ⟨i,h⟩
    omega
  have hterm (i : Fin 6) : (z i : ℤ)^2 ≤ 5*(z i : ℤ) := by
    have h0 : (0 : ℤ) ≤ (z i : ℤ) := Int.natCast_nonneg _
    have h5 : (z i : ℤ) ≤ 5 := by exact_mod_cast hb i
    nlinarith only [h0,h5]
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
  have hZi : (∑ i, (z i : ℤ)) = 7 := by exact_mod_cast hZ
  rw [← Finset.mul_sum, hZi] at hs
  have hQi : (Q : ℤ) ≤ 7 := by exact_mod_cast hQ
  rcases hg with hg | ⟨_hfour,hg⟩ <;> nlinarith only [hs,hQi,hg]
#print axioms Paper7MomentCounts.b6_seven_guard_has_large_coordinate

def B6SevenShapes (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  (∃ i, z = b6SevenSingle i ∧ (Q = 1 ∨ Q = 7)) ∨
    ∃ i j, i ≠ j ∧ z = b6SevenDouble i j ∧ Q = 7
#print axioms Paper7MomentCounts.B6SevenShapes

theorem b6_seven_guard_complete_shapes (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ k, z k) = 7) (hQ : Q ≤ 7) (hg : b6SevenMomentGuard z Q) :
    B6SevenShapes z Q := by
  obtain ⟨i,hi⟩ := b6_seven_guard_has_large_coordinate z Q hZ hQ hg
  have hi7 := b6_total_seven_coordinate_bound z hZ i
  have hicases : z i = 7 ∨ z i = 6 := by omega
  rcases hicases with hi | hi
  · have hz := b6_total_seven_with_seven z hZ i hi
    refine Or.inl ⟨i,hz,?_⟩
    rw [hz] at hg
    unfold b6SevenMomentGuard at hg
    rw [b6SevenSingle_sq_sum] at hg
    rcases hg with he | ⟨_hfour,he⟩
    · left
      omega
    · right
      omega
  · obtain ⟨j,hij,hz⟩ := b6_total_seven_with_six z hZ i hi
    refine Or.inr ⟨i,j,hij,hz,?_⟩
    rw [hz] at hg
    unfold b6SevenMomentGuard at hg
    rw [b6SevenDouble_sq_sum i j hij] at hg
    have hQi : (Q : ℤ) ≤ 7 := by exact_mod_cast hQ
    rcases hg with he | ⟨_hfour,he⟩ <;> omega
#print axioms Paper7MomentCounts.b6_seven_guard_complete_shapes

theorem b6_seven_shapes_accept (z : Fin 6 → ℕ) (Q : ℕ) (hs : B6SevenShapes z Q) :
    (∑ k, z k) = 7 ∧ Q ≤ 7 ∧ b6ZQAccept z Q := by
  rcases hs with ⟨i,rfl,hQ⟩ | ⟨i,j,hij,rfl,rfl⟩
  · rcases hQ with rfl | rfl
    · refine ⟨b6SevenSingle_sum i,by decide,?_⟩
      apply (b6_zq_accept_total_seven_iff _ _ (b6SevenSingle_sum i) (by decide)).mpr
      simp [b6SevenMomentGuard,b6SevenSingle_sq_sum]
    · refine ⟨b6SevenSingle_sum i,by decide,?_⟩
      apply (b6_zq_accept_total_seven_iff _ _ (b6SevenSingle_sum i) (by decide)).mpr
      simp [b6SevenMomentGuard,b6SevenSingle_sq_sum]
  · refine ⟨b6SevenDouble_sum i j hij,by decide,?_⟩
    apply (b6_zq_accept_total_seven_iff _ _ (b6SevenDouble_sum i j hij) (by decide)).mpr
    simp [b6SevenMomentGuard,b6SevenDouble_sq_sum i j hij]
#print axioms Paper7MomentCounts.b6_seven_shapes_accept

end Paper7MomentCounts
