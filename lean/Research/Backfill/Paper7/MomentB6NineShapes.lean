import Research.Backfill.Paper7.MomentB6NineRoute

/-! Source-only complete shape reduction of the original Z=9 layer.
The imported route is pending until Root provides actual closed producers. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6TwoPoint (M N : ℕ) (i j : Fin 6) : Fin 6 → ℕ :=
  fun k => if k = i then M else if k = j then N else 0
#print axioms Paper7MomentCounts.b6TwoPoint

def b6ThreePoint (M N L : ℕ) (i j k : Fin 6) : Fin 6 → ℕ :=
  fun a => if a = i then M else if a = j then N else if a = k then L else 0
#print axioms Paper7MomentCounts.b6ThreePoint

def b6SpikeOnes (M : ℕ) (i : Fin 6) (s : Finset (Fin 6)) : Fin 6 → ℕ :=
  fun k => if k = i then M else if k ∈ s then 1 else 0
#print axioms Paper7MomentCounts.b6SpikeOnes

theorem b6TwoPoint_sums (M N : ℕ) (i j : Fin 6) (hij : i ≠ j) :
    (∑ k, b6TwoPoint M N i j k) = M + N ∧
      (∑ k, (b6TwoPoint M N i j k : ℤ)^2) = (M : ℤ)^2 + (N : ℤ)^2 := by
  constructor
  · rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
    · simp [b6TwoPoint,hij.symm]
    · intro k _hk hne
      simp [b6TwoPoint,hne.1,hne.2]
  · rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
    · simp [b6TwoPoint,hij.symm]
    · intro k _hk hne
      simp [b6TwoPoint,hne.1,hne.2]
#print axioms Paper7MomentCounts.b6TwoPoint_sums

theorem b6ThreePoint_sums (M N L : ℕ) (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ a, b6ThreePoint M N L i j k a) = M + N + L ∧
      (∑ a, (b6ThreePoint M N L i j k a : ℤ)^2) = (M : ℤ)^2 + (N : ℤ)^2 + (L : ℤ)^2 := by
  have hfun : b6ThreePoint M N L i j k = fun a =>
      b6TwoPoint M N i j a + if a = k then L else 0 := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [b6ThreePoint,b6TwoPoint,hik]
    · by_cases haj : a = j
      · subst a
        simp [b6ThreePoint,b6TwoPoint,hij.symm,hjk]
      · simp [b6ThreePoint,b6TwoPoint,hai,haj]
  have hsfun : (fun a => (b6ThreePoint M N L i j k a : ℤ)^2) =
      fun a => (b6TwoPoint M N i j a : ℤ)^2 + if a = k then (L : ℤ)^2 else 0 := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [b6ThreePoint,b6TwoPoint,hik]
    · by_cases haj : a = j
      · subst a
        simp [b6ThreePoint,b6TwoPoint,hij.symm,hjk]
      · by_cases hak : a = k
        · subst a
          simp [b6ThreePoint,b6TwoPoint,hik.symm,hjk.symm]
        · simp [b6ThreePoint,b6TwoPoint,hai,haj,hak]
  constructor
  · rw [hfun,Finset.sum_add_distrib,(b6TwoPoint_sums M N i j hij).1]
    simp
  · rw [hsfun,Finset.sum_add_distrib,(b6TwoPoint_sums M N i j hij).2]
    simp
#print axioms Paper7MomentCounts.b6ThreePoint_sums

theorem b6SpikeOnes_sums (M : ℕ) (i : Fin 6) (s : Finset (Fin 6)) (hi : i ∉ s) :
    (∑ k, b6SpikeOnes M i s k) = M + s.card ∧
      (∑ k, (b6SpikeOnes M i s k : ℤ)^2) = (M : ℤ)^2 + s.card := by
  have hf : b6SpikeOnes M i s = fun k =>
      (if k = i then M else 0) + (if k ∈ s then 1 else 0) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [b6SpikeOnes,hi]
    · simp [b6SpikeOnes,hk]
  have hsf : (fun k => (b6SpikeOnes M i s k : ℤ)^2) = fun k =>
      (if k = i then (M : ℤ)^2 else 0) + (if k ∈ s then 1 else 0) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [b6SpikeOnes,hi]
    · by_cases hs : k ∈ s <;> simp [b6SpikeOnes,hk,hs]
  constructor
  · rw [hf,Finset.sum_add_distrib]
    simp
  · rw [hsf,Finset.sum_add_distrib]
    simp
#print axioms Paper7MomentCounts.b6SpikeOnes_sums

theorem b6_set_mass_one (s : Finset (Fin 6)) (z : Fin 6 → ℕ)
    (hs : (∑ k ∈ s, z k) = 1) : ∃ j ∈ s, z j = 1 := by
  by_contra hn
  have hz : ∀ j ∈ s, z j = 0 := by
    intro j hj
    have hb := Finset.single_le_sum (s := s) (f := z) (fun _ _ => Nat.zero_le _) hj
    have hne : z j ≠ 1 := fun h => hn ⟨j,hj,h⟩
    omega
  have he := Finset.sum_eq_zero hz
  omega
#print axioms Paper7MomentCounts.b6_set_mass_one

theorem b6_mass_at_two (z : Fin 6 → ℕ) (M N : ℕ) (i j : Fin 6)
    (hij : i ≠ j) (hi : z i = M) (hj : z j = N) (hZ : (∑ k, z k) = M + N) :
    z = b6TwoPoint M N i j := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hjm : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ j⟩
  have hrest : (∑ k ∈ Finset.univ.erase i, z k) = z j := by omega
  funext k
  by_cases hki : k = i
  · subst k
    simp [b6TwoPoint,hi]
  · by_cases hkj : k = j
    · subst k
      simp [b6TwoPoint,hij.symm,hj]
    · have hkm : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
      have hz := b6_nat_mass_exhausted (Finset.univ.erase i) z j hjm hrest k hkm hkj
      simp [b6TwoPoint,hki,hkj,hz]
#print axioms Paper7MomentCounts.b6_mass_at_two

theorem b6_mass_at_three_with_unit (z : Fin 6 → ℕ) (M N : ℕ) (i j : Fin 6)
    (hij : i ≠ j) (hi : z i = M) (hj : z j = N) (hZ : (∑ k, z k) = M + N + 1) :
    ∃ k, i ≠ k ∧ j ≠ k ∧ z = b6ThreePoint M N 1 i j k := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hjm : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ j⟩
  have he2 := Finset.sum_erase_add (Finset.univ.erase i) z hjm
  have hr : (∑ k ∈ (Finset.univ.erase i).erase j, z k) = 1 := by omega
  obtain ⟨k,hkm,hk⟩ := b6_set_mass_one _ z hr
  have hkj := (Finset.mem_erase.mp hkm).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hkm).2).1
  refine ⟨k,hki.symm,hkj.symm,?_⟩
  funext a
  by_cases hai : a = i
  · subst a
    simp [b6ThreePoint,hi]
  · by_cases haj : a = j
    · subst a
      simp [b6ThreePoint,hij.symm,hj]
    · by_cases hak : a = k
      · subst a
        simp [b6ThreePoint,hki,hkj,hk]
      · have ham : a ∈ (Finset.univ.erase i).erase j :=
          Finset.mem_erase.mpr ⟨haj,Finset.mem_erase.mpr ⟨hai,Finset.mem_univ a⟩⟩
        have hz := b6_nat_mass_exhausted _ z k hkm (hr.trans hk.symm) a ham hak
        simp [b6ThreePoint,hai,haj,hak,hz]
#print axioms Paper7MomentCounts.b6_mass_at_three_with_unit

theorem b6_zero_one_remainder_shape (z : Fin 6 → ℕ) (M r : ℕ) (i : Fin 6)
    (hi : z i = M) (hr : (∑ k ∈ Finset.univ.erase i, z k) = r)
    (hc : ∀ k, k ≠ i → z k ≤ 1) :
    ∃ s : Finset (Fin 6), i ∉ s ∧ s.card = r ∧ z = b6SpikeOnes M i s := by
  let s := (Finset.univ.erase i).filter (fun k => z k = 1)
  have him : i ∉ s := by simp [s]
  have he : (∑ k ∈ Finset.univ.erase i, z k) =
      ∑ k ∈ Finset.univ.erase i, if z k = 1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hb := hc k (Finset.mem_erase.mp hk).1
    by_cases hone : z k = 1
    · simp [hone]
    · have hz : z k = 0 := by omega
      simp [hz]
  have hcard : s.card = r := by
    rw [Finset.sum_boole] at he
    exact he.symm.trans hr
  refine ⟨s,him,hcard,?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [b6SpikeOnes,hi]
  · have hb := hc k hki
    by_cases hone : z k = 1
    · simp [b6SpikeOnes,hki,s,hone]
    · have hz : z k = 0 := by omega
      simp [b6SpikeOnes,hki,s,hz]
#print axioms Paper7MomentCounts.b6_zero_one_remainder_shape

theorem b6_mass_four_cap_three_sq_le_ten (s : Finset (Fin 6)) (z : Fin 6 → ℕ)
    (hmass : (∑ k ∈ s, z k) = 4) (hcap : ∀ k ∈ s, z k ≤ 3) :
    (∑ k ∈ s, (z k : ℤ)^2) ≤ 10 := by
  by_cases hex : ∃ i ∈ s, z i = 3
  · obtain ⟨i,hi,hzi⟩ := hex
    have he := Finset.sum_erase_add s z hi
    have hr : (∑ k ∈ s.erase i, z k) = 1 := by omega
    have hrI : (∑ k ∈ s.erase i, (z k : ℤ)) = 1 := by exact_mod_cast hr
    have hb := Finset.sum_sq_le_sq_sum_of_nonneg (s := s.erase i)
      (f := fun k => (z k : ℤ)) (fun k _ => Int.natCast_nonneg (z k))
    rw [hrI] at hb
    have he2 := Finset.sum_erase_add s (fun k => (z k : ℤ)^2) hi
    have hiI : (z i : ℤ) = 3 := by exact_mod_cast hzi
    nlinarith only [hb,he2,hiI]
  · have htwo : ∀ k ∈ s, z k ≤ 2 := by
      intro k hk
      have hb := hcap k hk
      have hn : z k ≠ 3 := fun hz => hex ⟨k,hk,hz⟩
      omega
    have hs := Finset.sum_le_sum (s := s) (f := fun k => (z k : ℤ)^2)
      (g := fun k => 2*(z k : ℤ)) (by
        intro k hk
        have h0 := Int.natCast_nonneg (z k)
        have h2 : (z k : ℤ) ≤ 2 := by exact_mod_cast htwo k hk
        nlinarith only [h0,h2])
    have hmI : (∑ k ∈ s, (z k : ℤ)) = 4 := by exact_mod_cast hmass
    rw [← Finset.mul_sum,hmI] at hs
    omega
#print axioms Paper7MomentCounts.b6_mass_four_cap_three_sq_le_ten

def B6NineShapes (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  (∃ i j, i ≠ j ∧ z = b6TwoPoint 6 3 i j ∧ (Q = 0 ∨ Q = 6)) ∨
  (∃ i j, i ≠ j ∧ z = b6TwoPoint 7 2 i j ∧ Q = 2) ∨
  (∃ (i : Fin 6) (s : Finset (Fin 6)), i ∉ s ∧ s.card = 2 ∧ z = b6SpikeOnes 7 i s ∧ Q = 3) ∨
  (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ z = b6ThreePoint 6 2 1 i j k ∧ Q = 8) ∨
  (∃ (i : Fin 6) (s : Finset (Fin 6)), i ∉ s ∧ s.card = 3 ∧ z = b6SpikeOnes 6 i s ∧ Q = 9) ∨
  (∃ i j, i ≠ j ∧ z = b6TwoPoint 5 4 i j ∧ Q = 8)
#print axioms Paper7MomentCounts.B6NineShapes

theorem b6_nine_guard_complete_shapes (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ k, z k) = 9) (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) :
    B6NineShapes z Q := by
  obtain ⟨i,⟨hi,hi7⟩,_huniq⟩ := b6_nine_guard_unique_dominant z Q hZ hQ hg
  have er := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have restbound (k : Fin 6) (hki : k ≠ i) : z k ≤ 9 - z i := by
    have hm : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
    have hb := Finset.single_le_sum (s := Finset.univ.erase i) (f := z) (fun _ _ => Nat.zero_le _) hm
    omega
  have hs := b6_nine_guard_square_bounds z Q hQ hg
  have hicases : z i = 5 ∨ z i = 6 ∨ z i = 7 := by omega
  rcases hicases with h5 | h6 | h7
  · have hr : (∑ k ∈ Finset.univ.erase i, z k) = 4 := by omega
    have hex : ∃ j, j ≠ i ∧ z j = 4 := by
      by_contra hn
      have hc : ∀ k ∈ Finset.univ.erase i, z k ≤ 3 := by
        intro k hk
        have hki := (Finset.mem_erase.mp hk).1
        have hb := restbound k hki
        have hne : z k ≠ 4 := fun he => hn ⟨k,hki,he⟩
        omega
      have hb := b6_mass_four_cap_three_sq_le_ten _ z hr hc
      have he2 := Finset.sum_erase_add Finset.univ (fun k => (z k : ℤ)^2) (Finset.mem_univ i)
      have hiI : (z i : ℤ) = 5 := by exact_mod_cast h5
      nlinarith only [hs.1,hb,he2,hiI]
    obtain ⟨j,hji,hj⟩ := hex
    have hz := b6_mass_at_two z 5 4 i j hji.symm h5 hj hZ
    have hq : Q = 8 := by
      rw [hz] at hg
      unfold b6NineMomentGuard at hg
      rw [(b6TwoPoint_sums 5 4 i j hji.symm).2] at hg
      rcases hg with ⟨_hz,he⟩ | ⟨_h2,he⟩ <;> omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,j,hji.symm,hz,hq⟩))))
  · have hr : (∑ k ∈ Finset.univ.erase i, z k) = 3 := by omega
    by_cases hthree : ∃ j, j ≠ i ∧ z j = 3
    · obtain ⟨j,hji,hj⟩ := hthree
      have hz := b6_mass_at_two z 6 3 i j hji.symm h6 hj hZ
      have hq : Q = 0 ∨ Q = 6 := by
        rw [hz] at hg
        unfold b6NineMomentGuard at hg
        rw [(b6TwoPoint_sums 6 3 i j hji.symm).2] at hg
        rcases hg with ⟨h0,_he⟩ | ⟨_h2,he⟩
        · exact Or.inl h0
        · exact Or.inr (by omega)
      exact Or.inl ⟨i,j,hji.symm,hz,hq⟩
    · by_cases htwo : ∃ j, j ≠ i ∧ z j = 2
      · obtain ⟨j,hji,hj⟩ := htwo
        obtain ⟨k,hik,hjk,hz⟩ := b6_mass_at_three_with_unit z 6 2 i j hji.symm h6 hj hZ
        have hq : Q = 8 := by
          rw [hz] at hg
          unfold b6NineMomentGuard at hg
          rw [(b6ThreePoint_sums 6 2 1 i j k hji.symm hik hjk).2] at hg
          rcases hg with ⟨_h0,he⟩ | ⟨_h2,he⟩ <;> omega
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,j,k,hji.symm,hik,hjk,hz,hq⟩)))
      · have hc : ∀ k, k ≠ i → z k ≤ 1 := by
          intro k hki
          have hb := restbound k hki
          have h3 : z k ≠ 3 := fun he => hthree ⟨k,hki,he⟩
          have h2 : z k ≠ 2 := fun he => htwo ⟨k,hki,he⟩
          omega
        obtain ⟨s,his,hcard,hz⟩ := b6_zero_one_remainder_shape z 6 3 i h6 hr hc
        have hq : Q = 9 := by
          rw [hz] at hg
          unfold b6NineMomentGuard at hg
          rw [(b6SpikeOnes_sums 6 i s his).2,hcard] at hg
          rcases hg with ⟨_h0,he⟩ | ⟨_h2,he⟩ <;> omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,s,his,hcard,hz,hq⟩))))
  · have hr : (∑ k ∈ Finset.univ.erase i, z k) = 2 := by omega
    by_cases htwo : ∃ j, j ≠ i ∧ z j = 2
    · obtain ⟨j,hji,hj⟩ := htwo
      have hz := b6_mass_at_two z 7 2 i j hji.symm h7 hj hZ
      have hq : Q = 2 := by
        rw [hz] at hg
        unfold b6NineMomentGuard at hg
        rw [(b6TwoPoint_sums 7 2 i j hji.symm).2] at hg
        rcases hg with ⟨_h0,he⟩ | ⟨_h2,he⟩ <;> omega
      exact Or.inr (Or.inl ⟨i,j,hji.symm,hz,hq⟩)
    · have hc : ∀ k, k ≠ i → z k ≤ 1 := by
        intro k hki
        have hb := restbound k hki
        have h2 : z k ≠ 2 := fun he => htwo ⟨k,hki,he⟩
        omega
      obtain ⟨s,his,hcard,hz⟩ := b6_zero_one_remainder_shape z 7 2 i h7 hr hc
      have hq : Q = 3 := by
        rw [hz] at hg
        unfold b6NineMomentGuard at hg
        rw [(b6SpikeOnes_sums 7 i s his).2,hcard] at hg
        rcases hg with ⟨_h0,he⟩ | ⟨_h2,he⟩ <;> omega
      exact Or.inr (Or.inr (Or.inl ⟨i,s,his,hcard,hz,hq⟩))
#print axioms Paper7MomentCounts.b6_nine_guard_complete_shapes

theorem b6_nine_shapes_accept (z : Fin 6 → ℕ) (Q : ℕ) (hs : B6NineShapes z Q) :
    (∑ k, z k) = 9 ∧ Q ≤ 9 ∧ b6ZQAccept z Q := by
  have from_guard (hZ : (∑ k, z k) = 9) (hQ : Q ≤ 9) (hg : b6NineMomentGuard z Q) :
      (∑ k, z k) = 9 ∧ Q ≤ 9 ∧ b6ZQAccept z Q :=
    ⟨hZ,hQ,(b6_zq_accept_total_nine_iff z Q hZ hQ).mpr hg⟩
  rcases hs with ⟨i,j,hij,rfl,hq⟩ | ⟨i,j,hij,rfl,rfl⟩ | ⟨i,s,his,hc,rfl,rfl⟩ |
    ⟨i,j,k,hij,hik,hjk,rfl,rfl⟩ | ⟨i,s,his,hc,rfl,rfl⟩ | ⟨i,j,hij,rfl,rfl⟩
  · rcases hq with rfl | rfl <;>
      apply from_guard (b6TwoPoint_sums 6 3 i j hij).1 (by decide) <;>
      simp [b6NineMomentGuard,(b6TwoPoint_sums 6 3 i j hij).2]
  · apply from_guard (b6TwoPoint_sums 7 2 i j hij).1 (by decide)
    simp [b6NineMomentGuard,(b6TwoPoint_sums 7 2 i j hij).2]
  · apply from_guard (by simpa [hc] using (b6SpikeOnes_sums 7 i s his).1) (by decide)
    simp [b6NineMomentGuard,(b6SpikeOnes_sums 7 i s his).2,hc]
  · apply from_guard (b6ThreePoint_sums 6 2 1 i j k hij hik hjk).1 (by decide)
    simp [b6NineMomentGuard,(b6ThreePoint_sums 6 2 1 i j k hij hik hjk).2]
  · apply from_guard (by simpa [hc] using (b6SpikeOnes_sums 6 i s his).1) (by decide)
    simp [b6NineMomentGuard,(b6SpikeOnes_sums 6 i s his).2,hc]
  · apply from_guard (b6TwoPoint_sums 5 4 i j hij).1 (by decide)
    simp [b6NineMomentGuard,(b6TwoPoint_sums 5 4 i j hij).2]
#print axioms Paper7MomentCounts.b6_nine_shapes_accept

end Paper7MomentCounts
