import Research.Backfill.Paper6.FlatBasics
import Research.Backfill.Paper6.TransversalDim
import Research.Backfill.Paper6.InclusionExclusion

/-!
# Paper 6 V3: sums of one, two and three arbitrary large affine flats

The frozen PropD is proved for all nonempty affine subspaces of dimension at
least seven, allowing repeated flats and the whole space. The only finite
certificate concerns small integer intersection sizes after the actual affine
geometry has supplied the necessary product bound. In the empty triple-
intersection case that bound is strict, by Mathlib's strict direction-span
inequality for two nonempty disjoint affine subspaces.

Frozen FROZEN.json SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Source candidate only; compilation and acceptance are root-controlled.
-/

set_option autoImplicit false

namespace Paper6ThreeFlats

open BackfillPaper6.V3
open Paper6InclusionExclusion

abbrev Flat := AffineSubspace (ZMod 2) (Pt 14)

noncomputable def size (F : Flat) : ℕ := (F : Set (Pt 14)).ncard

noncomputable def dim (F : Flat) : ℕ := Module.finrank (ZMod 2) F.direction

theorem hammingNorm_ind (S : Set (Pt 14)) : hammingNorm (ind S) = S.ncard := by
  classical
  unfold hammingNorm
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  by_cases hx : x ∈ S <;> simp [ind, hx]

theorem sum_bit_ind (S : Set (Pt 14)) :
    (∑ x : Pt 14, bit (ind S x)) = (S.ncard : ℤ) := by
  rw [← weight_as_sum, hammingNorm_ind]

theorem weight_two (F G : Flat) :
    (hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) : ℤ) =
      (size F : ℤ) + (size G : ℤ) - 2 * (size (F ⊓ G) : ℤ) := by
  classical
  have hpoint (x : Pt 14) :
      bit ((ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) x) =
        bit (ind (F : Set (Pt 14)) x) + bit (ind (G : Set (Pt 14)) x) -
          2 * bit (ind ((F : Set (Pt 14)) ∩ G) x) := by
    by_cases hF : x ∈ F <;> by_cases hG : x ∈ G <;>
      norm_num [ind, bit, hF, hG]
    all_goals decide
  calc
    (hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) : ℤ) =
        ∑ x : Pt 14, bit ((ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) x) :=
      weight_as_sum _
    _ = ∑ x : Pt 14,
        (bit (ind (F : Set (Pt 14)) x) + bit (ind (G : Set (Pt 14)) x) -
          2 * bit (ind ((F : Set (Pt 14)) ∩ G) x)) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (size F : ℤ) + (size G : ℤ) - 2 * (size (F ⊓ G) : ℤ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_bit_ind, size, AffineSubspace.coe_inf]

theorem weight_three (F G H : Flat) :
    (hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14)) +
      ind (H : Set (Pt 14))) : ℤ) =
      (size F : ℤ) + (size G : ℤ) + (size H : ℤ) -
        2 * ((size (F ⊓ G) : ℤ) + (size (F ⊓ H) : ℤ) + (size (G ⊓ H) : ℤ)) +
        4 * (size (F ⊓ G ⊓ H) : ℤ) := by
  classical
  have hpoint (x : Pt 14) :
      bit ((ind (F : Set (Pt 14)) + ind (G : Set (Pt 14)) +
        ind (H : Set (Pt 14))) x) =
      bit (ind (F : Set (Pt 14)) x) + bit (ind (G : Set (Pt 14)) x) +
        bit (ind (H : Set (Pt 14)) x) -
        2 * (bit (ind ((F : Set (Pt 14)) ∩ G) x) +
          bit (ind ((F : Set (Pt 14)) ∩ H) x) +
          bit (ind ((G : Set (Pt 14)) ∩ H) x)) +
        4 * bit (ind (((F : Set (Pt 14)) ∩ G) ∩ H) x) := by
    by_cases hF : x ∈ F <;> by_cases hG : x ∈ G <;> by_cases hH : x ∈ H <;>
      norm_num [ind, bit, hF, hG, hH] <;> decide
  calc
    (hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14)) +
        ind (H : Set (Pt 14))) : ℤ) =
      ∑ x : Pt 14, bit ((ind (F : Set (Pt 14)) + ind (G : Set (Pt 14)) +
        ind (H : Set (Pt 14))) x) := weight_as_sum _
    _ = ∑ x : Pt 14,
      (bit (ind (F : Set (Pt 14)) x) + bit (ind (G : Set (Pt 14)) x) +
        bit (ind (H : Set (Pt 14)) x) -
        2 * (bit (ind ((F : Set (Pt 14)) ∩ G) x) +
          bit (ind ((F : Set (Pt 14)) ∩ H) x) +
          bit (ind ((G : Set (Pt 14)) ∩ H) x)) +
        4 * bit (ind (((F : Set (Pt 14)) ∩ G) ∩ H) x)) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (size F : ℤ) + (size G : ℤ) + (size H : ℤ) -
        2 * ((size (F ⊓ G) : ℤ) + (size (F ⊓ H) : ℤ) + (size (G ⊓ H) : ℤ)) +
        4 * (size (F ⊓ G ⊓ H) : ℤ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_bit_ind, size, AffineSubspace.coe_inf]

theorem size_eq_pow (F : Flat) (hF : (F : Set (Pt 14)).Nonempty) : size F = 2 ^ dim F := by
  obtain ⟨p, hp⟩ := hF
  exact Paper6FlatBasics.flat_ncard F p hp (dim F) rfl

theorem dim_le_fourteen (F : Flat) : dim F ≤ 14 := by
  exact (Submodule.finrank_le F.direction).trans_eq (Paper6Geometry.ambient_finrank 14)

theorem size_eq_zero_of_empty (F : Flat) (hF : ¬ (F : Set (Pt 14)).Nonempty) :
    size F = 0 := by
  unfold size
  rw [Set.not_nonempty_iff_eq_empty.mp hF, Set.ncard_empty]

theorem size_mod_two_or_one (F : Flat) : size F % 2 = 0 ∨ size F = 1 := by
  by_cases hF : (F : Set (Pt 14)).Nonempty
  · rw [size_eq_pow F hF]
    by_cases hd : dim F = 0
    · right
      simp [hd]
    · left
      apply Nat.mod_eq_zero_of_dvd
      simpa using pow_dvd_pow (2 : ℕ) (show 1 ≤ dim F by omega)
  · left
    rw [size_eq_zero_of_empty F hF]

theorem size_mod_four (F : Flat) (hF : (F : Set (Pt 14)).Nonempty) (hd : 7 ≤ dim F) :
    size F % 4 = 0 := by
  rw [size_eq_pow F hF]
  apply Nat.mod_eq_zero_of_dvd
  simpa using pow_dvd_pow (2 : ℕ) (show 2 ≤ dim F by omega)

theorem mem_U_mod_four (w : ℕ) (hw : w ∈ U) : w % 4 = 2 := by
  simp only [U, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The direction dimensions of the two intersections add, and their sum fits inside F3.
If the intersections are nonempty and disjoint, the inequality is strict. -/
theorem intersection_product_bound (F1 F2 F3 : Flat) (h12 : size (F1 ⊓ F2) = 1) :
    size (F1 ⊓ F3) * size (F2 ⊓ F3) ≤ 2 ^ dim F3 ∧
    (size (F1 ⊓ F2 ⊓ F3) = 0 →
      size (F1 ⊓ F3) * size (F2 ⊓ F3) < 2 ^ dim F3) := by
  let A : Flat := F1 ⊓ F3
  let B : Flat := F2 ⊓ F3
  change size A * size B ≤ 2 ^ dim F3 ∧
    (size (F1 ⊓ F2 ⊓ F3) = 0 → size A * size B < 2 ^ dim F3)
  by_cases hA : (A : Set (Pt 14)).Nonempty
  · by_cases hB : (B : Set (Pt 14)).Nonempty
    · have htrans : F1.direction ⊓ F2.direction = ⊥ :=
        Paper6Geometry.direction_inf_eq_bot_of_inter_ncard_one F1 F2 h12
      have hbot : A.direction ⊓ B.direction = ⊥ := by
        refine le_antisymm ?_ bot_le
        calc
          A.direction ⊓ B.direction ≤ F1.direction ⊓ F2.direction :=
            inf_le_inf (AffineSubspace.direction_le (show A ≤ F1 from inf_le_left))
              (AffineSubspace.direction_le (show B ≤ F2 from inf_le_left))
          _ = ⊥ := htrans
      have hrank : dim A + dim B =
          Module.finrank (ZMod 2) (A.direction ⊔ B.direction : Submodule (ZMod 2) (Pt 14)) := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq A.direction B.direction
        rw [hbot, finrank_bot, add_zero] at h
        exact h.symm
      have hle : A.direction ⊔ B.direction ≤ F3.direction :=
        sup_le (AffineSubspace.direction_le (show A ≤ F3 from inf_le_right))
          (AffineSubspace.direction_le (show B ≤ F3 from inf_le_right))
      have hdim : dim A + dim B ≤ dim F3 := by
        rw [hrank]
        exact Submodule.finrank_mono hle
      constructor
      · rw [size_eq_pow A hA, size_eq_pow B hB, ← pow_add]
        exact Nat.pow_le_pow_right (by decide) hdim
      · intro hzero
        have ht : ((F1 ⊓ F2 ⊓ F3 : Flat) : Set (Pt 14)) = ∅ :=
          (Set.ncard_eq_zero
            (Set.toFinite (((F1 ⊓ F2 ⊓ F3 : Flat) : Set (Pt 14))))).mp hzero
        have he : ((A : Set (Pt 14)) ∩ B) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          change (x ∈ F1 ∧ x ∈ F3) ∧ (x ∈ F2 ∧ x ∈ F3) at hx
          have hx' : x ∈ ((F1 ⊓ F2 ⊓ F3 : Flat) : Set (Pt 14)) :=
            ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
          rw [ht] at hx'
          exact hx'
        have hstrict := Submodule.finrank_lt_finrank_of_lt
          (AffineSubspace.sup_direction_lt_of_nonempty_of_inter_empty hA hB he)
        have hsup : A ⊔ B ≤ F3 := sup_le inf_le_right inf_le_right
        have hupper := Submodule.finrank_mono (AffineSubspace.direction_le hsup)
        have hdimstrict : dim A + dim B < dim F3 := by
          rw [hrank]
          exact lt_of_lt_of_le hstrict hupper
        rw [size_eq_pow A hA, size_eq_pow B hB, ← pow_add]
        exact Nat.pow_lt_pow_right (by decide) hdimstrict
    · rw [size_eq_zero_of_empty B hB, mul_zero]
      exact ⟨Nat.zero_le _, fun _ => Nat.two_pow_pos _⟩
  · rw [size_eq_zero_of_empty A hA, zero_mul]
    exact ⟨Nat.zero_le _, fun _ => Nat.two_pow_pos _⟩

def pairSizes : Finset ℕ := {0, 2, 4, 8, 16, 32, 64, 128}

theorem positive_power_mem_pairSizes (k : ℕ) (hk : k ≤ 7) (h0 : k ≠ 0) :
    2 ^ k ∈ pairSizes := by
  interval_cases k <;> norm_num [pairSizes] at *

/-- An intersection with a seven-flat, unless singleton, has one of the actual allowed sizes. -/
theorem intersection_size_mem (F G : Flat) (hd : dim F = 7)
    (hne : size (F ⊓ G) ≠ 1) : size (F ⊓ G) ∈ pairSizes := by
  by_cases hFG : ((F ⊓ G : Flat) : Set (Pt 14)).Nonempty
  · have hk : dim (F ⊓ G) ≤ 7 :=
      (Submodule.finrank_mono (AffineSubspace.direction_le
        (inf_le_left : F ⊓ G ≤ F))).trans_eq hd
    have h0 : dim (F ⊓ G) ≠ 0 := by
      intro hz
      apply hne
      rw [size_eq_pow (F ⊓ G) hFG, hz, pow_zero]
    rw [size_eq_pow (F ⊓ G) hFG]
    exact positive_power_mem_pairSizes _ hk h0
  · rw [size_eq_zero_of_empty (F ⊓ G) hFG]
    simp [pairSizes]

set_option maxRecDepth 8192 in
/-- All remaining arithmetic is finite and only used after the actual geometric bounds.
Here d is dimension minus seven, a and b are intersection cardinalities, and t
is the cardinality of the triple intersection with a fixed singleton pair. -/
theorem one_transversal_arithmetic :
    ∀ d : Fin 8, ∀ a ∈ pairSizes, ∀ b ∈ pairSizes, ∀ t : Fin 2,
      t.val ≤ a → t.val ≤ b →
      (if t.val = 0 then a * b < 2 ^ (7 + d.val) else a * b ≤ 2 ^ (7 + d.val)) →
      ∀ w ∈ U, (w : ℤ) ≠
        254 + (2 : ℤ) ^ (7 + d.val) - 2 * ((a : ℤ) + (b : ℤ)) + 4 * (t.val : ℤ) := by
  decide +kernel

theorem size_mono {F G : Flat} (h : F ≤ G) : size F ≤ size G :=
  Set.ncard_mono h

theorem one_flat_not_mem_U (F : Flat) (hF : (F : Set (Pt 14)).Nonempty)
    (hd : 7 ≤ dim F) : hammingNorm (ind (F : Set (Pt 14))) ∉ U := by
  intro hw
  have hm := mem_U_mod_four _ hw
  rw [hammingNorm_ind] at hm
  have hc := size_mod_four F hF hd
  change (F : Set (Pt 14)).ncard % 4 = 0 at hc
  omega

theorem two_flats_not_mem_U (F G : Flat)
    (hF : (F : Set (Pt 14)).Nonempty) (hG : (G : Set (Pt 14)).Nonempty)
    (hdF : 7 ≤ dim F) (hdG : 7 ≤ dim G) :
    hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) ∉ U := by
  intro hw
  have hm := mem_U_mod_four _ hw
  have hf := size_mod_four F hF hdF
  have hg := size_mod_four G hG hdG
  have heq := weight_two F G
  by_cases hi : size (F ⊓ G) = 1
  · have hd := Paper6Geometry.check_TransversalDim F G hdF hdG hi
    have hdF' : dim F = 7 := hd.1
    have hdG' : dim G = 7 := hd.2
    have hcF : size F = 128 := by rw [size_eq_pow F hF, hdF']; norm_num
    have hcG : size G = 128 := by rw [size_eq_pow G hG, hdG']; norm_num
    rw [hcF, hcG, hi] at heq
    have hw254 : hammingNorm (ind (F : Set (Pt 14)) + ind (G : Set (Pt 14))) = 254 := by
      omega
    rw [hw254] at hw
    norm_num [U] at hw
  · have heven := (size_mod_two_or_one (F ⊓ G)).resolve_right hi
    omega

/-- A fixed transversal pair leaves only the two geometric cases certified above.
All other pairs are explicitly allowed to be transversal as well. -/
theorem three_flats_with_transversal_not_mem_U (F1 F2 F3 : Flat)
    (hF1 : (F1 : Set (Pt 14)).Nonempty) (hF2 : (F2 : Set (Pt 14)).Nonempty)
    (hF3 : (F3 : Set (Pt 14)).Nonempty)
    (hd1 : 7 ≤ dim F1) (hd2 : 7 ≤ dim F2) (hd3 : 7 ≤ dim F3)
    (h12 : size (F1 ⊓ F2) = 1) :
    hammingNorm (ind (F1 : Set (Pt 14)) + ind (F2 : Set (Pt 14)) +
      ind (F3 : Set (Pt 14))) ∉ U := by
  intro hw
  have hm := mem_U_mod_four _ hw
  have hm1 := size_mod_four F1 hF1 hd1
  have hm2 := size_mod_four F2 hF2 hd2
  have hm3 := size_mod_four F3 hF3 hd3
  have heq := weight_three F1 F2 F3
  have hd12 := Paper6Geometry.check_TransversalDim F1 F2 hd1 hd2 h12
  have hdim1 : dim F1 = 7 := hd12.1
  have hdim2 : dim F2 = 7 := hd12.2
  have hc1 : size F1 = 128 := by rw [size_eq_pow F1 hF1, hdim1]; norm_num
  have hc2 : size F2 = 128 := by rw [size_eq_pow F2 hF2, hdim2]; norm_num
  have ht : size (F1 ⊓ F2 ⊓ F3) ≤ 1 :=
    (size_mono (inf_le_left : F1 ⊓ F2 ⊓ F3 ≤ F1 ⊓ F2)).trans_eq h12
  by_cases h13 : size (F1 ⊓ F3) = 1
  · by_cases h23 : size (F2 ⊓ F3) = 1
    · have hdim3 : dim F3 = 7 :=
        (Paper6Geometry.check_TransversalDim F1 F3 hd1 hd3 h13).2
      have hc3 : size F3 = 128 := by rw [size_eq_pow F3 hF3, hdim3]; norm_num
      rw [hc1, hc2, hc3, h12, h13, h23] at heq
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> omega
    · have hm23 := (size_mod_two_or_one (F2 ⊓ F3)).resolve_right h23
      omega
  · by_cases h23 : size (F2 ⊓ F3) = 1
    · have hm13 := (size_mod_two_or_one (F1 ⊓ F3)).resolve_right h13
      omega
    · have ha := intersection_size_mem F1 F3 hdim1 h13
      have hb := intersection_size_mem F2 F3 hdim2 h23
      have hprod := intersection_product_bound F1 F2 F3 h12
      let d : Fin 8 := ⟨dim F3 - 7, by have h := dim_le_fourteen F3; omega⟩
      have hdim : 7 + d.val = dim F3 := by
        dsimp [d]
        omega
      let t : Fin 2 := ⟨size (F1 ⊓ F2 ⊓ F3), by omega⟩
      have hta : t.val ≤ size (F1 ⊓ F3) := by
        apply size_mono
        intro x hx
        exact ⟨hx.1.1, hx.2⟩
      have htb : t.val ≤ size (F2 ⊓ F3) := by
        apply size_mono
        intro x hx
        exact ⟨hx.1.2, hx.2⟩
      have hgeo :
          if t.val = 0 then size (F1 ⊓ F3) * size (F2 ⊓ F3) < 2 ^ (7 + d.val)
          else size (F1 ⊓ F3) * size (F2 ⊓ F3) ≤ 2 ^ (7 + d.val) := by
        by_cases hz : t.val = 0
        · rw [ite_eq_left hz, hdim]
          exact hprod.2 hz
        · rw [ite_eq_right hz, hdim]
          exact hprod.1
      have hbad := one_transversal_arithmetic d (size (F1 ⊓ F3)) ha
        (size (F2 ⊓ F3)) hb t hta htb hgeo _ hw
      have hpow : (size F3 : ℤ) = (2 : ℤ) ^ dim F3 := by
        exact_mod_cast size_eq_pow F3 hF3
      apply hbad
      change (hammingNorm (ind (F1 : Set (Pt 14)) + ind (F2 : Set (Pt 14)) +
        ind (F3 : Set (Pt 14))) : ℤ) =
        254 + (2 : ℤ) ^ (7 + d.val) -
          2 * ((size (F1 ⊓ F3) : ℤ) + (size (F2 ⊓ F3) : ℤ)) +
          4 * (size (F1 ⊓ F2 ⊓ F3) : ℤ)
      rw [hdim, weight_three, hc1, hc2, h12, hpow]
      ring

/-- Any possible weight in U forces a transversal pair; reorder the three flats to use it. -/
theorem three_flats_not_mem_U (F1 F2 F3 : Flat)
    (hF1 : (F1 : Set (Pt 14)).Nonempty) (hF2 : (F2 : Set (Pt 14)).Nonempty)
    (hF3 : (F3 : Set (Pt 14)).Nonempty)
    (hd1 : 7 ≤ dim F1) (hd2 : 7 ≤ dim F2) (hd3 : 7 ≤ dim F3) :
    hammingNorm (ind (F1 : Set (Pt 14)) + ind (F2 : Set (Pt 14)) +
      ind (F3 : Set (Pt 14))) ∉ U := by
  intro hw
  by_cases h12 : size (F1 ⊓ F2) = 1
  · exact three_flats_with_transversal_not_mem_U F1 F2 F3 hF1 hF2 hF3 hd1 hd2 hd3 h12 hw
  · by_cases h13 : size (F1 ⊓ F3) = 1
    · apply three_flats_with_transversal_not_mem_U F1 F3 F2 hF1 hF3 hF2 hd1 hd3 hd2 h13
      simpa only [add_assoc, add_left_comm, add_comm] using hw
    · by_cases h23 : size (F2 ⊓ F3) = 1
      · apply three_flats_with_transversal_not_mem_U F2 F3 F1 hF2 hF3 hF1 hd2 hd3 hd1 h23
        simpa only [add_assoc, add_left_comm, add_comm] using hw
      · have hm := mem_U_mod_four _ hw
        have hm1 := size_mod_four F1 hF1 hd1
        have hm2 := size_mod_four F2 hF2 hd2
        have hm3 := size_mod_four F3 hF3 hd3
        have hm12 := (size_mod_two_or_one (F1 ⊓ F2)).resolve_right h12
        have hm13 := (size_mod_two_or_one (F1 ⊓ F3)).resolve_right h13
        have hm23 := (size_mod_two_or_one (F2 ⊓ F3)).resolve_right h23
        have heq := weight_three F1 F2 F3
        omega

/-- The exact three-conjunct frozen proposition, without distinctness or proper-flat assumptions. -/
theorem propD : BackfillPaper6.V3.PropD := by
  intro F1 F2 F3 hF1 hF2 hF3 hd1 hd2 hd3
  exact ⟨one_flat_not_mem_U F1 hF1 hd1,
    two_flats_not_mem_U F1 F2 hF1 hF2 hd1 hd2,
    three_flats_not_mem_U F1 F2 F3 hF1 hF2 hF3 hd1 hd2 hd3⟩

/-- Exact contract check; the alias does not add a mathematical result. -/
theorem check_PropD : BackfillPaper6.V3.PropD := propD

end Paper6ThreeFlats

#print axioms Paper6ThreeFlats.Flat
#print axioms Paper6ThreeFlats.size
#print axioms Paper6ThreeFlats.dim
#print axioms Paper6ThreeFlats.hammingNorm_ind
#print axioms Paper6ThreeFlats.sum_bit_ind
#print axioms Paper6ThreeFlats.weight_two
#print axioms Paper6ThreeFlats.weight_three
#print axioms Paper6ThreeFlats.size_eq_pow
#print axioms Paper6ThreeFlats.dim_le_fourteen
#print axioms Paper6ThreeFlats.size_eq_zero_of_empty
#print axioms Paper6ThreeFlats.size_mod_two_or_one
#print axioms Paper6ThreeFlats.size_mod_four
#print axioms Paper6ThreeFlats.mem_U_mod_four
#print axioms Paper6ThreeFlats.intersection_product_bound
#print axioms Paper6ThreeFlats.pairSizes
#print axioms Paper6ThreeFlats.positive_power_mem_pairSizes
#print axioms Paper6ThreeFlats.intersection_size_mem
#print axioms Paper6ThreeFlats.one_transversal_arithmetic
#print axioms Paper6ThreeFlats.size_mono
#print axioms Paper6ThreeFlats.one_flat_not_mem_U
#print axioms Paper6ThreeFlats.two_flats_not_mem_U
#print axioms Paper6ThreeFlats.three_flats_with_transversal_not_mem_U
#print axioms Paper6ThreeFlats.three_flats_not_mem_U
#print axioms Paper6ThreeFlats.propD
#print axioms Paper6ThreeFlats.check_PropD
#print Paper6ThreeFlats.check_PropD
