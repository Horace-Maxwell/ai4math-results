import Research.Backfill.Paper5.Proof.HalfCounting
import Research.Backfill.Paper5.Proof.BrauerTriangleBasics

set_option autoImplicit false

namespace CodexPaper5.BrauerMatchingLabels

open BackfillPaper5

/-- The actual rank-r free sets excluding exactly the three frozen free labels. -/
abbrev RemainingLabels (n r : ℕ) :=
  {F : HalfCounting.FreeSets n r //
    ∀ j : Fin 3, F.val ≠ (Challenge.triHalf n r j).1}

theorem triPartner_injective : Function.Injective Challenge.triPartner := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- Distinct triangle indices omit distinct actual prefix points. -/
theorem triHalf_free_injective (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) :
    Function.Injective (fun j : Fin 3 => (Challenge.triHalf n r j).1) := by
  intro i j hij
  apply triPartner_injective
  by_contra hp
  let a : Fin n := ⟨Challenge.triPartner i,
    BrauerTriangleBasics.triPartner_lt_n n r hr hn i⟩
  have hj : a ∈ (Challenge.triHalf n r j).1 :=
    (BrauerTriangleBasics.triHalf_free_iff n r j a).mpr
      ⟨BrauerTriangleBasics.triPartner_lt_prefix r hr i,
        ne_of_gt (BrauerTriangleBasics.triPartner_pos i), hp⟩
  have hi : a ∈ (Challenge.triHalf n r i).1 := by
    rw [show (Challenge.triHalf n r i).1 = (Challenge.triHalf n r j).1 from hij]
    exact hj
  exact ((BrauerTriangleBasics.triHalf_free_iff n r i a).mp hi).2.2 rfl

def triLabel (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) : HalfCounting.FreeSets n r :=
  ⟨(Challenge.triHalf n r j).1, BrauerTriangleBasics.triHalf_card n r hr hn j⟩

theorem triLabel_injective (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Function.Injective (triLabel n r hr hn) := by
  intro i j h
  exact triHalf_free_injective n r hr hn (congrArg Subtype.val h)

def specialLabels (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Finset (HalfCounting.FreeSets n r) := Finset.univ.image (triLabel n r hr hn)

theorem specialLabels_card (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    (specialLabels n r hr hn).card = 3 := by
  simpa only [specialLabels, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective Finset.univ (triLabel_injective n r hr hn)

theorem mem_specialLabels (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (F : HalfCounting.FreeSets n r) :
    F ∈ specialLabels n r hr hn ↔ ∃ j : Fin 3, F.val = (Challenge.triHalf n r j).1 := by
  simp only [specialLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, congrArg Subtype.val hj.symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj.symm⟩

theorem three_le_choose (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    3 ≤ n.choose r := by
  have h := (specialLabels n r hr hn).card_le_univ
  rwa [specialLabels_card n r hr hn, HalfCounting.card_freeSets] at h

theorem card_remainingLabels (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Fintype.card (RemainingLabels n r) = n.choose r - 3 := by
  classical
  let S := specialLabels n r hr hn
  let e : RemainingLabels n r ≃ {F : HalfCounting.FreeSets n r // F ∉ S} :=
    Equiv.subtypeEquivRight (fun F => by
      rw [mem_specialLabels n r hr hn F]
      simp only [not_exists])
  calc
    Fintype.card (RemainingLabels n r) =
        Fintype.card {F : HalfCounting.FreeSets n r // F ∉ S} := Fintype.card_congr e
    _ = Fintype.card (HalfCounting.FreeSets n r) -
        Fintype.card {F : HalfCounting.FreeSets n r // F ∈ S} :=
      Fintype.card_subtype_compl (fun F => F ∈ S)
    _ = n.choose r - 3 := by
      rw [HalfCounting.card_freeSets, Fintype.card_coe, specialLabels_card n r hr hn]

theorem even_remainingLabels (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (hodd : Odd (n.choose r)) :
    Even (Fintype.card (RemainingLabels n r)) := by
  rw [card_remainingLabels n r hr hn, Nat.even_iff]
  have hmod := Nat.odd_iff.mp hodd
  have hle := three_le_choose n r hr hn
  omega

theorem difference_card_le (n r : ℕ) (F G : HalfCounting.FreeSets n r) :
    (F.val \ G.val).card ≤ r := by
  calc
    (F.val \ G.val).card ≤ F.val.card := Finset.card_le_card Finset.sdiff_subset
    _ = r := F.property

theorem difference_bound_two (n : ℕ) (hn : 6 ≤ n)
    (F G : HalfCounting.FreeSets n 2) : 2 + 2 * (F.val \ G.val).card ≤ n := by
  have h := difference_card_le n 2 F G
  omega

theorem difference_bound_three (n : ℕ) (hn : 9 ≤ n)
    (F G : HalfCounting.FreeSets n 3) : 3 + 2 * (F.val \ G.val).card ≤ n := by
  have h := difference_card_le n 3 F G
  omega

/-- The complete 16 pairs of the exceptional (7,3) boundary, as actual free sets. -/
def tableFree (x : Fin 16 × Bool) : Finset (Fin 7) :=
  match x.1.val, x.2 with
  | 0, false => {0, 1, 5}
  | 0, true => {0, 1, 6}
  | 1, false => {0, 2, 5}
  | 1, true => {0, 2, 6}
  | 2, false => {0, 3, 5}
  | 2, true => {0, 3, 6}
  | 3, false => {0, 4, 5}
  | 3, true => {0, 4, 6}
  | 4, false => {1, 2, 5}
  | 4, true => {1, 2, 6}
  | 5, false => {1, 3, 5}
  | 5, true => {1, 3, 6}
  | 6, false => {1, 4, 5}
  | 6, true => {1, 4, 6}
  | 7, false => {2, 3, 5}
  | 7, true => {2, 3, 6}
  | 8, false => {2, 4, 5}
  | 8, true => {2, 4, 6}
  | 9, false => {3, 4, 5}
  | 9, true => {3, 4, 6}
  | 10, false => {0, 5, 6}
  | 10, true => {0, 1, 2}
  | 11, false => {1, 5, 6}
  | 11, true => {0, 1, 3}
  | 12, false => {2, 5, 6}
  | 12, true => {0, 2, 3}
  | 13, false => {3, 5, 6}
  | 13, true => {1, 2, 3}
  | 14, false => {4, 5, 6}
  | 14, true => {0, 1, 4}
  | 15, false => {0, 2, 4}
  | 15, true => {0, 3, 4}
  | _, _ => {0, 3, 4}

/-- Explicit reverse lookup of the table; the final row is the default. -/
def tableLookup (F : Finset (Fin 7)) : Fin 16 × Bool :=
  if F = {0, 1, 5} then (0, false) else
  if F = {0, 1, 6} then (0, true) else
  if F = {0, 2, 5} then (1, false) else
  if F = {0, 2, 6} then (1, true) else
  if F = {0, 3, 5} then (2, false) else
  if F = {0, 3, 6} then (2, true) else
  if F = {0, 4, 5} then (3, false) else
  if F = {0, 4, 6} then (3, true) else
  if F = {1, 2, 5} then (4, false) else
  if F = {1, 2, 6} then (4, true) else
  if F = {1, 3, 5} then (5, false) else
  if F = {1, 3, 6} then (5, true) else
  if F = {1, 4, 5} then (6, false) else
  if F = {1, 4, 6} then (6, true) else
  if F = {2, 3, 5} then (7, false) else
  if F = {2, 3, 6} then (7, true) else
  if F = {2, 4, 5} then (8, false) else
  if F = {2, 4, 6} then (8, true) else
  if F = {3, 4, 5} then (9, false) else
  if F = {3, 4, 6} then (9, true) else
  if F = {0, 5, 6} then (10, false) else
  if F = {0, 1, 2} then (10, true) else
  if F = {1, 5, 6} then (11, false) else
  if F = {0, 1, 3} then (11, true) else
  if F = {2, 5, 6} then (12, false) else
  if F = {0, 2, 3} then (12, true) else
  if F = {3, 5, 6} then (13, false) else
  if F = {1, 2, 3} then (13, true) else
  if F = {4, 5, 6} then (14, false) else
  if F = {0, 1, 4} then (14, true) else
  if F = {0, 2, 4} then (15, false) else
  (15, true)

theorem tableFree_card (x : Fin 16 × Bool) : (tableFree x).card = 3 := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

theorem tableFree_ne_tri (x : Fin 16 × Bool) (j : Fin 3) :
    tableFree x ≠ (Challenge.triHalf 7 3 j).1 := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> fin_cases j <;> decide

theorem tableLookup_tableFree (x : Fin 16 × Bool) :
    tableLookup (tableFree x) = x := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

theorem tableFree_injective : Function.Injective tableFree :=
  (show Function.LeftInverse tableLookup tableFree from tableLookup_tableFree).injective

def tableLabel (x : Fin 16 × Bool) : RemainingLabels 7 3 :=
  ⟨⟨tableFree x, tableFree_card x⟩, tableFree_ne_tri x⟩

theorem tableLabel_injective : Function.Injective tableLabel := by
  intro x y h
  exact tableFree_injective (congrArg (fun F : RemainingLabels 7 3 => F.val.val) h)

theorem card_remainingLabels_small : Fintype.card (RemainingLabels 7 3) = 32 := by
  calc
    Fintype.card (RemainingLabels 7 3) = (7 : ℕ).choose 3 - 3 :=
      card_remainingLabels 7 3 (Or.inr rfl) (by decide)
    _ = 32 := by decide

/-- Injection and exact cardinality prove coverage of every remaining actual label. -/
theorem tableLabel_bijective : Function.Bijective tableLabel := by
  apply (Fintype.bijective_iff_injective_and_card tableLabel).mpr
  refine ⟨tableLabel_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, card_remainingLabels_small]

noncomputable def smallLabelEquiv : (Fin 16 × Bool) ≃ RemainingLabels 7 3 :=
  Equiv.ofBijective tableLabel tableLabel_bijective

theorem smallLabelEquiv_val (x : Fin 16 × Bool) :
    (smallLabelEquiv x).val.val = tableFree x := rfl

theorem tableFree_pair_bound (i : Fin 16) :
    3 + 2 * (tableFree (i, false) \ tableFree (i, true)).card ≤ 7 := by
  fin_cases i <;> decide

/-- A single actual equivalence pairs all nonspecial labels with the real join bound. -/
theorem exists_label_pairing (n r : ℕ) (hr : r = 2 ∨ r = 3) (hlt : r < n)
    (hpar : n % 2 = r % 2) (hgap : 4 ≤ n - r) (hodd : Odd (n.choose r)) :
    ∃ k : ℕ, ∃ e : (Fin k × Bool) ≃ RemainingLabels n r,
      ∀ i : Fin k, r + 2 * ((e (i, false)).val.val \ (e (i, true)).val.val).card ≤ n := by
  classical
  have hn : r + 2 ≤ n :=
    calc
      r + 2 ≤ r + (n - r) := Nat.add_le_add_left (by omega) r
      _ = n := Nat.add_sub_of_le (Nat.le_of_lt hlt)
  by_cases hsmall : r = 3 ∧ n = 7
  · rcases hsmall with ⟨rfl, rfl⟩
    refine ⟨16, smallLabelEquiv, ?_⟩
    intro i
    rw [smallLabelEquiv_val, smallLabelEquiv_val]
    exact tableFree_pair_bound i
  · have hall : ∀ F G : HalfCounting.FreeSets n r,
        r + 2 * (F.val \ G.val).card ≤ n := by
      rcases hr with rfl | rfl
      · exact difference_bound_two n (by omega)
      · have hnot7 : n ≠ 7 := fun hn7 => hsmall ⟨rfl, hn7⟩
        exact difference_bound_three n (by omega)
    obtain ⟨k, hk⟩ := even_remainingLabels n r hr hn hodd
    have hcard : Fintype.card (Fin k × Bool) = Fintype.card (RemainingLabels n r) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_two] using hk.symm
    let e : (Fin k × Bool) ≃ RemainingLabels n r := Fintype.equivOfCardEq hcard
    refine ⟨k, e, ?_⟩
    intro i
    exact hall (e (i, false)).val (e (i, true)).val

#print axioms CodexPaper5.BrauerMatchingLabels.RemainingLabels
#print axioms CodexPaper5.BrauerMatchingLabels.triPartner_injective
#print axioms CodexPaper5.BrauerMatchingLabels.triHalf_free_injective
#print axioms CodexPaper5.BrauerMatchingLabels.triLabel
#print axioms CodexPaper5.BrauerMatchingLabels.triLabel_injective
#print axioms CodexPaper5.BrauerMatchingLabels.specialLabels
#print axioms CodexPaper5.BrauerMatchingLabels.specialLabels_card
#print axioms CodexPaper5.BrauerMatchingLabels.mem_specialLabels
#print axioms CodexPaper5.BrauerMatchingLabels.three_le_choose
#print axioms CodexPaper5.BrauerMatchingLabels.card_remainingLabels
#print axioms CodexPaper5.BrauerMatchingLabels.even_remainingLabels
#print axioms CodexPaper5.BrauerMatchingLabels.difference_card_le
#print axioms CodexPaper5.BrauerMatchingLabels.difference_bound_two
#print axioms CodexPaper5.BrauerMatchingLabels.difference_bound_three
#print axioms CodexPaper5.BrauerMatchingLabels.tableFree
#print axioms CodexPaper5.BrauerMatchingLabels.tableLookup
#print axioms CodexPaper5.BrauerMatchingLabels.tableFree_card
#print axioms CodexPaper5.BrauerMatchingLabels.tableFree_ne_tri
#print axioms CodexPaper5.BrauerMatchingLabels.tableLookup_tableFree
#print axioms CodexPaper5.BrauerMatchingLabels.tableFree_injective
#print axioms CodexPaper5.BrauerMatchingLabels.tableLabel
#print axioms CodexPaper5.BrauerMatchingLabels.tableLabel_injective
#print axioms CodexPaper5.BrauerMatchingLabels.card_remainingLabels_small
#print axioms CodexPaper5.BrauerMatchingLabels.tableLabel_bijective
#print axioms CodexPaper5.BrauerMatchingLabels.smallLabelEquiv
#print axioms CodexPaper5.BrauerMatchingLabels.smallLabelEquiv_val
#print axioms CodexPaper5.BrauerMatchingLabels.tableFree_pair_bound
#print axioms CodexPaper5.BrauerMatchingLabels.exists_label_pairing

end CodexPaper5.BrauerMatchingLabels

