import Research.Backfill.Paper5.Proof.DiagramCoordinates

set_option autoImplicit false

namespace CodexPaper5.DiagramRanksOccurring

open BackfillPaper5

/-- Actual graph existence is equivalent to existence of a legal half, via real extraction/glue. -/
theorem rankOccurs_iff_exists_half (D : Challenge.Fam) (n r : ℕ) :
    Challenge.RankOccurs D n r ↔ ∃ l, l ∈ Challenge.Hr D n r := by
  constructor
  · rintro ⟨x, hx, hr⟩
    exact ⟨Challenge.topHalf x,
      DiagramExtraction.topHalf_mem_hr (D := D) (r := r) ⟨hx, hr⟩⟩
  · rintro ⟨l, hl⟩
    have hx := DiagramCoordinates.glue_mem_Jr hl hl (Equiv.refl l.1)
    exact ⟨DiagramCoordinates.glue l l (Equiv.refl l.1), hx.1, hx.2⟩

theorem half_card_le {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : r ≤ n := by
  calc
    r = l.1.card := hl.1.symm
    _ ≤ n := by simpa only [Fintype.card_fin] using l.1.card_le_univ

/-- The actual half-diagram involution, with itself as its inverse. -/
def halfPerm {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Equiv.Perm (Fin n) where
  toFun := l.2
  invFun := l.2
  left_inv := hl.2.1
  right_inv := hl.2.1

theorem halfPerm_sq {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : halfPerm hl ^ 2 = 1 := by
  rw [pow_two]
  apply Equiv.ext
  intro a
  exact hl.2.1 a

/-- In the Brauer family the nonfixed points are exactly the complement of the free set. -/
theorem halfPerm_support_eq_compl {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr Challenge.Fam.B n r) : (halfPerm hl).support = l.1ᶜ := by
  apply Finset.ext
  intro a
  rw [Equiv.Perm.mem_support, Finset.mem_compl]
  change l.2 a ≠ a ↔ a ∉ l.1
  constructor
  · intro hne ha
    exact hne (hl.2.2.1 a ha)
  · intro ha
    exact hl.2.2.2 rfl a ha

theorem two_dvd_complement {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr Challenge.Fam.B n r) : 2 ∣ n - r := by
  have hs := Equiv.Perm.two_dvd_card_support (halfPerm_sq hl)
  simpa only [halfPerm_support_eq_compl hl, Finset.card_compl, Fintype.card_fin, hl.1] using hs

theorem brauer_half_parity {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr Challenge.Fam.B n r) : r % 2 = n % 2 := by
  have hle := half_card_le hl
  have hmod : (n - r) % 2 = 0 := Nat.mod_eq_zero_of_dvd (two_dvd_complement hl)
  omega

/-- Exchange of two equal finite summands gives an actual fixed-point-free involution. -/
theorem exists_fixedPointFree_involution (C : Type*) [Fintype C]
    (heven : Even (Fintype.card C)) :
    ∃ δ : C → C, Function.Involutive δ ∧ ∀ a, δ a ≠ a := by
  classical
  obtain ⟨k, hk⟩ := heven
  have hcard : Fintype.card C = Fintype.card (Fin k ⊕ Fin k) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hk
  let e : C ≃ (Fin k ⊕ Fin k) := Fintype.equivOfCardEq hcard
  let δ : C → C := fun a => e.symm (Sum.swap (e a))
  refine ⟨δ, ?_, ?_⟩
  · intro a
    change e.symm (Sum.swap (e (e.symm (Sum.swap (e a))))) = a
    rw [e.apply_symm_apply, Sum.swap_swap, e.symm_apply_apply]
  · intro a ha
    have he := congrArg e ha
    change e (e.symm (Sum.swap (e a))) = e a at he
    have hs : Sum.swap (e a) = e a := by simpa only [e.apply_symm_apply] using he
    cases h : e a with
    | inl b =>
      have hh : (Sum.inr b : Fin k ⊕ Fin k) = Sum.inl b := by
        simpa only [h, Sum.swap_inl] using hs
      exact Sum.inr_ne_inl hh
    | inr b =>
      have hh : (Sum.inl b : Fin k ⊕ Fin k) = Sum.inr b := by
        simpa only [h, Sum.swap_inr] using hs
      exact Sum.inl_ne_inr hh

/-- Fix the free set and use the supplied actual function on its complement. -/
def extendOnComplement {n : ℕ} (F : Finset (Fin n)) (δ : ↥(Fᶜ) → ↥(Fᶜ))
    (a : Fin n) : Fin n :=
  if ha : a ∈ F then a else (δ ⟨a, Finset.mem_compl.mpr ha⟩).val

theorem extendOnComplement_of_mem {n : ℕ} (F : Finset (Fin n))
    (δ : ↥(Fᶜ) → ↥(Fᶜ)) {a : Fin n} (ha : a ∈ F) :
    extendOnComplement F δ a = a := by
  simp only [extendOnComplement, dite_eq_left ha]

theorem extendOnComplement_coe {n : ℕ} (F : Finset (Fin n))
    (δ : ↥(Fᶜ) → ↥(Fᶜ)) (a : ↥(Fᶜ)) :
    extendOnComplement F δ a.val = (δ a).val := by
  have ha : a.val ∉ F := Finset.mem_compl.mp a.property
  simp only [extendOnComplement, dite_eq_right ha]

theorem extendOnComplement_involutive {n : ℕ} (F : Finset (Fin n))
    (δ : ↥(Fᶜ) → ↥(Fᶜ)) (hδ : Function.Involutive δ) :
    Function.Involutive (extendOnComplement F δ) := by
  intro a
  by_cases ha : a ∈ F
  · simp only [extendOnComplement_of_mem F δ ha]
  · let c : ↥(Fᶜ) := ⟨a, Finset.mem_compl.mpr ha⟩
    have hfirst : extendOnComplement F δ a = (δ c).val := extendOnComplement_coe F δ c
    rw [hfirst, extendOnComplement_coe F δ (δ c)]
    exact congrArg Subtype.val (hδ c)

theorem extendOnComplement_ne {n : ℕ} (F : Finset (Fin n))
    (δ : ↥(Fᶜ) → ↥(Fᶜ)) (hδ : ∀ c, δ c ≠ c) {a : Fin n} (ha : a ∉ F) :
    extendOnComplement F δ a ≠ a := by
  intro h
  let c : ↥(Fᶜ) := ⟨a, Finset.mem_compl.mpr ha⟩
  have hc : (δ c).val = c.val := (extendOnComplement_coe F δ c).symm.trans h
  exact hδ c (Subtype.ext hc)

theorem exists_pb_half {n r : ℕ} (hle : r ≤ n) :
    ∃ l, l ∈ Challenge.Hr Challenge.Fam.PB n r := by
  have hrcard : r ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hle
  obtain ⟨F, _hFsub, hF⟩ := Finset.exists_subset_card_eq hrcard
  refine ⟨(F, id), hF, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a _ha
    rfl
  · intro hD
    cases hD

theorem exists_brauer_half {n r : ℕ} (hle : r ≤ n) (hpar : r % 2 = n % 2) :
    ∃ l, l ∈ Challenge.Hr Challenge.Fam.B n r := by
  classical
  have hrcard : r ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hle
  obtain ⟨F, _hFsub, hF⟩ := Finset.exists_subset_card_eq hrcard
  have hcard : Fintype.card ↥(Fᶜ) = n - r := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hF]
  have heven : Even (Fintype.card ↥(Fᶜ)) := by
    rw [hcard, Nat.even_iff]
    omega
  obtain ⟨δ, hinv, hne⟩ := exists_fixedPointFree_involution ↥(Fᶜ) heven
  refine ⟨(F, extendOnComplement F δ), hF, extendOnComplement_involutive F δ hinv, ?_, ?_⟩
  · intro a ha
    exact extendOnComplement_of_mem F δ ha
  · intro _hD a ha
    exact extendOnComplement_ne F δ hne ha

theorem rankOccurs_B_iff (n r : ℕ) :
    Challenge.RankOccurs Challenge.Fam.B n r ↔ r ≤ n ∧ r % 2 = n % 2 := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := (rankOccurs_iff_exists_half Challenge.Fam.B n r).mp h
    exact ⟨half_card_le hl, brauer_half_parity hl⟩
  · rintro ⟨hle, hpar⟩
    exact (rankOccurs_iff_exists_half Challenge.Fam.B n r).mpr (exists_brauer_half hle hpar)

theorem rankOccurs_PB_iff (n r : ℕ) : Challenge.RankOccurs Challenge.Fam.PB n r ↔ r ≤ n := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := (rankOccurs_iff_exists_half Challenge.Fam.PB n r).mp h
    exact half_card_le hl
  · intro hle
    exact (rankOccurs_iff_exists_half Challenge.Fam.PB n r).mpr (exists_pb_half hle)

theorem check_RanksOccurring : Challenge.RanksOccurring := by
  intro n r
  exact ⟨rankOccurs_B_iff n r, rankOccurs_PB_iff n r⟩

#print axioms CodexPaper5.DiagramRanksOccurring.rankOccurs_iff_exists_half
#print axioms CodexPaper5.DiagramRanksOccurring.half_card_le
#print axioms CodexPaper5.DiagramRanksOccurring.halfPerm
#print axioms CodexPaper5.DiagramRanksOccurring.halfPerm_sq
#print axioms CodexPaper5.DiagramRanksOccurring.halfPerm_support_eq_compl
#print axioms CodexPaper5.DiagramRanksOccurring.two_dvd_complement
#print axioms CodexPaper5.DiagramRanksOccurring.brauer_half_parity
#print axioms CodexPaper5.DiagramRanksOccurring.exists_fixedPointFree_involution
#print axioms CodexPaper5.DiagramRanksOccurring.extendOnComplement
#print axioms CodexPaper5.DiagramRanksOccurring.extendOnComplement_of_mem
#print axioms CodexPaper5.DiagramRanksOccurring.extendOnComplement_coe
#print axioms CodexPaper5.DiagramRanksOccurring.extendOnComplement_involutive
#print axioms CodexPaper5.DiagramRanksOccurring.extendOnComplement_ne
#print axioms CodexPaper5.DiagramRanksOccurring.exists_pb_half
#print axioms CodexPaper5.DiagramRanksOccurring.exists_brauer_half
#print axioms CodexPaper5.DiagramRanksOccurring.rankOccurs_B_iff
#print axioms CodexPaper5.DiagramRanksOccurring.rankOccurs_PB_iff
#print axioms CodexPaper5.DiagramRanksOccurring.check_RanksOccurring

end CodexPaper5.DiagramRanksOccurring
