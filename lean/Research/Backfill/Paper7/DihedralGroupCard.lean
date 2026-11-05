import Research.Backfill.Paper7.DihedralBurnsideBridge

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported MomentCounts Stage 02 and Stage 01 candidate chain remains pending.
This module has not been compiled or accepted. It identifies the actual frozen
IsDihedral subgroup with two copies of Fin b for b >= 3. It supplies no numerical
moment count, fixed-word count, or cycle-block certificate.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

/-- An actual circle translation, regarded as a member of the frozen subgroup. -/
def dihedralCardRotation (n : ℕ) (hb : 3 ≤ n + 3) (c : Fin (n + 3)) :
    dihedralSubgroup (n + 3) hb :=
  ⟨(Paper7Setup.cycleTranslation n c).toEquiv,
    Paper7Setup.cycle_iso_isDihedral (n + 3) hb (Paper7Setup.cycleTranslation n c)⟩

#print axioms Paper7MomentCounts.dihedralCardRotation

/-- An actual circle reflection, regarded as a member of the frozen subgroup. -/
def dihedralCardReflection (n : ℕ) (hb : 3 ≤ n + 3) (c : Fin (n + 3)) :
    dihedralSubgroup (n + 3) hb :=
  ⟨(Paper7Setup.cycleReflection n c).toEquiv,
    Paper7Setup.cycle_iso_isDihedral (n + 3) hb (Paper7Setup.cycleReflection n c)⟩

#print axioms Paper7MomentCounts.dihedralCardReflection

/-- At zero the two parameters agree; at one their equality would force 2 = 0. -/
theorem dihedralCardRotation_ne_reflection (n : ℕ) (hb : 3 ≤ n + 3)
    (c d : Fin (n + 3)) :
    dihedralCardRotation n hb c ≠ dihedralCardReflection n hb d := by
  intro h
  have h0 := congrArg
    (fun g : dihedralSubgroup (n + 3) hb => g.val (0 : Fin (n + 3))) h
  change (0 : Fin (n + 3)) + c = d - 0 at h0
  have hcd : c = d := by simpa only [zero_add, sub_zero] using h0
  have h1 := congrArg
    (fun g : dihedralSubgroup (n + 3) hb => g.val (1 : Fin (n + 3))) h
  change (1 : Fin (n + 3)) + c = d - 1 at h1
  rw [← hcd] at h1
  have hsum : (1 : Fin (n + 3)) + c + 1 = c :=
    eq_sub_iff_add_eq.mp h1
  have hcancel : c + ((1 : Fin (n + 3)) + 1) = c + 0 := by
    calc
      c + ((1 : Fin (n + 3)) + 1) = (1 + c) + 1 := by abel
      _ = c := hsum
      _ = c + 0 := (add_zero c).symm
  have htwo : (1 : Fin (n + 3)) + 1 = 0 := add_left_cancel hcancel
  have hval : 2 % (n + 3) = 0 := congrArg Fin.val htwo
  rw [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at hval
  omega

#print axioms Paper7MomentCounts.dihedralCardRotation_ne_reflection

/-- The two affine families, with their orientation retained as a sum tag. -/
def dihedralCardEncode (n : ℕ) (hb : 3 ≤ n + 3) :
    Fin (n + 3) ⊕ Fin (n + 3) → dihedralSubgroup (n + 3) hb
  | .inl c => dihedralCardRotation n hb c
  | .inr c => dihedralCardReflection n hb c

#print axioms Paper7MomentCounts.dihedralCardEncode

theorem dihedralCardEncode_injective (n : ℕ) (hb : 3 ≤ n + 3) :
    Function.Injective (dihedralCardEncode n hb) := by
  intro x y h
  cases x with
  | inl c =>
    cases y with
    | inl d =>
      have h0 := congrArg
        (fun g : dihedralSubgroup (n + 3) hb => g.val (0 : Fin (n + 3))) h
      change (0 : Fin (n + 3)) + c = 0 + d at h0
      have hcd : c = d := by simpa only [zero_add] using h0
      exact congrArg Sum.inl hcd
    | inr d =>
      exact (dihedralCardRotation_ne_reflection n hb c d h).elim
  | inr c =>
    cases y with
    | inl d =>
      exact (dihedralCardRotation_ne_reflection n hb d c h.symm).elim
    | inr d =>
      have h0 := congrArg
        (fun g : dihedralSubgroup (n + 3) hb => g.val (0 : Fin (n + 3))) h
      change c - (0 : Fin (n + 3)) = d - 0 at h0
      have hcd : c = d := by simpa only [sub_zero] using h0
      exact congrArg Sum.inr hcd

#print axioms Paper7MomentCounts.dihedralCardEncode_injective

theorem dihedralCardEncode_surjective (n : ℕ) (hb : 3 ≤ n + 3) :
    Function.Surjective (dihedralCardEncode n hb) := by
  intro g
  rcases Paper7Setup.isDihedral_affine n (fun k => g.val k) g.property with
    ⟨c, hc⟩ | ⟨c, hc⟩
  · refine ⟨Sum.inl c, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro k
    change k + c = g.val k
    exact (hc k).symm
  · refine ⟨Sum.inr c, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro k
    change c - k = g.val k
    exact (hc k).symm

#print axioms Paper7MomentCounts.dihedralCardEncode_surjective

def dihedralCardAffineEquiv (n : ℕ) (hb : 3 ≤ n + 3) :
    (Fin (n + 3) ⊕ Fin (n + 3)) ≃ dihedralSubgroup (n + 3) hb :=
  Equiv.ofBijective (dihedralCardEncode n hb)
    ⟨dihedralCardEncode_injective n hb, dihedralCardEncode_surjective n hb⟩

#print axioms Paper7MomentCounts.dihedralCardAffineEquiv

theorem dihedralCardEquiv_nonempty (b : ℕ) (hb : 3 ≤ b) :
    Nonempty (dihedralSubgroup b hb ≃ (Fin b ⊕ Fin b)) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  exact ⟨(dihedralCardAffineEquiv n hb).symm⟩

#print axioms Paper7MomentCounts.dihedralCardEquiv_nonempty

/-- The actual subgroup, rather than an assumed abstract dihedral group, has two families. -/
def dihedralSubgroupEquiv (b : ℕ) (hb : 3 ≤ b) :
    dihedralSubgroup b hb ≃ (Fin b ⊕ Fin b) :=
  Classical.choice (dihedralCardEquiv_nonempty b hb)

#print axioms Paper7MomentCounts.dihedralSubgroupEquiv

theorem dihedralSubgroup_card (b : ℕ) (hb : 3 ≤ b) :
    Fintype.card (dihedralSubgroup b hb) = 2 * b := by
  calc
    Fintype.card (dihedralSubgroup b hb) = Fintype.card (Fin b ⊕ Fin b) :=
      Fintype.card_congr (dihedralSubgroupEquiv b hb)
    _ = 2 * b := by simp only [Fintype.card_sum, Fintype.card_fin, two_mul]

#print axioms Paper7MomentCounts.dihedralSubgroup_card

end Paper7MomentCounts
