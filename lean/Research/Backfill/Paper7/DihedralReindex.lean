import Research.Backfill.Paper7.SunReindexIso

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge

def cycleTranslation (n : ℕ) (c : Fin (n + 3)) :
    cycleGraph (n + 3) ≃g cycleGraph (n + 3) where
  toEquiv := Equiv.addRight c
  map_rel_iff' := by
    intro i j
    change (cycleGraph (n + 3)).Adj (i + c) (j + c) ↔ _
    rw [cycleGraph_adj, cycleGraph_adj]
    have h1 : (i + c) - (j + c) = i - j := by abel
    have h2 : (j + c) - (i + c) = j - i := by abel
    rw [h1, h2]

#print axioms Paper7Setup.cycleTranslation

def cycleReflection (n : ℕ) (c : Fin (n + 3)) :
    cycleGraph (n + 3) ≃g cycleGraph (n + 3) where
  toEquiv := Equiv.subLeft c
  map_rel_iff' := by
    intro i j
    change (cycleGraph (n + 3)).Adj (c - i) (c - j) ↔ _
    rw [cycleGraph_adj, cycleGraph_adj]
    have h1 : (c - i) - (c - j) = j - i := by abel
    have h2 : (c - j) - (c - i) = i - j := by abel
    rw [h1, h2]
    exact or_comm

#print axioms Paper7Setup.cycleReflection

/-- The frozen natural-number congruence definition gives one of the two
affine permutations of Fin (n+3), without presupposing bijectivity. -/
theorem isDihedral_affine (n : ℕ) (σ : Fin (n + 3) → Fin (n + 3))
    (hσ : IsDihedral (n + 3) σ) :
    (∃ c : Fin (n + 3), ∀ k, σ k = k + c) ∨
      (∃ c : Fin (n + 3), ∀ k, σ k = c - k) := by
  obtain ⟨c, hr | hf⟩ := hσ
  · apply Or.inl
    refine ⟨⟨c % (n + 3), Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro k
    apply Fin.ext
    change (σ k).val = (k.val + c % (n + 3)) % (n + 3)
    rw [hr]
    simp only [Nat.add_mod, Nat.mod_mod]
  · apply Or.inr
    refine ⟨⟨c % (n + 3), Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro k
    apply eq_sub_iff_add_eq.mpr
    apply Fin.ext
    change ((σ k).val + k.val) % (n + 3) = c % (n + 3)
    exact hf k

#print axioms Paper7Setup.isDihedral_affine

theorem cycle_iso_of_isDihedral (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) :
    ∃ e : cycleGraph b ≃g cycleGraph b, ∀ k, e k = σ k := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  rcases isDihedral_affine n σ hσ with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨cycleTranslation n c, fun k => (hc k).symm⟩
  · exact ⟨cycleReflection n c, fun k => (hc k).symm⟩

#print axioms Paper7Setup.cycle_iso_of_isDihedral

/-- The reverse direction of the exact frozen isomorphism classification:
every permitted dihedral reindexing gives an actual full sun-graph isomorphism. -/
theorem sg_iso_of_dihedral (b : ℕ) (p q p' q' : Fin b → ℕ) (hb : 3 ≤ b)
    (σ : Fin b → Fin b) (hσ : IsDihedral b σ)
    (hp : p' = p ∘ σ) (hq : q' = q ∘ σ) :
    Nonempty (SG b p q ≃g SG b p' q') := by
  obtain ⟨e, he⟩ := cycle_iso_of_isDihedral b hb σ hσ
  have hp' : p' = p ∘ e := by
    funext k
    rw [hp]
    change p (σ k) = p (e k)
    rw [he]
  have hq' : q' = q ∘ e := by
    funext k
    rw [hq]
    change q (σ k) = q (e k)
    rw [he]
  rw [hp', hq']
  exact ⟨(sgReindexIso b p q hb e).symm⟩

#print axioms Paper7Setup.sg_iso_of_dihedral

end Paper7Setup
