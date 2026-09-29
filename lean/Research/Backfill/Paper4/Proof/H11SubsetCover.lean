import Research.Backfill.Paper4.Proof.ConcreteDHCertificate

/-! Exact 6+5 decomposition of every actual Finset of eleven vertices.
The only finite powerset equalities below have 64 and 32 entries.
Acceptance evidence is recorded separately; no H11 distance-heredity is claimed. -/
set_option autoImplicit false

namespace CodexPaper4.H11SubsetCover

def lowVertex (i : Fin 6) : Fin 11 := ⟨i.val, by omega⟩
def highVertex (i : Fin 5) : Fin 11 := ⟨i.val + 6, by omega⟩

def low (S : Finset (Fin 11)) : Finset (Fin 6) :=
  Finset.univ.filter fun i => lowVertex i ∈ S

def high (S : Finset (Fin 11)) : Finset (Fin 5) :=
  Finset.univ.filter fun i => highVertex i ∈ S

def join (L : Finset (Fin 6)) (H : Finset (Fin 5)) : Finset (Fin 11) :=
  L.image lowVertex ∪ H.image highVertex

theorem join_low_high (S : Finset (Fin 11)) : join (low S) (high S) = S := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hl | hh
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact (Finset.mem_filter.mp hi).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
      exact (Finset.mem_filter.mp hi).2
  · intro hv
    change v ∈ (low S).image lowVertex ∪ (high S).image highVertex
    by_cases h : v.val < 6
    · let i : Fin 6 := ⟨v.val, h⟩
      have he : lowVertex i = v := by
        apply Fin.ext
        rfl
      apply Finset.mem_union.mpr
      left
      refine Finset.mem_image.mpr ⟨i, ?_, he⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, he.symm ▸ hv⟩
    · let i : Fin 5 := ⟨v.val - 6, by have := v.isLt; omega⟩
      have he : highVertex i = v := by
        apply Fin.ext
        dsimp [highVertex, i]
        omega
      apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨i, ?_, he⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, he.symm ▸ hv⟩

/-- Shared small enumerations, independently of any graph certificates. -/
def lowSubsets : List (Finset (Fin 6)) := [
  ∅,
  {0},
  {1},
  {0, 1},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  {3},
  {0, 3},
  {1, 3},
  {0, 1, 3},
  {2, 3},
  {0, 2, 3},
  {1, 2, 3},
  {0, 1, 2, 3},
  {4},
  {0, 4},
  {1, 4},
  {0, 1, 4},
  {2, 4},
  {0, 2, 4},
  {1, 2, 4},
  {0, 1, 2, 4},
  {3, 4},
  {0, 3, 4},
  {1, 3, 4},
  {0, 1, 3, 4},
  {2, 3, 4},
  {0, 2, 3, 4},
  {1, 2, 3, 4},
  {0, 1, 2, 3, 4},
  {5},
  {0, 5},
  {1, 5},
  {0, 1, 5},
  {2, 5},
  {0, 2, 5},
  {1, 2, 5},
  {0, 1, 2, 5},
  {3, 5},
  {0, 3, 5},
  {1, 3, 5},
  {0, 1, 3, 5},
  {2, 3, 5},
  {0, 2, 3, 5},
  {1, 2, 3, 5},
  {0, 1, 2, 3, 5},
  {4, 5},
  {0, 4, 5},
  {1, 4, 5},
  {0, 1, 4, 5},
  {2, 4, 5},
  {0, 2, 4, 5},
  {1, 2, 4, 5},
  {0, 1, 2, 4, 5},
  {3, 4, 5},
  {0, 3, 4, 5},
  {1, 3, 4, 5},
  {0, 1, 3, 4, 5},
  {2, 3, 4, 5},
  {0, 2, 3, 4, 5},
  {1, 2, 3, 4, 5},
  {0, 1, 2, 3, 4, 5}]

def highSubsets : List (Finset (Fin 5)) := [
  ∅,
  {0},
  {1},
  {0, 1},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  {3},
  {0, 3},
  {1, 3},
  {0, 1, 3},
  {2, 3},
  {0, 2, 3},
  {1, 2, 3},
  {0, 1, 2, 3},
  {4},
  {0, 4},
  {1, 4},
  {0, 1, 4},
  {2, 4},
  {0, 2, 4},
  {1, 2, 4},
  {0, 1, 2, 4},
  {3, 4},
  {0, 3, 4},
  {1, 3, 4},
  {0, 1, 3, 4},
  {2, 3, 4},
  {0, 2, 3, 4},
  {1, 2, 3, 4},
  {0, 1, 2, 3, 4}]

lemma low_powerset : (Finset.univ : Finset (Fin 6)).powerset = lowSubsets.toFinset := by
  decide +kernel

lemma high_powerset : (Finset.univ : Finset (Fin 5)).powerset = highSubsets.toFinset := by
  decide +kernel

theorem low_complete (L : Finset (Fin 6)) : L ∈ lowSubsets := by
  apply List.mem_toFinset.mp
  rw [← low_powerset]
  exact Finset.mem_powerset.mpr (Finset.subset_univ L)

theorem high_complete (H : Finset (Fin 5)) : H ∈ highSubsets := by
  apply List.mem_toFinset.mp
  rw [← high_powerset]
  exact Finset.mem_powerset.mpr (Finset.subset_univ H)

theorem coverage (S : Finset (Fin 11)) :
    ∃ L ∈ lowSubsets, ∃ H ∈ highSubsets, join L H = S :=
  ⟨low S, low_complete _, high S, high_complete _, join_low_high S⟩

theorem blocks_cover (P : Finset (Fin 11) → Prop)
    (hblocks : ∀ H ∈ highSubsets, ∀ L ∈ lowSubsets, P (join L H)) : ∀ S, P S := by
  intro S
  obtain ⟨L, hL, H, hH, hS⟩ := coverage S
  rw [← hS]
  exact hblocks H hH L hL

/-- Conditional assembly only: this requires all 32 blocks, not the two cost probes.
Choice extracts explicit witnesses already established by the point certificates. -/
theorem all_block_certificates_valid (G : SimpleGraph (Fin 11))
    (D : Fin 11 → Fin 11 → ℕ)
    (hblocks : ∀ H ∈ highSubsets, ∀ L ∈ lowSubsets,
      ∃ C : Finset (Fin 11), ConcreteDHCertificate.Cut G (join L H) C ∨
        ConcreteDHCertificate.Descent G D (join L H)) :
    ∃ cut : Finset (Fin 11) → Finset (Fin 11), ConcreteDHCertificate.Valid G D cut := by
  have hall : ∀ S : Finset (Fin 11), ∃ C : Finset (Fin 11),
      ConcreteDHCertificate.Cut G S C ∨ ConcreteDHCertificate.Descent G D S :=
    blocks_cover _ hblocks
  refine ⟨fun S => Classical.choose (hall S), ?_⟩
  intro S
  exact Classical.choose_spec (hall S)

#print axioms all_block_certificates_valid
end CodexPaper4.H11SubsetCover
