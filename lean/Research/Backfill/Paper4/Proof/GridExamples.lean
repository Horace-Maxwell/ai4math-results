import Research.Backfill.Paper4.Challenge
import Research.HKOTriameter

/-! Full frozen grid descriptions of G1 and G2, using their actual coordinate sets.
The graph metric is transported by an explicit graph isomorphism.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace GridExamples

theorem iso_dist_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hc : G.Connected) (u v : V) : H.dist (e u) (e v) = G.dist u v := by
  have hcH : H.Connected := e.connected_iff.mp hc
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
    calc
      H.dist (e u) (e v) ≤ (p.map e.toHom).length := SimpleGraph.dist_le _
      _ = p.length := SimpleGraph.Walk.length_map _ _
      _ = G.dist u v := hp
  · obtain ⟨p, hp⟩ := hcH.exists_walk_length_eq_dist (e u) (e v)
    have hle := SimpleGraph.dist_le (p.map e.symm.toHom)
    have hle' : G.dist u v ≤ p.length := by
      change G.dist (e.symm (e u)) (e.symm (e v)) ≤
        (p.map e.symm.toHom).length at hle
      simpa only [SimpleGraph.Walk.length_map, RelIso.symm_apply_apply] using hle
    exact hle'.trans_eq hp

noncomputable def positionsEquiv {n k : ℕ} (S : Finset (Fin k → ℤ))
    (pos : Fin n → (Fin k → ℤ)) (hinj : Function.Injective pos)
    (hmem : ∀ s, s ∈ S ↔ ∃ i, pos i = s) : Fin n ≃ S :=
  Equiv.ofBijective (fun i => (⟨pos i, (hmem (pos i)).mpr ⟨i, rfl⟩⟩ : S))
    ⟨fun i j h => hinj (congrArg Subtype.val h), fun s => by
      obtain ⟨i, hi⟩ := (hmem s.val).mp s.property
      exact ⟨i, Subtype.ext hi⟩⟩

noncomputable def positionsIso {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin k → ℤ)) (pos : Fin n → (Fin k → ℤ))
    (hinj : Function.Injective pos) (hmem : ∀ s, s ∈ S ↔ ∃ i, pos i = s)
    (hadj : ∀ i j, G.Adj i j ↔ Challenge.l1 (pos i) (pos j) = 1) :
    G ≃g Challenge.gridGraph S where
  toEquiv := positionsEquiv S pos hinj hmem
  map_rel_iff' := by
    intro i j
    change Challenge.l1 (pos i) (pos j) = 1 ↔ G.Adj i j
    exact (hadj i j).symm

theorem gridA_of_positions {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin k → ℤ)) (pos : Fin n → (Fin k → ℤ))
    (hinj : Function.Injective pos) (hmem : ∀ s, s ∈ S ↔ ∃ i, pos i = s)
    (hadj : ∀ i j, G.Adj i j ↔ Challenge.l1 (pos i) (pos j) = 1)
    (hc : G.Connected) (hd : ∀ i j, G.dist i j = Challenge.l1 (pos i) (pos j)) :
    Challenge.GridA S := by
  let e := positionsIso G S pos hinj hmem hadj
  intro u v
  obtain ⟨i, rfl⟩ := e.toEquiv.surjective u
  obtain ⟨j, rfl⟩ := e.toEquiv.surjective v
  change (Challenge.gridGraph S).dist (e i) (e j) = Challenge.l1 (pos i) (pos j)
  exact (iso_dist_eq e hc i j).trans (hd i j)

theorem gridB_of_positions {n k : ℕ} (S : Finset (Fin k → ℤ))
    (pos : Fin n → (Fin k → ℤ)) (hmem : ∀ s, s ∈ S ↔ ∃ i, pos i = s)
    (hclosed : ∀ i j l, ∃ m, pos m = Challenge.medPt (pos i) (pos j) (pos l)) :
    Challenge.GridB S := by
  intro u v w hu hv hw
  obtain ⟨i, rfl⟩ := (hmem u).mp hu
  obtain ⟨j, rfl⟩ := (hmem v).mp hv
  obtain ⟨l, rfl⟩ := (hmem w).mp hw
  exact (hmem _).mpr (hclosed i j l)

local instance : DecidableRel Challenge.G1.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.g1Edges ∨
    (j.val, i.val) ∈ Challenge.g1Edges))
local instance : DecidableRel Challenge.G2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.g2Edges ∨
    (j.val, i.val) ∈ Challenge.g2Edges))

theorem S1_eq_image : Challenge.S1 = Finset.univ.image Challenge.pos1 := by decide +kernel
theorem S2_eq_image : Challenge.S2 = Finset.univ.image Challenge.pos2 := by decide +kernel

theorem S1_mem_iff (s : Fin 2 → ℤ) : s ∈ Challenge.S1 ↔ ∃ i, Challenge.pos1 i = s := by
  rw [S1_eq_image]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem S2_mem_iff (s : Fin 2 → ℤ) : s ∈ Challenge.S2 ↔ ∃ i, Challenge.pos2 i = s := by
  rw [S2_eq_image]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem pos1_injective : Function.Injective Challenge.pos1 := by decide +kernel
theorem pos2_injective : Function.Injective Challenge.pos2 := by decide +kernel

theorem pos1_adj : ∀ i j, Challenge.G1.Adj i j ↔
    Challenge.l1 (Challenge.pos1 i) (Challenge.pos1 j) = 1 := by decide +kernel
theorem pos2_adj : ∀ i j, Challenge.G2.Adj i j ↔
    Challenge.l1 (Challenge.pos2 i) (Challenge.pos2 j) = 1 := by decide +kernel

theorem pos1_dist : ∀ i j, Challenge.G1.dist i j =
    Challenge.l1 (Challenge.pos1 i) (Challenge.pos1 j) := by
  have htable : ∀ i j : Fin 8, HKOTriameter.D1 i j =
      Challenge.l1 (Challenge.pos1 i) (Challenge.pos1 j) := by decide +kernel
  intro i j
  have hd : Challenge.G1.dist i j = HKOTriameter.D1 i j := HKOTriameter.G1_dist i j
  exact hd.trans (htable i j)

theorem pos2_dist : ∀ i j, Challenge.G2.dist i j =
    Challenge.l1 (Challenge.pos2 i) (Challenge.pos2 j) := by
  have htable : ∀ i j : Fin 8, HKOTriameter.D2 i j =
      Challenge.l1 (Challenge.pos2 i) (Challenge.pos2 j) := by decide +kernel
  intro i j
  have hd : Challenge.G2.dist i j = HKOTriameter.D2 i j := HKOTriameter.G2_dist i j
  exact hd.trans (htable i j)

theorem pos1_median_closed : ∀ i j l : Fin 8, ∃ m : Fin 8,
    Challenge.pos1 m = Challenge.medPt (Challenge.pos1 i) (Challenge.pos1 j) (Challenge.pos1 l) := by
  decide +kernel

theorem pos2_median_closed : ∀ i j l : Fin 8, ∃ m : Fin 8,
    Challenge.pos2 m = Challenge.medPt (Challenge.pos2 i) (Challenge.pos2 j) (Challenge.pos2 l) := by
  decide +kernel

end GridExamples

theorem check_TheoremA_grid : Challenge.TheoremA_grid :=
  ⟨GridExamples.pos1_injective, GridExamples.S1_mem_iff, GridExamples.pos1_adj,
    ⟨GridExamples.positionsIso Challenge.G1 Challenge.S1 Challenge.pos1
      GridExamples.pos1_injective GridExamples.S1_mem_iff GridExamples.pos1_adj⟩,
    GridExamples.gridA_of_positions Challenge.G1 Challenge.S1 Challenge.pos1
      GridExamples.pos1_injective GridExamples.S1_mem_iff GridExamples.pos1_adj
      HKOTriameter.G1_connected GridExamples.pos1_dist,
    GridExamples.gridB_of_positions Challenge.S1 Challenge.pos1
      GridExamples.S1_mem_iff GridExamples.pos1_median_closed⟩

theorem check_TheoremB_grid : Challenge.TheoremB_grid :=
  ⟨GridExamples.pos2_injective, GridExamples.S2_mem_iff, GridExamples.pos2_adj,
    ⟨GridExamples.positionsIso Challenge.G2 Challenge.S2 Challenge.pos2
      GridExamples.pos2_injective GridExamples.S2_mem_iff GridExamples.pos2_adj⟩,
    GridExamples.gridA_of_positions Challenge.G2 Challenge.S2 Challenge.pos2
      GridExamples.pos2_injective GridExamples.S2_mem_iff GridExamples.pos2_adj
      HKOTriameter.G2_connected GridExamples.pos2_dist,
    GridExamples.gridB_of_positions Challenge.S2 Challenge.pos2
      GridExamples.S2_mem_iff GridExamples.pos2_median_closed⟩

#print axioms check_TheoremA_grid
#print axioms check_TheoremB_grid
end CodexPaper4
