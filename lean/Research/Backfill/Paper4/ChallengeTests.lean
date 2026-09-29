import Research.Backfill.Paper4.Challenge
import Research.HKOTriameterDH

set_option autoImplicit false

/-!
# Known-answer and triviality tests for `BackfillPaper4.Challenge` (back-fill addendum 1; v2)

Not a proof of any challenge statement. Each custom definition of the challenge is evaluated on
small cases whose answer is stated in the paper or in the papers it cites, with at least one
instance that must come out false. Distances of the small test graphs are identified with
Mathlib's `SimpleGraph.dist` by the released certificate lemma
`HKOTriameter.dist_eq_of_certificate` (imported for that purpose only; the challenge itself
imports only Mathlib).

Sources of the known answers:
* paper §4: "a median graph has no triangle" (`K3`);
* HKO Theorem 1.2 (trees have (Q3) and (Q4)) and HKO Proposition 2.1 (`2 diam ≤ tr ≤ 3 diam`)
  on the path `P3`;
* the released `HKOTriameter.C6_not_median` (the 6-cycle is not median);
* Bandelt–Mulder (viii) needs the "+2": the 4-cycle (distance-hereditary) has the three sums
  `2, 4, 2`; the 5-cycle (a hole, not distance-hereditary, Howorka) violates the four-point
  condition and is not distance-hereditary (induced path of length 3 between vertices at
  distance 2);
* paper §2: the strong reading of (Q4) degenerates for a graph with two vertices (`K2`);
* paper §3: `‖(0,0) − (2,2)‖ = 4`, `d(1,5) = 3`; `med(1,3,2) = 2`;
* edge lists of the paper's graphs (numbers of edges and the structure described in the text).
-/

namespace BackfillPaper4.ChallengeTests

open BackfillPaper4.Challenge SimpleGraph

instance (A B C : ℕ) : Decidable (FP A B C) := by unfold FP; infer_instance
instance (A B C : ℤ) : Decidable (FPZ A B C) := by unfold FPZ; infer_instance
instance (A B C : ℕ) : Decidable (BMvii A B C) := by unfold BMvii; infer_instance
instance (A B C : ℕ) : Decidable (BMviiiExtra A B C) := by unfold BMviiiExtra; infer_instance
instance (l : List ℤ) : Decidable (MonotoneList l) := by unfold MonotoneList; infer_instance

/-! ## 1. `FP`, `FPZ`, (vii), (viii) -/

example : FP 2 4 2 := by decide          -- the 4-cycle: sums 2, 4, 2 (needs the "+2")
example : ¬ FP 2 5 2 := by decide        -- largest exceeds by 3
example : ¬ FP 1 2 3 := by decide        -- no two sums equal
example : FP 5 5 3 := by decide          -- the two larger sums equal
example : ¬ FP 3 3 6 := by decide
example : FPZ (-1) (-1) 1 := by decide
example : ¬ FPZ 0 0 3 := by decide
example : BMvii 3 3 6 ∧ ¬ BMviiiExtra 3 3 6 := by decide
example : BMvii 5 5 3 ∧ BMviiiExtra 5 5 3 ∧ ¬ BMvii 1 2 3 := by decide

/-! ## 2. The grid: `l1`, `med3`, `medPt`, `pos1`, `S1`, `pos2`, `S2`, `gridGraph`, `MonotoneList` -/

example : med3 1 3 2 = 2 ∧ med3 5 (-1) 5 = 5 ∧ med3 0 0 7 = 0 ∧ med3 (-4) 9 2 = 2 := by decide
example : med3 1 3 2 ≠ 3 := by decide
example : medPt ![0, 2] ![2, 0] ![1, 1] = ![1, 1] := by decide +kernel
example : l1 (pos1 3) (pos1 7) = 4 := by decide +kernel      -- (0,0) and (2,2)
example : l1 (pos1 1) (pos1 5) = 3 := by decide +kernel      -- d(1,5) = 3 in the proof of Theorem A
example : l1 ![0, 0] ![0, 0] = 0 ∧ l1 ![0, 0] ![0, 1] = 1 := by decide +kernel
example : l1 (pos2 7) (pos2 1) = 4 := by decide +kernel      -- (-2,0) and (2,0)
example : S1.card = 8 ∧ (![0, 2] : Fin 2 → ℤ) ∉ S1 ∧ (![2, 2] : Fin 2 → ℤ) ∈ S1 := by
  decide +kernel
example : ∀ i, pos1 i ∈ S1 := by decide +kernel
example : S2.card = 8 ∧ (![-2, 0] : Fin 2 → ℤ) ∈ S2 ∧ (![1, 2] : Fin 2 → ℤ) ∉ S2 := by
  decide +kernel
example : ∀ i, pos2 i ∈ S2 := by decide +kernel
example : (gridGraph S1).Adj ⟨![1, 1], by decide +kernel⟩ ⟨![0, 1], by decide +kernel⟩ := by
  show l1 _ _ = 1
  decide +kernel
example : ¬ (gridGraph S1).Adj ⟨![0, 0], by decide +kernel⟩ ⟨![1, 1], by decide +kernel⟩ := by
  show ¬ l1 _ _ = 1
  decide +kernel
example : MonotoneList [0, 1, 1, 2] ∧ MonotoneList [3, 1, 0] ∧ ¬ MonotoneList [0, 2, 1] := by
  decide
example {u : S1} : IsMonotoneWalk (Walk.nil : (gridGraph S1).Walk u u) := by
  intro i
  left
  simp

/-! ## 3. The concrete graphs: edge counts and the structure described in the paper -/

instance : DecidableRel G1.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ g1Edges ∨ (j.val, i.val) ∈ g1Edges))
instance : DecidableRel G2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ g2Edges ∨ (j.val, i.val) ∈ g2Edges))
instance : DecidableRel F1G.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ f1gEdges ∨ (j.val, i.val) ∈ f1gEdges))
instance : DecidableRel F1H.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ f1hEdges ∨ (j.val, i.val) ∈ f1hEdges))
instance : DecidableRel H11.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ h11Edges ∨ (j.val, i.val) ∈ h11Edges))
instance : DecidableRel HKOFig2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ hkoFig2Edges ∨ (j.val, i.val) ∈ hkoFig2Edges))
instance : DecidableRel MOGraph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ moEdges ∨ (j.val, i.val) ∈ moEdges))

example : G1.edgeFinset.card = 10 ∧ G2.edgeFinset.card = 8 ∧ F1G.edgeFinset.card = 7 ∧
    F1H.edgeFinset.card = 11 := by decide +kernel
example : H11.edgeFinset.card = 12 ∧ HKOFig2.edgeFinset.card = 13 ∧
    MOGraph.edgeFinset.card = 14 := by decide +kernel
example : G1.Adj 0 1 ∧ G1.Adj 1 0 ∧ G1.Adj 6 7 ∧ ¬ G1.Adj 0 3 ∧ ¬ G1.Adj 3 7 := by decide
-- G1 = Γ(S1): adjacency is ℓ¹-distance 1
example : ∀ i j, G1.Adj i j ↔ l1 (pos1 i) (pos1 j) = 1 := by decide +kernel
example : ∀ i j, G2.Adj i j ↔ l1 (pos2 i) (pos2 j) = 1 := by decide +kernel
-- H11: K_{2,3} with parts {0,4}, {1,2,3}; pendants 6,7,8,9 at 1,2,3,4; path 0-5-10
example : (∀ a : Fin 11, a = 1 ∨ a = 2 ∨ a = 3 → H11.Adj 0 a ∧ H11.Adj 4 a) ∧ ¬ H11.Adj 0 4 ∧
    H11.Adj 1 6 ∧ H11.Adj 2 7 ∧ H11.Adj 3 8 ∧ H11.Adj 4 9 ∧ H11.Adj 0 5 ∧ H11.Adj 5 10 := by
  decide
-- MO graph: the four squares s-u1-a-u2, s-v1-b-v2, s-v1-x-w1, s-w1-c-w2
example : MOGraph.Adj 0 1 ∧ MOGraph.Adj 1 3 ∧ MOGraph.Adj 3 2 ∧ MOGraph.Adj 2 0 ∧
    MOGraph.Adj 0 4 ∧ MOGraph.Adj 4 6 ∧ MOGraph.Adj 6 5 ∧ MOGraph.Adj 5 0 ∧
    MOGraph.Adj 4 7 ∧ MOGraph.Adj 7 8 ∧ MOGraph.Adj 8 0 ∧
    MOGraph.Adj 8 10 ∧ MOGraph.Adj 10 9 ∧ MOGraph.Adj 9 0 ∧ ¬ MOGraph.Adj 6 7 := by decide
-- HKO Figure 2: x-m1-b-m3-m4-y, x-t1-a-t3-m4, x-b1-c-b3-m4
example : HKOFig2.Adj 0 1 ∧ HKOFig2.Adj 1 2 ∧ HKOFig2.Adj 4 5 ∧ HKOFig2.Adj 6 7 ∧
    HKOFig2.Adj 8 4 ∧ HKOFig2.Adj 11 4 ∧ ¬ HKOFig2.Adj 0 5 := by decide

/-! ## 4. `IsPendant`, `AreTwins` (Mathlib `neighborSet`) -/

example : IsPendant G2 7 := ⟨6, by
  ext w
  simp only [mem_neighborSet, Set.mem_singleton_iff]
  revert w
  decide⟩

example : ¬ IsPendant G2 0 := by
  rintro ⟨u, hu⟩
  have h2 : (2 : Fin 8) ∈ G2.neighborSet 0 := by rw [mem_neighborSet]; decide
  have h3 : (3 : Fin 8) ∈ G2.neighborSet 0 := by rw [mem_neighborSet]; decide
  rw [hu, Set.mem_singleton_iff] at h2 h3
  exact absurd (h2.trans h3.symm) (by decide)

-- HKO Figure 3, graph G: a = 2 and b = 3 have the same neighbours {m, x} (false twins)
example : AreTwins F1G 2 3 := ⟨by decide, by
  ext w
  simp only [Set.mem_sdiff, mem_neighborSet, Set.mem_singleton_iff]
  revert w
  decide⟩

-- in G2, the vertices 2 and 3 are not twins (1 ~ 2 but 1 ≁ 3)
example : ¬ AreTwins G2 2 3 := by
  rintro ⟨-, h⟩
  have h1 : (1 : Fin 8) ∈ G2.neighborSet 2 \ {3} := by
    simp only [Set.mem_sdiff, mem_neighborSet, Set.mem_singleton_iff]
    decide
  rw [h] at h1
  simp only [Set.mem_sdiff, mem_neighborSet, Set.mem_singleton_iff] at h1
  revert h1
  decide

-- why `BandeltMulder_extension` assumes connectedness: two isolated vertices are twins
example : AreTwins (⊥ : SimpleGraph (Fin 2)) 0 1 ∧ ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by
  refine ⟨⟨by decide, by simp⟩, fun h => ?_⟩
  exact absurd (reachable_bot.mp (h.preconnected 0 1)) (by decide)

/-! ## 5. Metric definitions on small graphs -/

/-- The path `0 - 1 - 2`. -/
def p3Edges : List (ℕ × ℕ) := [(0, 1), (1, 2)]

def P3 : SimpleGraph (Fin 3) where
  Adj i j := (i.val, j.val) ∈ p3Edges ∨ (j.val, i.val) ∈ p3Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel P3.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ p3Edges ∨ (j.val, i.val) ∈ p3Edges))

def DP3 (i j : Fin 3) : ℕ := if i.val ≤ j.val then j.val - i.val else i.val - j.val

theorem P3_dist : ∀ x y, P3.dist x y = DP3 x y :=
  HKOTriameter.dist_eq_of_certificate P3 DP3 (by decide) (by decide) (by decide) (by decide)

theorem P3_connected : P3.Connected :=
  HKOTriameter.connected_of_dist P3 fun x y hxy => by
    rw [P3_dist]
    revert x y
    decide

theorem P3_diam : P3.diam = 2 :=
  HKOTriameter.diam_eq_of_bounds P3 P3_connected 2
    (fun u v => by rw [P3_dist]; revert u v; decide) 0 2 (by rw [P3_dist]; decide)

theorem P3_triameter : triameter P3 = 4 := by
  have hle : ∀ a b c : Fin 3, DP3 a b + DP3 a c + DP3 b c ≤ 4 := by decide
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    simp only [triDist, P3_dist]
    exact hle a b c
  · have h : triDist P3 0 1 2 = 4 := by simp only [triDist, P3_dist]; decide
    calc (4 : ℕ) = triDist P3 0 1 2 := h.symm
      _ ≤ triameter P3 :=
        Finset.le_sup (f := fun t : Fin 3 × Fin 3 × Fin 3 => triDist P3 t.1 t.2.1 t.2.2)
          (Finset.mem_univ ((0, 1, 2) : Fin 3 × Fin 3 × Fin 3))

-- a tree is median; HKO Proposition 2.1: tr = 4 = 2 diam here
example : IsMedian P3 ∧ triameter P3 = 2 * P3.diam := by
  refine ⟨⟨P3_connected, ?_⟩, by rw [P3_triameter, P3_diam]⟩
  have key : ∀ u v w : Fin 3, ∃ x,
      (DP3 u x + DP3 x v = DP3 u v ∧ DP3 u x + DP3 x w = DP3 u w ∧
        DP3 v x + DP3 x w = DP3 v w) ∧
      ∀ y, (DP3 u y + DP3 y v = DP3 u v ∧ DP3 u y + DP3 y w = DP3 u w ∧
        DP3 v y + DP3 y w = DP3 v w) → y = x := by decide
  intro u v w
  simp only [InInterval, P3_dist]
  exact key u v w

-- the ends are peripheral, the middle vertex is not
example : IsPeripheral P3 0 ∧ ¬ IsPeripheral P3 1 ∧ IsPeripheralPair P3 2 ∧
    ¬ IsPeripheralPair P3 1 := by
  refine ⟨(HKOTriameter.isPeripheral_iff_isPeripheralPair P3 P3_connected 0).mpr
      ⟨2, by show P3.dist 0 2 = P3.diam; rw [P3_dist, P3_diam]; decide⟩,
    HKOTriameter.not_isPeripheral_of_lt P3 P3_connected 1
      (fun v => by rw [P3_dist, P3_diam]; revert v; decide),
    ⟨0, by show P3.dist 2 0 = P3.diam; rw [P3_dist, P3_diam]; decide⟩, ?_⟩
  rintro ⟨v, hv⟩
  have hv' : P3.dist 1 v = P3.diam := hv
  clear hv
  rw [P3_dist, P3_diam] at hv'
  revert hv'
  revert v
  decide

-- HKO Theorem 1.2 (trees): (Q3) and (Q4) hold; also (Q3'), (Q4') and the strong reading
example : Question3 P3 ∧ Question4 P3 ∧ Question4Strong P3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c h
    have h' : DP3 a b + DP3 a c + DP3 b c = 4 := by
      have := h; simp only [IsTriametral, P3_triameter, triDist, P3_dist] at this; exact this
    simp only [IsDiametral, P3_dist, P3_diam]
    clear h
    revert h'
    revert a b c
    decide
  · intro x y h
    have h' : DP3 x y = 2 := by
      have := h; simp only [IsDiametral, P3_dist, P3_diam] at this; exact this
    simp only [IsTriametral, P3_triameter, triDist, P3_dist]
    clear h
    revert h'
    revert x y
    decide
  · intro x y h
    have h' : DP3 x y = 2 := by
      have := h; simp only [IsDiametral, P3_dist, P3_diam] at this; exact this
    simp only [IsTriametral, P3_triameter, triDist, P3_dist]
    clear h
    revert h'
    revert x y
    decide

/-- The triangle. -/
def k3Edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2)]

def K3 : SimpleGraph (Fin 3) where
  Adj i j := (i.val, j.val) ∈ k3Edges ∨ (j.val, i.val) ∈ k3Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel K3.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ k3Edges ∨ (j.val, i.val) ∈ k3Edges))

def DK3 (i j : Fin 3) : ℕ := if i = j then 0 else 1

theorem K3_dist : ∀ x y, K3.dist x y = DK3 x y :=
  HKOTriameter.dist_eq_of_certificate K3 DK3 (by decide) (by decide) (by decide) (by decide)

-- paper §4: a median graph has no triangle
example : ¬ IsMedian K3 := by
  rintro ⟨_, h⟩
  obtain ⟨x, hx, -⟩ := h 0 1 2
  simp only [InInterval, K3_dist] at hx
  revert hx
  revert x
  decide

-- the released 6-cycle is not median (definitional link to the released module)
example : ¬ IsMedian HKOTriameter.C6 := HKOTriameter.C6_not_median

/-- The 4-cycle `0-1-2-3-0` (distance-hereditary). -/
def c4Edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (0, 3)]

def C4 : SimpleGraph (Fin 4) where
  Adj i j := (i.val, j.val) ∈ c4Edges ∨ (j.val, i.val) ∈ c4Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel C4.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ c4Edges ∨ (j.val, i.val) ∈ c4Edges))

def DC4 (i j : Fin 4) : ℕ := min ((i.val + 4 - j.val) % 4) ((j.val + 4 - i.val) % 4)

theorem C4_dist : ∀ x y, C4.dist x y = DC4 x y :=
  HKOTriameter.dist_eq_of_certificate C4 DC4 (by decide) (by decide) (by decide) (by decide)

example : FourPointBM C4 := by
  intro u v w x
  simp only [C4_dist]
  revert u v w x
  decide

-- the sums of the quadruple 0,1,2,3 are 2, 4, 2: FP holds only thanks to "+2"
example : C4.dist 0 1 + C4.dist 2 3 = 2 ∧ C4.dist 0 2 + C4.dist 1 3 = 4 ∧
    C4.dist 0 3 + C4.dist 1 2 = 2 := by
  simp only [C4_dist]
  decide

/-- The 5-cycle `0-1-2-3-4-0` (a hole: not distance-hereditary). -/
def c5Edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]

def C5 : SimpleGraph (Fin 5) where
  Adj i j := (i.val, j.val) ∈ c5Edges ∨ (j.val, i.val) ∈ c5Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel C5.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ c5Edges ∨ (j.val, i.val) ∈ c5Edges))

def DC5 (i j : Fin 5) : ℕ := min ((i.val + 5 - j.val) % 5) ((j.val + 5 - i.val) % 5)

theorem C5_dist : ∀ x y, C5.dist x y = DC5 x y :=
  HKOTriameter.dist_eq_of_certificate C5 DC5 (by decide) (by decide) (by decide +kernel)
    (by decide +kernel)

example : ¬ FourPointBM C5 := by
  intro h
  have := h 0 1 2 3
  simp only [C5_dist] at this
  revert this
  decide

/-- The induced path `0-1-2-3` inside `C5`. -/
def s5 : Set (Fin 5) := {x | x.val < 4}

instance : DecidablePred (· ∈ s5) := fun x => inferInstanceAs (Decidable (x.val < 4))
instance : Nonempty s5 := ⟨⟨0, by decide⟩⟩
instance : DecidableRel (C5.induce s5).Adj := fun a b =>
  inferInstanceAs (Decidable (C5.Adj a.1 b.1))

def Ds5 (a b : s5) : ℕ := if a.1.val ≤ b.1.val then b.1.val - a.1.val else a.1.val - b.1.val

theorem s5_dist : ∀ a b, (C5.induce s5).dist a b = Ds5 a b :=
  HKOTriameter.dist_eq_of_certificate (C5.induce s5) Ds5 (by decide) (by decide) (by decide)
    (by decide)

example : ¬ IsDistanceHereditary C5 := by
  rintro ⟨-, h⟩
  have hc : (C5.induce s5).Connected :=
    HKOTriameter.connected_of_dist _ fun x y hxy => by
      rw [s5_dist]
      revert x y
      decide
  have := h s5 hc ⟨0, by decide⟩ ⟨3, by decide⟩
  rw [s5_dist, C5_dist] at this
  revert this
  decide

/-- `K2`: the strong reading of (Q4) fails for two vertices (paper §2). -/
def DK2 (i j : Fin 2) : ℕ := if i = j then 0 else 1

theorem K2_dist : ∀ x y, (⊤ : SimpleGraph (Fin 2)).dist x y = DK2 x y :=
  HKOTriameter.dist_eq_of_certificate ⊤ DK2 (by decide) (by decide) (by decide) (by decide)

theorem K2_diam : (⊤ : SimpleGraph (Fin 2)).diam = 1 :=
  HKOTriameter.diam_eq_of_bounds ⊤ connected_top 1
    (fun u v => by rw [K2_dist]; revert u v; decide) 0 1 (by rw [K2_dist]; decide)

example : Question4 (⊤ : SimpleGraph (Fin 2)) ∧ ¬ Question4Strong (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨fun x y hd => ⟨x, ?_⟩, fun h => ?_⟩
  · have hxy : DK2 x y = 1 := by
      have e : (⊤ : SimpleGraph (Fin 2)).dist x y = (⊤ : SimpleGraph (Fin 2)).diam := hd
      rw [K2_dist, K2_diam] at e
      exact e
    clear hd
    apply le_antisymm
    · exact Finset.le_sup (f := fun t : Fin 2 × Fin 2 × Fin 2 =>
        triDist (⊤ : SimpleGraph (Fin 2)) t.1 t.2.1 t.2.2) (Finset.mem_univ (x, y, x))
    · apply Finset.sup_le
      rintro ⟨a, b, c⟩ -
      simp only [triDist, K2_dist]
      revert hxy
      revert a b c x y
      decide
  · obtain ⟨z, h0, h1, -⟩ := h 0 1 (by
      show (⊤ : SimpleGraph (Fin 2)).dist 0 1 = _
      rw [K2_dist, K2_diam]
      decide)
    revert h0 h1
    revert z
    decide

/-! ## 6. Triviality tests (degenerate objects) -/

-- the empty graph is neither median nor distance-hereditary (not connected), so the class
-- statements are not vacuous at `n = 0`
example : ¬ IsMedian (⊥ : SimpleGraph (Fin 0)) := fun h => h.1.nonempty.elim fun x => x.elim0
example : ¬ IsDistanceHereditary (⊥ : SimpleGraph (Fin 0)) := fun h =>
  h.1.nonempty.elim fun x => x.elim0
-- the empty graph trivially satisfies the four-point condition: `TheoremC_FP` and
-- `Proposition3` therefore also assume connectedness
example : FourPointBM (⊥ : SimpleGraph (Fin 0)) := fun u => u.elim0
-- the one-vertex graph is distance-hereditary
example : IsDistanceHereditary (⊤ : SimpleGraph (Fin 1)) := by
  refine ⟨connected_top, fun s _ u v => ?_⟩
  have huv : u = v := Subtype.ext (Subsingleton.elim _ _)
  subst huv
  simp
-- Lemma 1 needs `S.Nonempty`: for `S = ∅`, (a) and (b) hold vacuously but `Γ(∅)` is not median
example : GridA (∅ : Finset (Fin 1 → ℤ)) ∧ GridB (∅ : Finset (Fin 1 → ℤ)) ∧
    ¬ IsMedian (gridGraph (∅ : Finset (Fin 1 → ℤ))) := by
  refine ⟨fun u => absurd u.2 (Finset.notMem_empty _), fun u _ _ hu => absurd hu
    (Finset.notMem_empty _), fun h => h.1.nonempty.elim fun u => absurd u.2 (Finset.notMem_empty _)⟩

/-! ## 7. Tests added with challenge v2 (the review's list, `REVIEW-CHALLENGE.md` §5) -/

/-! ### Definitional links to the released theorems: `Question3'`, `Question3'Pair`, `Question3`,
`Question4`, `Question4'` and the five problem claims agree with the released definitions -/

example : ¬ Question3' G1 := HKOTriameter.not_question3'_G1
example : ¬ Question3'Pair G1 := HKOTriameter.not_question3'Pair_G1
example : ¬ Question3 G1 := HKOTriameter.not_question3_G1
example : ¬ Question4 G2 := HKOTriameter.not_question4_G2
example : ¬ Question4' G2 := HKOTriameter.not_question4'_G2
example : ¬ Problem1Claim := HKOTriameter.not_problem1Claim
example : ¬ Problem1ClaimPair := HKOTriameter.not_problem1ClaimPair
example : ¬ Problem2Claim := HKOTriameter.not_problem2Claim
example : ¬ Problem2ClaimWeak := HKOTriameter.not_problem2ClaimWeak
example : Problem3ClaimFP := HKOTriameter.problem3ClaimFP

/-! ### Positive instances on the path `P3` (a tree: HKO Theorem 1.2) -/

theorem P3_per0 : IsPeripheral P3 0 :=
  (HKOTriameter.isPeripheral_iff_isPeripheralPair P3 P3_connected 0).mpr
    ⟨2, by show P3.dist 0 2 = P3.diam; rw [P3_dist, P3_diam]; decide⟩

theorem P3_per2 : IsPeripheral P3 2 :=
  (HKOTriameter.isPeripheral_iff_isPeripheralPair P3 P3_connected 2).mpr
    ⟨0, by show P3.dist 2 0 = P3.diam; rw [P3_dist, P3_diam]; decide⟩

theorem P3_Q3' : Question3' P3 := by
  intro a b c h
  have h' : DP3 a b + DP3 a c + DP3 b c = 4 := by
    have := h; simp only [IsTriametral, P3_triameter, triDist, P3_dist] at this; exact this
  clear h
  have key : ∀ a b c : Fin 3, DP3 a b + DP3 a c + DP3 b c = 4 →
      (a = 0 ∨ a = 2) ∨ (b = 0 ∨ b = 2) ∨ (c = 0 ∨ c = 2) := by decide
  rcases key a b c h' with (rfl | rfl) | (rfl | rfl) | (rfl | rfl)
  · exact Or.inl P3_per0
  · exact Or.inl P3_per2
  · exact Or.inr (Or.inl P3_per0)
  · exact Or.inr (Or.inl P3_per2)
  · exact Or.inr (Or.inr P3_per0)
  · exact Or.inr (Or.inr P3_per2)

example : Question3'Distinct P3 := fun a b c _ _ _ h => P3_Q3' a b c h

example : Question3Distinct P3 := by
  intro a b c _ _ _ h
  have h' : DP3 a b + DP3 a c + DP3 b c = 4 := by
    have := h; simp only [IsTriametral, P3_triameter, triDist, P3_dist] at this; exact this
  clear h
  simp only [IsDiametral, P3_dist, P3_diam]
  revert h'
  revert a b c
  decide

example : Question4' P3 := by
  intro x _
  have key : ∀ x : Fin 3, ∃ y z : Fin 3, DP3 x y + DP3 x z + DP3 y z = 4 := by decide
  obtain ⟨y, z, hyz⟩ := key x
  exact ⟨y, z, by simp only [IsTriametral, P3_triameter, triDist, P3_dist]; exact hyz⟩

example : Question4'Strong P3 := by
  intro x _
  have key : ∀ x : Fin 3, ∃ y z : Fin 3, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      DP3 x y + DP3 x z + DP3 y z = 4 := by decide
  obtain ⟨y, z, h1, h2, h3, hyz⟩ := key x
  exact ⟨y, z, h1, h2, h3, by simp only [IsTriametral, P3_triameter, triDist, P3_dist]; exact hyz⟩

/-! ### Negative instances of the strong and distinct variants -/

-- `K2`: both vertices are peripheral, but there is no triple of distinct vertices
example : ¬ Question4'Strong (⊤ : SimpleGraph (Fin 2)) := by
  intro h
  have hp : IsPeripheral (⊤ : SimpleGraph (Fin 2)) 0 :=
    (HKOTriameter.isPeripheral_iff_isPeripheralPair ⊤ connected_top 0).mpr
      ⟨1, by show (⊤ : SimpleGraph (Fin 2)).dist 0 1 = _; rw [K2_dist, K2_diam]; decide⟩
  obtain ⟨y, z, h1, h2, h3, -⟩ := h 0 hp
  revert h1 h2 h3
  revert y z
  decide

-- `G1`: the triple `1, 5, 6` of distinct vertices is triametral, without a diametral pair and
-- without a peripheral vertex
example : ¬ Question3Distinct G1 := by
  intro h
  have e : G1 = HKOTriameter.G1 := rfl
  have := h 1 5 6 (by decide) (by decide) (by decide) HKOTriameter.G1_triametral_156
  simp only [IsDiametral, e, HKOTriameter.G1_dist, HKOTriameter.G1_diam] at this
  revert this
  decide

example : ¬ Question3'Distinct G1 := by
  intro h
  obtain ⟨h1, h5, h6⟩ := HKOTriameter.G1_not_peripheral_156
  rcases h 1 5 6 (by decide) (by decide) (by decide) HKOTriameter.G1_triametral_156 with
    h' | h' | h'
  · exact h1 h'
  · exact h5 h'
  · exact h6 h'

-- a false instance of `IsTriametral` and of `medPt`
example : ¬ IsTriametral P3 0 0 1 := by
  rw [IsTriametral, P3_triameter]
  unfold triDist
  simp only [P3_dist]
  decide

example : medPt ![0, 2] ![2, 0] ![1, 1] ≠ ![0, 0] := by decide +kernel

/-! ### A distance-hereditary graph with more than one vertex: every complete graph -/

theorem top_isDH (n : ℕ) : IsDistanceHereditary (⊤ : SimpleGraph (Fin (n + 1))) := by
  refine ⟨connected_top, fun s _ u v => ?_⟩
  have e : (⊤ : SimpleGraph (Fin (n + 1))).induce s = ⊤ := induce_top s
  rw [e, dist_top, dist_top]
  by_cases h : u = v
  · subst h
    simp
  · have h' : (u : Fin (n + 1)) ≠ v := fun h'' => h (Subtype.ext h'')
    simp [h, h']

example : IsDistanceHereditary (⊤ : SimpleGraph (Fin 2)) := top_isDH 1
example : IsDistanceHereditary (⊤ : SimpleGraph (Fin 3)) := top_isDH 2

/-! ### Non-vacuous tests of `GridA`, `GridB`, `IsMonotoneWalk` -/

/-- Three collinear points `(0,0), (1,0), (2,0)`. -/
def Spath : Finset (Fin 2 → ℤ) := {![0, 0], ![1, 0], ![2, 0]}

/-- Two points at `ℓ¹`-distance `2`: `Γ` has no edge. -/
def Sdiag : Finset (Fin 2 → ℤ) := {![0, 0], ![1, 1]}

/-- `(0,1), (1,0), (1,2)`: their coordinatewise median `(1,1)` is missing. -/
def Sbad : Finset (Fin 2 → ℤ) := {![0, 1], ![1, 0], ![1, 2]}

instance (S : Finset (Fin 2 → ℤ)) : DecidableRel (gridGraph S).Adj := fun u v =>
  inferInstanceAs (Decidable (l1 (u : Fin 2 → ℤ) v = 1))

-- (a) holds for the three collinear points (distances 1, 1, 2)
theorem Spath_gridA : GridA Spath := fun u v =>
  HKOTriameter.dist_eq_of_certificate (gridGraph Spath) (fun a b => l1 (a : Fin 2 → ℤ) b)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) u v

-- (b) holds for them
theorem Spath_gridB : GridB Spath := by
  intro u v w hu hv hw
  have key : ∀ u ∈ Spath, ∀ v ∈ Spath, ∀ w ∈ Spath, medPt u v w ∈ Spath := by decide +kernel
  exact key u hu v hv w hw

-- (a) fails for two points at distance 2 (no edge, graph distance 0)
example : ¬ GridA Sdiag := by
  intro h
  have hbot : gridGraph Sdiag = ⊥ := by
    ext a b
    simp only [bot_adj, iff_false]
    revert a b
    decide +kernel
  have := h ⟨![0, 0], by decide +kernel⟩ ⟨![1, 1], by decide +kernel⟩
  rw [hbot, dist_bot] at this
  revert this
  decide +kernel

-- (b) fails when the median point is missing
example : ¬ GridB Sbad := by
  intro h
  have := h ![0, 1] ![1, 0] ![1, 2] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

def q0 : Spath := ⟨![0, 0], by decide +kernel⟩
def q1 : Spath := ⟨![1, 0], by decide +kernel⟩
def q2 : Spath := ⟨![2, 0], by decide +kernel⟩
theorem q01 : (gridGraph Spath).Adj q0 q1 := by show l1 _ _ = 1; decide +kernel
theorem q12 : (gridGraph Spath).Adj q1 q2 := by show l1 _ _ = 1; decide +kernel
theorem q10 : (gridGraph Spath).Adj q1 q0 := by show l1 _ _ = 1; decide +kernel

-- `(0,0) → (1,0) → (2,0)` is a monotone lattice path (coordinates `0,1,2` and `0,0,0`)
example : IsMonotoneWalk (Walk.cons q01 (Walk.cons q12 Walk.nil)) := by
  intro i
  revert i
  decide +kernel

-- `(0,0) → (1,0) → (0,0)` is not (the first coordinate runs `0, 1, 0`)
example : ¬ IsMonotoneWalk (Walk.cons q01 (Walk.cons q10 Walk.nil)) := by
  intro h
  have := h 0
  revert this
  decide +kernel

end BackfillPaper4.ChallengeTests
