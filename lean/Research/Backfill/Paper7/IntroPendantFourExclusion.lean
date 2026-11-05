import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment
import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion
import Research.Backfill.Paper7.UnicyclicComponentAttachment
import Research.Backfill.Paper7.FourWalkTuples

/-! Exclude an actual bare C4 joined by one bridge to an arbitrary other
side in the original unicyclic order-21 range. No branch shape is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroPendantFour
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem embedded_two_neighbors
    {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (i a b : W) (hN : ∀ j, H.Adj i j ↔ j = a ∨ j = b)
    (hout : ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x) :
    ∀ x, G.Adj (f i) x ↔ x = f a ∨ x = f b := by
  have hN' : ∀ j, H.Adj i j ↔ f j = f a ∨ f j = f b := by
    intro j
    simpa only [hf.eq_iff] using hN j
  intro x
  constructor
  · intro hx
    have hm : x ∈ Set.range f := by
      by_contra hn
      exact hout x hn hx
    obtain ⟨j, rfl⟩ := hm
    exact (hN' j).mp ((hAdj i j).mpr hx)
  · rintro (rfl | rfl)
    · exact (hAdj i a).mp ((hN a).mpr (Or.inl rfl))
    · exact (hAdj i b).mp ((hN b).mpr (Or.inr rfl))
#print axioms Paper7IntroPendantFour.embedded_two_neighbors

theorem embedded_four_off_vertex_bridges
    {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (hG : IsUnicyclicWithCycle G 4) (f : Fin 4 → V) (hf : Function.Injective f)
    (hAdj : ∀ i j, (cycleGraph 4).Adj i j ↔ G.Adj (f i) (f j))
    (v : V) (hv : v ∉ Set.range f) : ∀ a, G.Adj v a → G.IsBridge s(v, a) := by
  let q : Paper7FourWalks.Quad G := ⟨(f 0, f 1, f 2, f 3),
    (hAdj 0 1).mp (by decide), (hAdj 1 2).mp (by decide),
    (hAdj 2 3).mp (by decide), (hAdj 3 0).mp (by decide)⟩
  let w : G.Walk (f 0) (f 0) := Paper7FourWalks.quadWalk G q
  have hw : w.IsCycle := by
    apply (Paper7FourWalks.quadWalk_isCycle_iff G q).mpr
    exact ⟨fun h => (by decide : (0 : Fin 4) ≠ 2) (hf h),
      fun h => (by decide : (1 : Fin 4) ≠ 3) (hf h)⟩
  have hlen : w.length = 4 := rfl
  have hvw : v ∉ w.support := by
    intro h
    simp only [w, q, Paper7FourWalks.quadWalk, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at h
    apply hv
    rcases h with h | h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
    · exact ⟨0, h.symm⟩
  intro a hva
  exact Paper7UnicyclicAttachment.unicyclic_off_cycle_edge_isBridge
    G 4 hG (f 0) w hw hlen v a hvw hva
#print axioms Paper7IntroPendantFour.embedded_four_off_vertex_bridges

theorem intro21_no_single_bridge_four_side
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsUnicyclicWithCycle G 4) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (S : Set V) (u v : V)
    (hu : u ∈ S) (hv : v ∉ S) (huv : G.Adj u v)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → i = u ∧ j = v)
    (e : G.induce S ≃g cycleGraph 4) : False := by
  let f : Fin 4 → V := fun i => (e.symm i).val
  let k : Fin 4 := e ⟨u, hu⟩
  have hf : Function.Injective f := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hroot : f k = u := by simp [f, k]
  have hAdj : ∀ i j, (cycleGraph 4).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    exact e.symm.map_rel_iff.symm
  have hrange (x : V) : x ∈ S ↔ x ∈ Set.range f := by
    constructor
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
  have hout : ∀ i, i ≠ k → ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x := by
    intro i hi x hx hadj
    have hxS : x ∉ S := fun h => hx ((hrange x).mp h)
    have he := (hcross (f i) (e.symm i).property x hxS hadj).1
    exact hi (hf (he.trans hroot.symm))
  have hn0 : ∀ j : Fin 4, (cycleGraph 4).Adj k j ↔ j = k + 1 ∨ j = k + 3 := by
    exact (by decide +kernel : ∀ (r j : Fin 4),
      (cycleGraph 4).Adj r j ↔ j = r + 1 ∨ j = r + 3) k
  have hn1 : ∀ j : Fin 4, (cycleGraph 4).Adj (k + 1) j ↔ j = k + 2 ∨ j = k := by
    exact (by decide +kernel : ∀ (r j : Fin 4),
      (cycleGraph 4).Adj (r + 1) j ↔ j = r + 2 ∨ j = r) k
  have hn2 : ∀ j : Fin 4, (cycleGraph 4).Adj (k + 2) j ↔ j = k + 1 ∨ j = k + 3 := by
    exact (by decide +kernel : ∀ (r j : Fin 4),
      (cycleGraph 4).Adj (r + 2) j ↔ j = r + 1 ∨ j = r + 3) k
  have hn3 : ∀ j : Fin 4, (cycleGraph 4).Adj (k + 3) j ↔ j = k + 2 ∨ j = k := by
    exact (by decide +kernel : ∀ (r j : Fin 4),
      (cycleGraph 4).Adj (r + 3) j ↔ j = r + 2 ∨ j = r) k
  have hi : k + 1 ≠ k + 3 ∧ k + 2 ≠ k ∧ k + 1 ≠ k ∧ k + 3 ≠ k := by
    exact (by decide +kernel : ∀ r : Fin 4,
      r + 1 ≠ r + 3 ∧ r + 2 ≠ r ∧ r + 1 ≠ r ∧ r + 3 ≠ r) k
  obtain ⟨h13, h20, h10, h30⟩ := hi
  have hurow : ∀ x, G.Adj (f k) x ↔ x = f (k + 1) ∨ x = f (k + 3) ∨ x = v := by
    intro x
    constructor
    · intro hx
      by_cases hxS : x ∈ S
      · let j : Fin 4 := e ⟨x, hxS⟩
        have hfj : f j = x := by simp [f, j]
        have hj : (cycleGraph 4).Adj k j := (hAdj k j).mpr (hfj.symm ▸ hx)
        rcases (hn0 j).mp hj with hj | hj
        · exact Or.inl (hfj.symm.trans (congrArg f hj))
        · exact Or.inr (Or.inl (hfj.symm.trans (congrArg f hj)))
      · exact Or.inr (Or.inr ((hcross (f k) (e.symm k).property x hxS hx).2))
    · rintro (rfl | rfl | rfl)
      · exact (hAdj k (k + 1)).mp ((hn0 _).mpr (Or.inl rfl))
      · exact (hAdj k (k + 3)).mp ((hn0 _).mpr (Or.inr rfl))
      · simpa only [hroot] using huv
  have hfv (i : Fin 4) : f i ≠ v := fun h => hv (h ▸ (e.symm i).property)
  have hbound := Paper7IntroFour.intro21_even_spectrum_abs_le_three
    G 4 hG hI hn (by decide : Even 4)
  obtain ⟨hd, hfour⟩ := pendant_four_local_moments G hI hbound
    (f (k + 2)) (f (k + 1)) (f (k + 3)) (f k) v
    (fun h => h13 (hf h)) (fun h => h20 (hf h)) (hfv _) (hfv _)
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn2 (hout _ h20))
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn1 (hout _ h10))
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn3 (hout _ h30)) hurow
  have hbridge := embedded_four_off_vertex_bridges G hG f hf hAdj v
    (fun h => hv ((hrange v).mpr h))
  have hcard := bridge_vertex_fourth_moment_bound G v hbridge
  rw [hd, hfour] at hcard
  have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
  norm_num at hcard
  linarith
#print axioms Paper7IntroPendantFour.intro21_no_single_bridge_four_side

end Paper7IntroPendantFour
