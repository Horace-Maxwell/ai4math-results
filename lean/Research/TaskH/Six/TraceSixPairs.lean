import Research.TaskH.Six.TraceSixPaths

/-!
Ordered pairs of different simple three-edge paths with the same ordered
endpoints.  The six-word convention is `(u,a,b,v,d,c)`, corresponding to
`u-a-b-v` and `u-c-d-v`.  No disjointness is imposed until it is proved.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def IsTracePathPair (G : SimpleGraph V) (f : Fin 6 → V) : Prop :=
  IsTraceThreePath G (f 0) (f 3) (f 1, f 2) ∧
    IsTraceThreePath G (f 0) (f 3) (f 5, f 4) ∧
      (f 1, f 2) ≠ (f 5, f 4)

def tracePairFromData (u v : V) (p : (V × V) × (V × V)) : Fin 6 → V :=
  ![u, p.1.1, p.1.2, v, p.2.2, p.2.1]

theorem tracePairFromData_isPair (u v : V) (p : (V × V) × (V × V))
    (h1 : IsTraceThreePath G u v p.1) (h2 : IsTraceThreePath G u v p.2)
    (hne : p.1 ≠ p.2) : IsTracePathPair G (tracePairFromData u v p) := by
  exact ⟨h1, h2, hne⟩

theorem tracePathPair_injective_iff (f : Fin 6 → V)
    (hf : IsTracePathPair G f) :
    Function.Injective f ↔
      f 1 ≠ f 5 ∧ f 2 ≠ f 4 ∧ f 1 ≠ f 4 ∧ f 2 ≠ f 5 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide : (1 : Fin 6) ≠ 5),
      h.ne (by decide : (2 : Fin 6) ≠ 4),
      h.ne (by decide : (1 : Fin 6) ≠ 4),
      h.ne (by decide : (2 : Fin 6) ≠ 5)⟩
  · rintro ⟨h15, h24, h14, h25⟩
    rcases (traceThreeWord_injective_iff (f 0) (f 1) (f 2) (f 3)).mp hf.1.1 with
      ⟨h01, h02, h03, h12, h13, h23⟩
    rcases (traceThreeWord_injective_iff (f 0) (f 5) (f 4) (f 3)).mp hf.2.1.1 with
      ⟨h05, h04, _, h54, h53, h43⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem tracePathPair_isHexagon (f : Fin 6 → V)
    (hf : IsTracePathPair G f) (hinj : Function.Injective f) :
    IsHexagon G f :=
  ⟨hinj, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2,
    hf.2.1.2.2.2.symm, hf.2.1.2.2.1.symm, hf.2.1.2.1.symm⟩

theorem isHexagon_isTracePathPair (f : Fin 6 → V) (hf : IsHexagon G f) :
    IsTracePathPair G f := by
  have hn : ∀ {i j : Fin 6}, i ≠ j → f i ≠ f j := hf.1.ne
  refine ⟨⟨(traceThreeWord_injective_iff _ _ _ _).mpr ?_,
    hf.2.1, hf.2.2.1, hf.2.2.2.1⟩,
    ⟨(traceThreeWord_injective_iff _ _ _ _).mpr ?_,
      hf.2.2.2.2.2.2.symm, hf.2.2.2.2.2.1.symm, hf.2.2.2.2.1.symm⟩, ?_⟩
  · exact ⟨hn (by decide : (0 : Fin 6) ≠ 1), hn (by decide : (0 : Fin 6) ≠ 2),
      hn (by decide : (0 : Fin 6) ≠ 3), hn (by decide : (1 : Fin 6) ≠ 2),
      hn (by decide : (1 : Fin 6) ≠ 3), hn (by decide : (2 : Fin 6) ≠ 3)⟩
  · exact ⟨hn (by decide : (0 : Fin 6) ≠ 5), hn (by decide : (0 : Fin 6) ≠ 4),
      hn (by decide : (0 : Fin 6) ≠ 3), hn (by decide : (5 : Fin 6) ≠ 4),
      hn (by decide : (5 : Fin 6) ≠ 3), hn (by decide : (4 : Fin 6) ≠ 3)⟩
  · intro he
    exact hn (by decide : (1 : Fin 6) ≠ 5) (congrArg Prod.fst he)

theorem isHexagon_iff_injective_tracePathPair (f : Fin 6 → V) :
    IsHexagon G f ↔ IsTracePathPair G f ∧ Function.Injective f :=
  ⟨fun h => ⟨isHexagon_isTracePathPair f h, h.1⟩,
    fun h => tracePathPair_isHexagon f h.1 h.2⟩

noncomputable def tracePathPairWords [Fintype V] (G : SimpleGraph V) :
    Finset (Fin 6 → V) := by
  classical
  exact Finset.univ.filter (IsTracePathPair G)

theorem mem_tracePathPairWords_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ tracePathPairWords G ↔ IsTracePathPair G f := by
  classical
  simp [tracePathPairWords]

open scoped Classical in
theorem tracePathPair_endpoint_fiber_card [Fintype V] (u v : V) :
    ((tracePathPairWords G).filter (fun f => (f 0, f 3) = (u, v))).card =
      (traceThreePaths G u v).card ^ 2 - (traceThreePaths G u v).card := by
  classical
  calc
    _ = (traceThreePaths G u v).offDiag.card := by
      apply Finset.card_bij (fun f _ => ((f 1, f 2), (f 5, f 4)))
      · intro f hf
        obtain ⟨hfp, he⟩ := Finset.mem_filter.mp hf
        have hp := (mem_tracePathPairWords_iff f).mp hfp
        have hu : f 0 = u := congrArg Prod.fst he
        have hv : f 3 = v := congrArg Prod.snd he
        apply Finset.mem_offDiag.mpr
        exact ⟨(mem_traceThreePaths_iff u v _).mpr (by simpa only [hu, hv] using hp.1),
          (mem_traceThreePaths_iff u v _).mpr (by simpa only [hu, hv] using hp.2.1),
          hp.2.2⟩
      · intro f hf g hg he
        have hfe := (Finset.mem_filter.mp hf).2
        have hge := (Finset.mem_filter.mp hg).2
        have h0 : f 0 = g 0 := (congrArg Prod.fst hfe).trans
          (congrArg Prod.fst hge).symm
        have h3 : f 3 = g 3 := (congrArg Prod.snd hfe).trans
          (congrArg Prod.snd hge).symm
        have h1 : f 1 = g 1 := congrArg (fun p : (V × V) × (V × V) => p.1.1) he
        have h2 : f 2 = g 2 := congrArg (fun p : (V × V) × (V × V) => p.1.2) he
        have h5 : f 5 = g 5 := congrArg (fun p : (V × V) × (V × V) => p.2.1) he
        have h4 : f 4 = g 4 := congrArg (fun p : (V × V) × (V × V) => p.2.2) he
        funext i
        fin_cases i <;> assumption
      · intro p hp
        obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
        have hword : IsTracePathPair G (tracePairFromData u v p) :=
          tracePairFromData_isPair u v p ((mem_traceThreePaths_iff u v _).mp h1)
            ((mem_traceThreePaths_iff u v _).mp h2) hne
        refine ⟨tracePairFromData u v p, Finset.mem_filter.mpr
          ⟨(mem_tracePathPairWords_iff _).mpr hword, rfl⟩, ?_⟩
        rfl
    _ = _ := by rw [Finset.offDiag_card, pow_two]

theorem tracePathPairWords_card [Fintype V] :
    (tracePathPairWords G).card =
      ∑ u : V, ∑ v : V,
        ((traceThreePaths G u v).card ^ 2 - (traceThreePaths G u v).card) := by
  classical
  calc
    _ = ∑ p : V × V,
        ((tracePathPairWords G).filter (fun f => (f 0, f 3) = p)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ p : V × V,
        ((traceThreePaths G p.1 p.2).card ^ 2 - (traceThreePaths G p.1 p.2).card) :=
      Finset.sum_congr rfl (fun p _ => tracePathPair_endpoint_fiber_card p.1 p.2)
    _ = _ := by rw [Fintype.sum_prod_type]

end TaskH.Six

#print axioms TaskH.Six.tracePairFromData_isPair
#print axioms TaskH.Six.tracePathPair_injective_iff
#print axioms TaskH.Six.tracePathPair_isHexagon
#print axioms TaskH.Six.isHexagon_isTracePathPair
#print axioms TaskH.Six.isHexagon_iff_injective_tracePathPair
#print axioms TaskH.Six.mem_tracePathPairWords_iff
#print axioms TaskH.Six.tracePathPair_endpoint_fiber_card
#print axioms TaskH.Six.tracePathPairWords_card
