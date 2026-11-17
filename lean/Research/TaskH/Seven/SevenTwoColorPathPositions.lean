import Research.TaskH.Seven.SevenTwoColorRetention

/-! Genuine positions on the actual seven-edge paths. In particular the
same-colored opposite leaf cannot be confused with an internal path point.
The position-four point has no Q-neighbor by a displayed five-edge path. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.seven_path_prefix_ne_splitB {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7) (n : ℕ) (hn : n < 7) :
    (p.getVert n).val ≠ (F.splitB j).val := by
  intro he
  have hpoint : p.getVert n = F.splitBD j := Subtype.ext he
  have hcol := twoColor_color_at p c (F.pairIndex i).val hf n (by omega)
  have hca : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
  have hcj : c (F.splitBD j) = (F.pairIndex j).val := F.splitB_color j
  by_cases hpar : n % 2 = 0
  · rw [ite_eq_left hpar, hpoint, hcj, hca] at hcol
    exact F.pairColor_ne_singleton j 0 hcol
  · rw [ite_eq_right hpar, hpoint, hcj] at hcol
    have hji : j = i := F.pairColor_injective hcol
    subst j
    have he' : p.getVert n = p.getVert p.length := by
      rw [Walk.getVert_length]
      exact hpoint
    have hindex := hp.getVert_injOn (by change n ≤ p.length; omega)
      (by change p.length ≤ p.length; exact le_rfl) he'
    omega

theorem DegreeTwelveFrame.seven_path_position_ne_center_one {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (n : ℕ) (hn : n ≤ p.length) :
    (p.getVert n).val ≠ (F.center 1).val := by
  intro he
  have hpoint : p.getVert n = F.centerD 1 := Subtype.ext he
  have hcol := twoColor_color_at p c (F.pairIndex i).val hf n hn
  have hca : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
  have hcb : c (F.centerD 1) = (F.singletonIndex 1).val := F.center_color 1
  by_cases hpar : n % 2 = 0
  · rw [ite_eq_left hpar, hpoint, hcb, hca] at hcol
    exact (F.singletonColor_injective.ne (by decide : (1 : Fin 2) ≠ 0)) hcol
  · rw [ite_eq_right hpar, hpoint, hcb] at hcol
    exact F.pairColor_ne_singleton i 1 hcol.symm

theorem DegreeTwelveFrame.seven_path_even_position_outside {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (n : ℕ) (hn : n ≤ p.length) (hn0 : n ≠ 0) (heven : n % 2 = 0) :
    (p.getVert n).val ∉ insert v (G.neighborFinset v) := by
  intro hm
  rcases Finset.mem_insert.mp hm with he | he
  · exact (p.getVert n).property he
  · have hadj := (G.mem_neighborFinset v (p.getVert n).val).mp he
    have hcol : c (p.getVert n) = (F.singletonIndex 0).val := by
      have hh := twoColor_color_at p c (F.pairIndex i).val hf n hn
      rw [ite_eq_left heven] at hh
      exact hh.trans (F.center_color 0)
    have hpoint := (F.singleton_fiber_as_deleted 0 (p.getVert n) hadj).mp hcol
    exact hn0 ((hp.getVert_eq_start_iff hn).mp hpoint)

theorem DegreeTwelveFrame.seven_path_position_four_not_adj_Q
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7) : ¬ G.Adj (p.getVert 4).val (F.splitB j).val := by
  intro he
  let f : Fin 5 → V := fun n => (p.getVert n.val).val
  have hfinj : Function.Injective f := by
    intro n m hh
    apply Fin.ext
    exact hp.getVert_injOn (by change n.val ≤ p.length; omega)
      (by change m.val ≤ p.length; omega) (Subtype.ext hh)
  let t : Fin 6 → V := Fin.append f (fun _ : Fin 1 => (F.splitB j).val)
  have ht : Function.Injective t := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hfinj, fun n m _ => Subsingleton.elim n m, ?_⟩
    intro n _m
    exact F.seven_path_prefix_ne_splitB i j p hp hf hl n.val (by omega)
  have htv : ∀ n : Fin 6, t n ≠ v := by
    intro n
    fin_cases n
    all_goals first
      | exact (p.getVert _).property
      | exact (F.splitB j).property.ne.symm
  have hstart : G.Adj v (t 0) := by
    change G.Adj v (p.getVert 0).val
    rw [Walk.getVert_zero]
    exact (F.center 0).property
  have hend : G.Adj v (t 5) := (F.splitB j).property
  have h01 : G.Adj (t 0) (t 1) := p.adj_getVert_succ (i := 0) (by omega)
  have h12 : G.Adj (t 1) (t 2) := p.adj_getVert_succ (i := 1) (by omega)
  have h23 : G.Adj (t 2) (t 3) := p.adj_getVert_succ (i := 2) (by omega)
  have h34 : G.Adj (t 3) (t 4) := p.adj_getVert_succ (i := 3) (by omega)
  have h45 : G.Adj (t 4) (t 5) := he
  have hcol : c ⟨t 0, htv 0⟩ = c ⟨t 2, htv 2⟩ := by
    have hh := twoColor_color_at p c (F.pairIndex i).val hf 2 (by omega)
    change c (p.getVert 0) = c (p.getVert 2)
    rw [Walk.getVert_zero]
    simpa only [show (2 : ℕ) % 2 = 0 from rfl, ite_true] using hh.symm
  exact rooted_five_path_same_color_false hr v c t ht htv hstart hend
    h01 h12 h23 h34 h45 0 2 (by decide) hcol

theorem DegreeTwelveFrame.seven_path_position_two_not_adj_Q
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i j : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7) : ¬ G.Adj (p.getVert 2).val (F.splitB j).val := by
  intro he
  obtain ⟨l, hlj⟩ : ∃ l : Fin 5, l ≠ j := exists_ne j
  have hj := F.splitAB_adjacencies j (hF j)
  have hlE := F.splitAB_adjacencies l (hF l)
  have h01 : (p.getVert 0).val ≠ (p.getVert 1).val := by
    intro hh
    have hn := hp.getVert_injOn (by change 0 ≤ p.length; omega)
      (by change 1 ≤ p.length; omega) (Subtype.ext hh)
    omega
  have h02 : (p.getVert 0).val ≠ (p.getVert 2).val := by
    intro hh
    have hn := hp.getVert_injOn (by change 0 ≤ p.length; omega)
      (by change 2 ≤ p.length; omega) (Subtype.ext hh)
    omega
  have h12 : (p.getVert 1).val ≠ (p.getVert 2).val := by
    intro hh
    have hn := hp.getVert_injOn (by change 1 ≤ p.length; omega)
      (by change 2 ≤ p.length; omega) (Subtype.ext hh)
    omega
  have h0j := F.seven_path_prefix_ne_splitB i j p hp hf hl 0 (by decide)
  have h1j := F.seven_path_prefix_ne_splitB i j p hp hf hl 1 (by decide)
  have h2j := F.seven_path_prefix_ne_splitB i j p hp hf hl 2 (by decide)
  have h0l := F.seven_path_prefix_ne_splitB i l p hp hf hl 0 (by decide)
  have h1l := F.seven_path_prefix_ne_splitB i l p hp hf hl 1 (by decide)
  have h2l := F.seven_path_prefix_ne_splitB i l p hp hf hl 2 (by decide)
  have h0b := F.seven_path_position_ne_center_one i p hf 0 (by omega)
  have h1b := F.seven_path_position_ne_center_one i p hf 1 (by omega)
  have h2b := F.seven_path_position_ne_center_one i p hf 2 (by omega)
  have hbj := F.center_splitB_ne 1 j
  have hbl := F.center_splitB_ne 1 l
  have hjl := F.splitB_injective.ne (Ne.symm hlj)
  let t : Fin 6 → V := ![(p.getVert 0).val, (p.getVert 1).val, (p.getVert 2).val,
    (F.splitB j).val, (F.center 1).val, (F.splitB l).val]
  have ht : Function.Injective t := by
    intro n m hh
    fin_cases n <;> fin_cases m <;> simp_all [t]
  have htv : ∀ n : Fin 6, t n ≠ v := by
    intro n
    fin_cases n
    all_goals first
      | exact (p.getVert _).property
      | exact (F.splitB j).property.ne.symm
      | exact (F.center 1).property.ne.symm
      | exact (F.splitB l).property.ne.symm
  have hstart : G.Adj v (t 0) := by
    change G.Adj v (p.getVert 0).val
    rw [Walk.getVert_zero]
    exact (F.center 0).property
  have hcol : c ⟨t 0, htv 0⟩ = c ⟨t 2, htv 2⟩ := by
    simpa [t] using (twoColor_color_at p c (F.pairIndex i).val hf 2 (by omega)).symm
  exact rooted_five_path_same_color_false hr v c t ht htv hstart (F.splitB l).property
    (p.adj_getVert_succ (i := 0) (by omega))
    (p.adj_getVert_succ (i := 1) (by omega)) he hj.2.2.1.symm hlE.2.2.1
    0 2 (by decide) hcol

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_prefix_ne_splitB
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_position_ne_center_one
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_even_position_outside
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_position_four_not_adj_Q
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_position_two_not_adj_Q
