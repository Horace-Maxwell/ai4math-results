import Research.TaskH.Seven.SevenTwoColorDetours
import Research.TaskH.Seven.SevenColorClassBudgets

/-! The actual singleton-class capacity and actual short detours force a
connected singleton/pair Kempe path to have exactly seven edges.  Connecting
at least four of the five pairs is a separate, explicitly outstanding task. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem twoColor_exists_length_seven [Fintype V]
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {a b s t u : {z : V // z ≠ v}} (beta : Fin 7)
    (hbeta : beta ≠ c a) (hend : c b = beta)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) (hab : ¬ G.Adj a.val b.val)
    (hsa : c s ≠ c a) (hsb : c s ≠ beta)
    (hta : c t ≠ c a) (htb : c t ≠ beta)
    (hucolor : c u = c t) (htu : t ≠ u) (hst : c s ≠ c t)
    (hbs : G.Adj b.val s.val) (hsv : G.Adj s.val v)
    (hstedge : G.Adj s.val t.val) (htv : G.Adj t.val v)
    (hvu : G.Adj v u.val) (hua : G.Adj u.val a.val)
    (hclass : (Finset.univ.filter (fun z : {x : V // x ≠ v} => c z = c a)).card ≤ 5)
    (hreach : b ∈ twoColorComponent c (c a) beta a) :
    ∃ p : (G.induce {x | x ≠ v}).Walk a b,
      p.IsPath ∧ Follows p c (Equiv.swap (c a) beta) ∧
      (∀ q : (G.induce {x | x ≠ v}).Walk a b,
        Follows q c (Equiv.swap (c a) beta) → p.length ≤ q.length) ∧
      p.length = 7 := by
  obtain ⟨p, hp, hf, hmin, hpos, hodd⟩ := twoColor_exists_shortest c beta hbeta hend hreach
  have hcap := twoColor_odd_path_length_le p c beta hp hf hodd 5 hclass
  have h1 : p.length ≠ 1 := by
    intro hl
    have hedge := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
    have hend' : p.getVert 1 = b := by simpa only [hl] using p.getVert_length
    rw [Walk.getVert_zero, hend'] at hedge
    exact hab hedge
  have h3 := twoColor_path_length_ne_three hr v c beta hbeta hend hsa hsb
    (by simpa [hucolor] using hta) (by simpa [hucolor] using htb)
    (by simpa [hucolor] using hst) hbs hsv hvu hua p hp hf
  have h5 := twoColor_path_length_ne_five hr v c ha hb beta hbeta hend p hp hf
  have h9 := twoColor_path_length_ne_nine hs v c beta hbeta hend hsa hsb hta htb
    hucolor htu hst hbs hstedge htv hvu hua p hp hf
  exact ⟨p, hp, hf, hmin, by omega⟩

theorem equality_singleton_color_path_capacity [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    {a b : {z : V // z ≠ v}} (ha : c a = j.val)
    (beta : Fin 7) (p : (G.induce {x | x ≠ v}).Walk a b)
    (hp : p.IsPath) (hf : Follows p c (Equiv.swap (c a) beta))
    (hodd : p.length % 2 = 1) : p.length ≤ 9 := by
  have hclass := equality_singletonColorClass_card_le_five hcrit hc hnot v c i j hij
  have hcard : (Finset.univ.filter (fun z : {x : V // x ≠ v} => c z = c a)).card ≤ 5 := by
    simpa only [deletedColorClass, ha] using hclass
  have hcap := twoColor_odd_path_length_le p c beta hp hf hodd 5 hcard
  omega

theorem equality_singleton_exists_length_seven [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    {a b s t u : {z : V // z ≠ v}} (hacolor : c a = j.val) (beta : Fin 7)
    (hbeta : beta ≠ c a) (hend : c b = beta)
    (ha : G.Adj v a.val) (hb : G.Adj v b.val) (hab : ¬ G.Adj a.val b.val)
    (hsa : c s ≠ c a) (hsb : c s ≠ beta)
    (hta : c t ≠ c a) (htb : c t ≠ beta)
    (hucolor : c u = c t) (htu : t ≠ u) (hst : c s ≠ c t)
    (hbs : G.Adj b.val s.val) (hsv : G.Adj s.val v)
    (hstedge : G.Adj s.val t.val) (htv : G.Adj t.val v)
    (hvu : G.Adj v u.val) (hua : G.Adj u.val a.val)
    (hreach : b ∈ twoColorComponent c (c a) beta a) :
    ∃ p : (G.induce {x | x ≠ v}).Walk a b,
      p.IsPath ∧ Follows p c (Equiv.swap (c a) beta) ∧
      (∀ q : (G.induce {x | x ≠ v}).Walk a b,
        Follows q c (Equiv.swap (c a) beta) → p.length ≤ q.length) ∧
      p.length = 7 := by
  have hclass := equality_singletonColorClass_card_le_five hcrit hc hnot v c i j hij
  have hcard : (Finset.univ.filter (fun z : {x : V // x ≠ v} => c z = c a)).card ≤ 5 := by
    simpa only [deletedColorClass, hacolor] using hclass
  exact twoColor_exists_length_seven (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) v c beta hbeta hend ha hb hab hsa hsb hta htb
    hucolor htu hst hbs hsv hstedge htv hvu hua hcard hreach

end TaskH.Seven
#print axioms TaskH.Seven.twoColor_exists_length_seven
#print axioms TaskH.Seven.equality_singleton_color_path_capacity
#print axioms TaskH.Seven.equality_singleton_exists_length_seven
