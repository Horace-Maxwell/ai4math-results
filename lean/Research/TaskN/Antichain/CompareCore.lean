import Research.TaskN.Antichain.GraphTransport
import Research.TaskN.Antichain.SequenceGraph
import Research.TaskN.Antichain.TreePolynomial

namespace TaskN.Antichain

open Polynomial SimpleGraph Challenge

private theorem positive_nonnegative {V : Type*} [Fintype V] (G : SimpleGraph V)
    {x : ℝ} (hx : 0 ≤ x) : 0 < (independencePolynomial G).eval x := by
  classical
  unfold independencePolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_pos'
  · intro s _
    split_ifs <;> simp [pow_nonneg hx]
  · refine ⟨∅, Finset.mem_univ _, ?_⟩
    simp [SimpleGraph.IsIndepSet]

theorem width_of_roots
    (hr : ∀ t : RT, ∃ r : ℝ, IsGreatest {x : ℝ | t.pair.1.eval x = 0} r) :
    WidthLowerBound := by
  intro n hn
  let m := n/11
  let pad := n%11
  have hm : 0 < m := by dsimp [m]; omega
  have hs : 11*m+pad = n := by dsimp [m,pad]; omega
  let cells (i : Fin (m+1)) := Num.family m i.val pad
  have hi (i : Fin (m+1)) : i.val ≤ m := by omega
  have hne (i : Fin (m+1)) : cells i ≠ [] := family_nonempty hm (hi i)
  let code (i : Fin (m+1)) := realise (cells i) (hne i)
  have hc (i : Fin (m+1)) : Fintype.card (code i).V = n :=
    (code i).cardV.trans ((realise_size (hi i) (hne i)).trans hs)
  let e (i : Fin (m+1)) := Fintype.equivFinOfCardEq (hc i)
  let G (i : Fin (m+1)) := (code i).graph.map (e i)
  have iso (i : Fin (m+1)) : (code i).graph ≃g G i := SimpleGraph.Iso.map (e i) _
  have hp (i : Fin (m+1)) : independencePolynomial (G i) = (code i).pair.1 :=
    (iso_ip (iso i)).trans (code i).polynomial_pair.1
  have hev (i : Fin (m+1)) (x : ℝ) :
      (independencePolynomial (G i)).eval x = (Num.val (cells i) x).1 := by
    rw [hp]
    exact realise_eval _ _ _
  have hroot (i : Fin (m+1)) : ∃ r, LargestRoot (G i) r := by
    simpa only [LargestRoot, hp] using hr (code i)
  have left (i : Fin (m+1)) {r : ℝ} (h : LargestRoot (G i) r) : r < -(1/6:ℝ) := by
    have hz : (independencePolynomial (G i)).eval r = 0 := h.1
    by_contra! hle
    by_cases hr0 : r ≤ 0
    · have hpos := Num.val_pos (cells i) (show r ∈ Set.Icc (-(1/6:ℝ)) 0 from ⟨hle,hr0⟩)
      rw [← hev] at hpos
      linarith
    · exact (positive_nonnegative (G i) (le_of_not_ge hr0)).ne' hz
  have inc (i j : Fin (m+1)) (hij : i.val < j.val) :
      ¬ Precedes (G i) (G j) ∧ ¬ Precedes (G j) (G i) := by
    obtain ⟨ri,hri⟩ := hroot i
    obtain ⟨rj,hrj⟩ := hroot j
    constructor
    · intro h
      have hcomp := h rj hrj (-(1/6:ℝ)) ⟨(left j hrj).le,by norm_num⟩
      rw [hev, hev] at hcomp
      exact (not_le_of_gt (Num.family_strict_6 pad hij (hi j))) hcomp
    · intro h
      have hcomp := h ri hri (-(1/10:ℝ)) ⟨by linarith [left i hri],by norm_num⟩
      rw [hev, hev] at hcomp
      exact (not_le_of_gt (Num.family_strict_10 pad hij (hi j))) hcomp
  refine ⟨G,fun i ↦ ⟨(iso i).isTree_iff.mp (code i).tree,hroot i⟩,?_⟩
  intro i j hne'
  rcases lt_or_gt_of_ne hne' with hij | hji
  · exact inc i j hij
  · exact (inc j i hji).symm

theorem arbitrary_of_width (hw : WidthLowerBound) : ArbitrarilyLarge := by
  intro k
  let n := 11*(k+1)
  have hn : 11 ≤ n := by dsimp [n]; omega
  obtain ⟨F,hF,hpair⟩ := hw n hn
  have hle : k ≤ n/11+1 := by dsimp [n]; omega
  exact ⟨n,fun i ↦ F (i.castLE hle),fun i ↦ hF _,fun i j hne ↦
    hpair _ _ (fun h ↦ hne (Fin.ext (congrArg (fun x : Fin (n/11+1) ↦ x.val) h)))⟩

end TaskN.Antichain
