import Research.TaskP.RectangleDefect.StripLayout
import Research.TaskP.RectangleDefect.BoundaryRows

namespace TaskP.RectangleDefect

open Challenge Set

def joinTiles {k : ℕ} (m b : Counts k) :
    (Tile m ⊕ Tile b) ≃ Tile (fun i => m i + b i) :=
  (Equiv.sigmaSumDistrib (fun i => Fin (m i)) (fun i => Fin (b i))).symm.trans
    (Equiv.sigmaCongrRight (fun _ => finSumFinEquiv))

def placeLabels {k : ℕ} {m A B V : Counts k} (part : ∀ i, A i+B i+V i=m i) :
    Placed (Tile A) (Tile B) (Tile V) ≃ Tile m :=
  ((Equiv.sumCongr (joinTiles A B) (Equiv.refl _)).trans
    (joinTiles (fun i => A i + B i) V)).trans
    (Equiv.sigmaCongrRight fun i => finCongr (part i))

private def brickWidth {k : ℕ} {m : Counts k} (t : Tile m) : ℝ := (t.1.val+1 : ℕ)

private theorem sum_width {k : ℕ} (m : Counts k) :
    ∑ t : Tile m, brickWidth t = area m := by
  rw [Fintype.sum_sigma]
  simp [brickWidth,area,mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  ring

private theorem sum_tile_ones {k : ℕ} (m : Counts k) :
    ∑ _ : Tile m, (1 : ℝ) = (∑ i, m i : ℕ) := by
  rw [Fintype.sum_sigma]
  simp

theorem tiles_of_rowSplit {k n : ℕ} {m : Counts k} (hn : 0 < n) (split : RowSplit m n) :
    tiles m n := by
  classical
  obtain ⟨A,B,V,part,vsize,ha,hb⟩ := split
  let E := placeLabels part
  let L : ℝ := area A
  let F : ℝ := (∑ i, V i : ℕ)
  have ab : area A = area B := by omega
  have hwidth : F + L = (n : ℝ) := by
    dsimp [F,L]
    exact_mod_cast (show (∑ i, V i) + area A = n by omega)
  let top := mkStrip (brickWidth (m := A)) (fun t => by unfold brickWidth; positivity) L (sum_width A)
  let bot := mkStrip (brickWidth (m := B)) (fun t => by unfold brickWidth; positivity) L
    (by simpa only [ab, L] using sum_width B)
  let vert := mkStrip (fun _ : Tile V => (1 : ℝ)) (fun _ => zero_lt_one) F (sum_tile_ones V)
  let anchor := fun t : Tile m => offsetOfPlace top bot vert (E.symm t)
  let d : Placed (Tile A) (Tile B) (Tile V) → Bool := fun s => match s with
    | .inl _ => false
    | .inr _ => true
  let dir := fun t : Tile m => d (E.symm t)
  have sizes (s : Placed (Tile A) (Tile B) (Tile V)) :
      tileSize dir (E s) = sizeOfPlace brickWidth brickWidth s := by
    simp only [tileSize,dir,E.symm_apply_apply]
    rcases s with (s | s) | s
    · rfl
    · rfl
    · change (((s.1.val+1 : ℕ) : ℝ),1) = (2,1)
      rw [vsize _ (Nat.ne_zero_of_lt s.2.isLt)]
      norm_num
  have start (s : Placed (Tile A) (Tile B) (Tile V)) :
      anchor (E s) = offsetOfPlace top bot vert s := by simp [anchor]
  have cover := layout_closed top bot vert (show 0 ≤ L by dsimp [L]; positivity)
    (show 0 ≤ F by dsimp [F]; positivity) (hwidth ▸ (by exact_mod_cast hn))
  rw [hwidth] at cover
  refine ⟨anchor,dir,?_,?_⟩
  · change (⋃ t, placeClosed (anchor t) (tileSize dir t)) = _
    rw [← cover]
    ext xy
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t,ht⟩
      obtain ⟨s,rfl⟩ := E.surjective t
      exact ⟨s, by simpa only [start,sizes] using ht⟩
    · rintro ⟨s,hs⟩
      exact ⟨E s, by simpa only [start,sizes] using hs⟩
  · intro t u hne
    obtain ⟨s,rfl⟩ := E.surjective t
    obtain ⟨r,rfl⟩ := E.surjective u
    change Disjoint (placeOpen (anchor _) (tileSize dir _)) (placeOpen (anchor _) (tileSize dir _))
    rw [start,start,sizes,sizes]
    exact layout_open top bot vert s r (fun h => hne (congrArg E h))

theorem tiles_iff_rowSplit {k n : ℕ} {m : Counts k} (hn : 0 < n) (hm : area m = 2*n) :
    tiles m n ↔ RowSplit m n := ⟨rowSplit_of_tiles hm, tiles_of_rowSplit hn⟩

end TaskP.RectangleDefect
