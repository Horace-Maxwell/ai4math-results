import Research.TaskP.GradedWilf.WilfBasis
import Research.TaskP.GradedWilf.WilfScalar

namespace TaskP.GradedWilf
open Challenge

def layer (d t : ℕ) : Finset (Point d) := Finset.univ.piAntidiag t

@[simp] theorem mem_layer {d t : ℕ} {x : Point d} : x ∈ layer d t ↔ degree x = t := by
  simp [layer, degree]

theorem card_layer (d t : ℕ) : (layer d t).card = d.multichoose t := by
  have e := Finset.card_finsuppAntidiag_nat_eq_multichoose (s := (Finset.univ : Finset (Fin d))) t
  simpa [Finset.finsuppAntidiag,layer] using e

def ball (d t : ℕ) : Finset (Point d) :=
  (Finset.range (t+1)).biUnion (layer d)

@[simp] theorem mem_ball {d t : ℕ} {x : Point d} : x ∈ ball d t ↔ degree x ≤ t := by
  simp [ball]

theorem card_ball (d t : ℕ) : (ball d t).card = (t+d).choose d := by
  unfold ball
  rw [Finset.card_biUnion]
  · simpa only [card_layer] using Nat.sum_range_multichoose t d
  · intro i hi j hj hij
    exact Finset.disjoint_left.mpr (fun x hx hy => hij ((mem_layer.mp hx).symm.trans (mem_layer.mp hy)))

theorem below_eq_ball {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) (hd : 0 < d) :
    belowGaps (graded a b d) = (ball d (frob a b) : Set (Point d)) := by
  obtain ⟨hgap,habove⟩ := frob_spec ha hb hc
  ext x
  constructor
  · rintro ⟨y,hy,hle⟩
    apply mem_ball.mpr
    have hsum : degree x ≤ degree y := Finset.sum_le_sum (fun i _ => hle i)
    exact hsum.trans (le_of_not_gt (fun h => hy (habove _ h)))
  · intro hx
    have h := mem_ball.mp hx
    let i : Fin d := ⟨0,hd⟩
    let z : Point d := Pi.single i (frob a b - degree x)
    have hz : degree z = frob a b - degree x := by simp [z,degree,Pi.single_apply]
    refine ⟨x+z, ?_, fun j => Nat.le_add_right (x j) (z j)⟩
    change degree (x+z) ∉ scalar a b
    simpa only [degree_add,hz,Nat.add_sub_of_le h] using hgap

end TaskP.GradedWilf
