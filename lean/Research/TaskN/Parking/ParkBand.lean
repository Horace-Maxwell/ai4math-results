import Research.TaskN.Parking.ParkPrefix

namespace TaskN.Parking
open Challenge
open scoped Classical

theorem band_eq_prefix (b : ℕ) (xs : List ℕ) (hd : dominant xs) :
    ((Finset.Icc b (b+xs.sum)).filter
      (fun a => xs.sum ≤ a-b ∨ prefixSymmetric xs (xs.sum-(a-b)))).card =
    ((Finset.range ((ruler (jumps xs)).length+1)).filter
      (fun i => pal ((ruler (jumps xs)).take i))).card := by
  let w := ruler (jumps xs)
  let good := (Finset.range (w.length+1)).filter (fun i => pal (w.take i))
  let pick := fun i => b+(xs.sum - (w.take i).sum)
  obtain ⟨hsum,hpos,hset⟩ := walk_of_dominant xs hd
  change w.sum=xs.sum at hsum
  change positive w at hpos
  change points w=subsetSums xs at hset
  have bound (i : ℕ) (hi : i≤ w.length) : (w.take i).sum ≤ xs.sum := by
    rw [←hsum]
    exact point_bound ((point_iff_take w _).2 ⟨i,hi,rfl⟩)
  have hz : prefixSymmetric xs 0 := by
    refine ⟨zero_mem_subsets _,?_⟩
    intro s _ _
    simp
  have heq : ((Finset.Icc b (b+xs.sum)).filter
      (fun a => xs.sum ≤ a-b ∨ prefixSymmetric xs (xs.sum-(a-b)))) = good.image pick := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_filter.mp ha with ⟨hband,hp⟩
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hband
      have ps : prefixSymmetric xs (xs.sum-(a-b)) := hp.elim
        (fun h => by rw [Nat.sub_eq_zero_of_le h]; exact hz) id
      have hm := ps.1
      rw [←hset] at hm
      obtain ⟨i,hi,he⟩ := (point_iff_take w _).1 hm
      have hpal : pal (w.take i) :=
        (prefixSymmetric_take hd i).1 (by change prefixSymmetric xs (w.take i).sum; rwa [he])
      apply Finset.mem_image.mpr
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hpal⟩,
        by dsimp [pick]; omega⟩
    · intro ha
      obtain ⟨i,hg,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hi,hp⟩ := Finset.mem_filter.mp hg
      have hi' : i≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hlim := bound i hi'
      change b+(xs.sum-(w.take i).sum) ∈ _ 
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩, Or.inr ?_⟩
      convert (prefixSymmetric_take hd i).2 hp using 1
      change xs.sum - (b+(xs.sum-(w.take i).sum)-b)=(w.take i).sum
      omega
  rw [heq]
  change (good.image pick).card=good.card
  apply Finset.card_image_of_injOn
  intro i hi j hj he
  have hi' : i≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
  have hj' : j≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  apply take_sum_inj hpos i j hi' hj'
  change b+(xs.sum-(w.take i).sum)=b+(xs.sum-(w.take j).sum) at he
  have := bound i hi'
  have := bound j hj'
  omega

end TaskN.Parking
