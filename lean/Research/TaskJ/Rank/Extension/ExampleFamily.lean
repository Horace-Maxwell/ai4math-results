import Research.TaskJ.Rank.Extension.Arithmetic
import Research.TaskJ.Rank.Extension.FiberAutomorphisms
import Research.TaskJ.Rank.Extension.SquareRank

namespace TaskJ.Rank.Extension.ExampleFamily

open Arithmetic

theorem faithful (n : ℕ) : Function.Injective (family n).action :=
  CRT.faithful (family n) outgoing (prod_out n) (outgoing_pairwise n)
    (fun i => dvd_mul_right (outgoing i) (incoming i))

theorem rank_two {n : ℕ} (hn : 3 ≤ n) :
    Group.rank (family n).automorphisms = 2 := by
  let D := family n
  let i : Fin n := ⟨0, by omega⟩
  have : Fact (1 < (D.modulus : ℕ)) :=
    ⟨(width_gt_one hn i).trans_le (Nat.le_of_dvd D.modulus.property (D.divides i))⟩
  let split := CRT.familySquare D outgoing incoming width_eq (prod_out n) (prod_in n)
    (outgoing_pairwise n) (incoming_pairwise n) cross_coprime
  let equiv := (D.automorphismsEquivProduct (width_injective hn)).trans split
  exact (Group.rank_congr equiv).trans (CRT.square_rank D.Actor)

end TaskJ.Rank.Extension.ExampleFamily
