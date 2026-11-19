import Research.TaskJ.Rank.Extension.ExampleFamily
import Research.TaskJ.Rank.Extension.PacketRank

namespace TaskJ.Rank.Extension.Proof

/-- All quantities are taken from the same faithful cyclic action. -/
theorem UnboundedGap : TaskJ.Rank.Extension.UnboundedGap := by
  intro n hn
  let D := Arithmetic.family n
  have wide := Arithmetic.width_gt_one hn
  have injective := Arithmetic.width_injective hn
  have boxes := D.r_eq injective
  have singles := D.kappa_eq injective
  have correction := D.capitalLambda_eq (by omega) injective wide
  refine ⟨D, wide, injective, ExampleFamily.faithful n, inferInstance,
    D.stabilizer_eq, D.orbit_eq, D.box_injective injective, fun i => ⟨D.weylFiber i⟩,
    boxes, singles, correction, ExampleFamily.rank_two hn, D.valid_exists, ?_⟩
  intro B hB
  have count := D.packets_eq hB wide Arithmetic.width_non_coprime
  refine ⟨count, ?_, ?_⟩ <;>
    simp [Family.journal, Family.preprint, boxes, singles, correction, count]

end TaskJ.Rank.Extension.Proof

#print axioms TaskJ.Rank.Extension.Proof.UnboundedGap
