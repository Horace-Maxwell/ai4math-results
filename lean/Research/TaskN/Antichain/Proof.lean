import Research.TaskN.Antichain.CompareCore
import Research.TaskN.Antichain.TreeRoot

namespace TaskN.Antichain.Proof

theorem WidthLowerBound : Challenge.WidthLowerBound :=
  width_of_roots RT.exists_largestRoot

theorem ArbitrarilyLarge : Challenge.ArbitrarilyLarge :=
  arbitrary_of_width WidthLowerBound

end TaskN.Antichain.Proof
