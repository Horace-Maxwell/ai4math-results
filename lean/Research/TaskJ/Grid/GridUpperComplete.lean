import Research.TaskJ.Grid.GridUpper
import Research.TaskJ.Grid.GridNarrow

namespace Grid

theorem upper_complete : Challenge.LengthUpperBound := by
  apply upper_of_narrow
  intro d hd odd p hp
  let m := d / 2
  have hm : 0 < m := by dsimp [m]; omega
  have e : d = 2 * m + 1 := by dsimp [m]; omega
  exact e ▸ Narrow.bound m hm (e ▸ hp)

end Grid

#print axioms Grid.upper_complete
