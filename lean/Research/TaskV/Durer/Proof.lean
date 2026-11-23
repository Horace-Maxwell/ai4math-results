import Research.TaskV.Durer.Arc
import Research.TaskV.Durer.Metric
import Research.TaskV.Durer.Contacts
import Research.TaskV.Durer.Example

namespace DurerDV

theorem strictRoofNet : StrictRoofNet := by
  intro s
  obtain ⟨u,hu⟩ := existsArc s s.upper
  obtain ⟨v,hv⟩ := existsArc s s.lower
  exact ⟨u,v,hu,hv,metric s u v hu hv,contacts s u v hu hv⟩

end DurerDV
