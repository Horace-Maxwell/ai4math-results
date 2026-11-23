import Research.TaskV.Illumination.Gaps
import Research.TaskV.Illumination.Upper
import Research.TaskV.Illumination.Lower

namespace PrismIllumination

theorem prism_trichotomy : Trichotomy := by
  intro K hc hv hP hQ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨r,hr,hg⟩ := gapSix hP hQ hc h
    exact ⟨upperSix hc.isClosed hP hQ hr hg, lowerSix hP hQ⟩
  · intro he hn
    obtain ⟨b,r,hr,hg⟩ := gapSeven hP hQ hc hv hn
    exact ⟨upperSeven hc.isClosed hP hQ b hr hg, lowerSeven hP hQ he⟩
  · rintro rfl
    exact ⟨cubeEight, lowerEight⟩

end PrismIllumination
