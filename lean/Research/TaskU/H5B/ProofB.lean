import Research.TaskU.H5B.Construct
import Research.TaskU.H5B.Necessity
import Research.TaskU.H5B.CoprimeCongruence
import Research.TaskU.H5B.CoprimeSeeds

namespace TaskU.H5.ProofB

theorem fullSpectrum : ChallengeB.fullSpectrum := by
  intro m
  constructor
  · rintro ⟨f,rfl⟩
    by_cases h : (5:ℤ) ∣ groupDet f
    · exact Or.inr (Spectrum.divisible_necessary f h)
    · exact Or.inl (Coprime.coprime_necessary f h)
  · rintro (h | ⟨k,rfl⟩ | ⟨n,_,rfl,q,hq,hd⟩)
    · exact Coprime.coprime_sufficient m h
    · exact Spectrum.high_sufficient k
    · exact Spectrum.low_sufficient hq hd

#print axioms fullSpectrum
end TaskU.H5.ProofB
