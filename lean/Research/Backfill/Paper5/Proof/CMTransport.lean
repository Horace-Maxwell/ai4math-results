import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5.CMTransport

open BackfillPaper5 Function

/-- Transport the actual mapping, by conjugating its underlying function. -/
def transport {G M : Type*} [Mul G] [Mul M] (e : G ≃* M) (f : G → G) : M → M :=
  fun y => e (f (e.symm y))

theorem transport_complete {G M : Type*} [Mul G] [Mul M] (e : G ≃* M) (f : G → G)
    (hf : Challenge.IsCompleteMapping (· * ·) f) :
    Challenge.IsCompleteMapping (· * ·) (transport e f) := by
  constructor
  · exact e.bijective.comp (hf.1.comp e.symm.bijective)
  · have heq : (fun y : M => y * transport e f y) =
        (fun y : M => e (e.symm y * f (e.symm y))) := by
      funext y
      simp only [transport, e.map_mul, e.apply_symm_apply]
    change Bijective (fun y : M => y * transport e f y)
    rw [heq]
    exact e.bijective.comp (hf.2.comp e.symm.bijective)

/-- Existence of an actual complete mapping is invariant under a multiplication equivalence. -/
theorem hasCM_iff {G M : Type*} [Mul G] [Mul M] (e : G ≃* M) :
    Challenge.HasCM G ↔ Challenge.HasCM M := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨transport e f, transport_complete e f hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨transport e.symm f, transport_complete e.symm f hf⟩

/-- Inversion, followed by `op`, is a multiplication equivalence for every group. -/
theorem hasCM_opposite (G : Type*) [Group G] :
    Challenge.HasCM G ↔ Challenge.HasCM Gᵐᵒᵖ :=
  hasCM_iff (MulEquiv.inv' G)

#print axioms CodexPaper5.CMTransport.transport_complete
#print axioms CodexPaper5.CMTransport.hasCM_iff
#print axioms CodexPaper5.CMTransport.hasCM_opposite

end CodexPaper5.CMTransport
