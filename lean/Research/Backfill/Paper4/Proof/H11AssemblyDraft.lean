import Research.Backfill.Paper4.Proof.H11SubsetCover
import Research.Backfill.Paper4.Proof.H11Metric
import Research.Backfill.Paper4.Proof.H11DHBlock00
import Research.Backfill.Paper4.Proof.H11DHBlock01
import Research.Backfill.Paper4.Proof.H11DHBlock02
import Research.Backfill.Paper4.Proof.H11DHBlock03
import Research.Backfill.Paper4.Proof.H11DHBlock04
import Research.Backfill.Paper4.Proof.H11DHBlock05
import Research.Backfill.Paper4.Proof.H11DHBlock06
import Research.Backfill.Paper4.Proof.H11DHBlock07
import Research.Backfill.Paper4.Proof.H11DHBlock08
import Research.Backfill.Paper4.Proof.H11DHBlock09
import Research.Backfill.Paper4.Proof.H11DHBlock10
import Research.Backfill.Paper4.Proof.H11DHBlock11
import Research.Backfill.Paper4.Proof.H11DHBlock12
import Research.Backfill.Paper4.Proof.H11DHBlock13
import Research.Backfill.Paper4.Proof.H11DHBlock14
import Research.Backfill.Paper4.Proof.H11DHBlock15
import Research.Backfill.Paper4.Proof.H11DHBlock16
import Research.Backfill.Paper4.Proof.H11DHBlock17
import Research.Backfill.Paper4.Proof.H11DHBlock18
import Research.Backfill.Paper4.Proof.H11DHBlock19
import Research.Backfill.Paper4.Proof.H11DHBlock20
import Research.Backfill.Paper4.Proof.H11DHBlock21
import Research.Backfill.Paper4.Proof.H11DHBlock22
import Research.Backfill.Paper4.Proof.H11DHBlock23
import Research.Backfill.Paper4.Proof.H11DHBlock24
import Research.Backfill.Paper4.Proof.H11DHBlock25
import Research.Backfill.Paper4.Proof.H11DHBlock26
import Research.Backfill.Paper4.Proof.H11DHBlock27
import Research.Backfill.Paper4.Proof.H11DHBlock28
import Research.Backfill.Paper4.Proof.H11DHBlock29
import Research.Backfill.Paper4.Proof.H11DHBlock30
import Research.Backfill.Paper4.Proof.H11DHBlock31
import Research.Backfill.Paper4.Proof.F1DistanceHereditary
import Research.Backfill.Paper4.Proof.NonDHExamples

/-! Final H11 assembly source. All thirty-two block modules are explicit dependencies.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace H11Assembly

def HighValid (H : Finset (Fin 5)) : Prop :=
  ∀ L : Finset (Fin 6), ∃ C : Finset (Fin 11),
    ConcreteDHCertificate.Cut Challenge.H11 (H11SubsetCover.join L H) C ∨
      ConcreteDHCertificate.Descent Challenge.H11 H11Metric.D11 (H11SubsetCover.join L H)

/-- The entries follow exactly the fixed 32-element high-subset enumeration. -/
theorem all_high_blocks : H11SubsetCover.highSubsets.Forall HighValid := by
  exact And.intro H11DHBlock00.block_valid (And.intro H11DHBlock01.block_valid (And.intro H11DHBlock02.block_valid (And.intro H11DHBlock03.block_valid (And.intro H11DHBlock04.block_valid (And.intro H11DHBlock05.block_valid (And.intro H11DHBlock06.block_valid (And.intro H11DHBlock07.block_valid (And.intro H11DHBlock08.block_valid (And.intro H11DHBlock09.block_valid (And.intro H11DHBlock10.block_valid (And.intro H11DHBlock11.block_valid (And.intro H11DHBlock12.block_valid (And.intro H11DHBlock13.block_valid (And.intro H11DHBlock14.block_valid (And.intro H11DHBlock15.block_valid (And.intro H11DHBlock16.block_valid (And.intro H11DHBlock17.block_valid (And.intro H11DHBlock18.block_valid (And.intro H11DHBlock19.block_valid (And.intro H11DHBlock20.block_valid (And.intro H11DHBlock21.block_valid (And.intro H11DHBlock22.block_valid (And.intro H11DHBlock23.block_valid (And.intro H11DHBlock24.block_valid (And.intro H11DHBlock25.block_valid (And.intro H11DHBlock26.block_valid (And.intro H11DHBlock27.block_valid (And.intro H11DHBlock28.block_valid (And.intro H11DHBlock29.block_valid (And.intro H11DHBlock30.block_valid (H11DHBlock31.block_valid)))))))))))))))))))))))))))))))

/-- Complete finite-subset coverage; the two initial cost probes alone do not supply this. -/
theorem all_subsets_valid :
    ∃ cut : Finset (Fin 11) → Finset (Fin 11),
      ConcreteDHCertificate.Valid Challenge.H11 H11Metric.D11 cut := by
  apply H11SubsetCover.all_block_certificates_valid
  intro H hH L _hL
  exact ((List.forall_iff_forall_mem.mp all_high_blocks) H hH) L

theorem H11_distanceHereditary : Challenge.IsDistanceHereditary Challenge.H11 := by
  obtain ⟨cut, hcert⟩ := all_subsets_valid
  exact ConcreteDHCertificate.isDistanceHereditary Challenge.H11 H11Metric.D11 cut
    H11Metric.H11_connected H11Metric.H11_dist hcert

end H11Assembly

theorem check_Remark5_ii : Challenge.Remark5_ii :=
  ⟨H11Assembly.H11_distanceHereditary, H11Metric.metric_facts⟩

theorem check_Remark5_iii : Challenge.Remark5_iii := by
  intro h
  have hstrict : 2 * Challenge.H11.diam < Challenge.triameter Challenge.H11 := by
    rw [H11Metric.diam, H11Metric.triameter]
    decide
  exact H11Metric.not_question3'
    (h (Fin 11) Challenge.H11 H11Assembly.H11_distanceHereditary hstrict)

theorem check_Sec6_DHtests : Challenge.Sec6_DHtests :=
  ⟨G2DistanceHereditary.G2_distanceHereditary, H11Assembly.H11_distanceHereditary,
    F1DistanceHereditary.F1G_distanceHereditary, F1DistanceHereditary.F1H_distanceHereditary,
    NonDHExamples.G1_not_distanceHereditary, NonDHExamples.HKOFig2_not_distanceHereditary⟩

#print axioms H11Assembly.H11_distanceHereditary
#print axioms check_Remark5_ii
#print axioms check_Remark5_iii
#print axioms check_Sec6_DHtests
end CodexPaper4

