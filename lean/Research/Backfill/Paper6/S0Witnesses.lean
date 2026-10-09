import Research.Backfill.Paper6.S0WitnessBlock00
import Research.Backfill.Paper6.S0WitnessBlock01
import Research.Backfill.Paper6.S0WitnessBlock02
import Research.Backfill.Paper6.S0WitnessBlock03
import Research.Backfill.Paper6.S0WitnessBlock04
import Research.Backfill.Paper6.S0WitnessBlock05
import Research.Backfill.Paper6.S0WitnessBlock06
import Research.Backfill.Paper6.S0WitnessBlock07
import Research.Backfill.Paper6.S0WitnessBlock08
import Research.Backfill.Paper6.S0WitnessBlock09
import Research.Backfill.Paper6.S0WitnessBlock10
import Research.Backfill.Paper6.S0WitnessBlock11
import Research.Backfill.Paper6.S0WitnessBlock12
import Research.Backfill.Paper6.S0WitnessBlock13
import Research.Backfill.Paper6.S0WitnessBlock14
import Research.Backfill.Paper6.S0WitnessBlock15
import Research.Backfill.Paper6.S0WitnessBlock16
import Research.Backfill.Paper6.S0WitnessBlock17
import Research.Backfill.Paper6.S0WitnessBlock18
import Research.Backfill.Paper6.S0WitnessBlock19
import Research.Backfill.Paper6.S0WitnessBlock20
import Research.Backfill.Paper6.S0WitnessBlock21
import Research.Backfill.Paper6.S0WitnessBlock22
import Research.Backfill.Paper6.S0WitnessBlock23
import Research.Backfill.Paper6.S0WitnessBlock24
import Research.Backfill.Paper6.S0WitnessBlock25
import Research.Backfill.Paper6.S0WitnessBlock26
import Research.Backfill.Paper6.S0WitnessBlock27
import Research.Backfill.Paper6.S0WitnessBlock28
import Research.Backfill.Paper6.S0WitnessBlock29
import Research.Backfill.Paper6.S0WitnessBlock30
import Research.Backfill.Paper6.S0WitnessBlock31
import Research.Backfill.Paper6.S0WitnessBlock32
import Research.Backfill.Paper6.S0WitnessBlock33
import Research.Backfill.Paper6.S0WitnessBlock34
import Research.Backfill.Paper6.S0WitnessBlock35
import Research.Backfill.Paper6.S0WitnessBlock36
import Research.Backfill.Paper6.S0WitnessBlock37
import Research.Backfill.Paper6.S0WitnessBlock38
import Research.Backfill.Paper6.S0WitnessBlock39
import Research.Backfill.Paper6.S0WitnessBlock40
import Research.Backfill.Paper6.S0WitnessBlock41
import Research.Backfill.Paper6.S0WitnessBlock42
import Research.Backfill.Paper6.S0WitnessBlock43
import Research.Backfill.Paper6.S0WitnessBlock44
import Research.Backfill.Paper6.S0WitnessBlock45
import Research.Backfill.Paper6.S0WitnessBlock46
import Research.Backfill.Paper6.S0WitnessBlock47
import Research.Backfill.Paper6.S0WitnessBlock48
import Research.Backfill.Paper6.S0WitnessBlock49
import Research.Backfill.Paper6.S0WitnessBlock50
import Research.Backfill.Paper6.S0WitnessBlock51
import Research.Backfill.Paper6.S0WitnessBlock52
import Research.Backfill.Paper6.S0WitnessBlock53
import Research.Backfill.Paper6.S0WitnessBlock54
import Research.Backfill.Paper6.S0WitnessBlock55
import Research.Backfill.Paper6.S0WitnessBlock56
import Research.Backfill.Paper6.S0WitnessBlock57
import Research.Backfill.Paper6.S0WitnessBlock58
import Research.Backfill.Paper6.S0WitnessBlock59
import Research.Backfill.Paper6.S0WitnessBlock60
import Research.Backfill.Paper6.S0WitnessBlock61
import Research.Backfill.Paper6.S0WitnessBlock62
import Research.Backfill.Paper6.S0WitnessBlock63
import Research.Backfill.Paper6.S0WitnessBlock64

/-! Complete frozen ThmB_witnesses, conditional only on compiling its imports.
This source candidate has not been compiled. Every numerical row and every
coverage assertion must pass kernel checking before this target earns credit. -/

set_option autoImplicit false

namespace Paper6S0Witnesses

theorem all_blocks : ∀ b : Fin 65, BlockResult b.val := by
  intro b
  fin_cases b
  · exact block_00
  · exact block_01
  · exact block_02
  · exact block_03
  · exact block_04
  · exact block_05
  · exact block_06
  · exact block_07
  · exact block_08
  · exact block_09
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27
  · exact block_28
  · exact block_29
  · exact block_30
  · exact block_31
  · exact block_32
  · exact block_33
  · exact block_34
  · exact block_35
  · exact block_36
  · exact block_37
  · exact block_38
  · exact block_39
  · exact block_40
  · exact block_41
  · exact block_42
  · exact block_43
  · exact block_44
  · exact block_45
  · exact block_46
  · exact block_47
  · exact block_48
  · exact block_49
  · exact block_50
  · exact block_51
  · exact block_52
  · exact block_53
  · exact block_54
  · exact block_55
  · exact block_56
  · exact block_57
  · exact block_58
  · exact block_59
  · exact block_60
  · exact block_61
  · exact block_62
  · exact block_63
  · exact block_64

theorem check_ThmB_witnesses : BackfillPaper6.V3.ThmB_witnesses := by
  intro w hw
  have hn := (mem_S0_iff w).mp hw
  have hb := normalizedS0_bound w hn
  let b : Fin 65 := ⟨w / 256, by omega⟩
  let i : Fin 256 := ⟨w % 256, Nat.mod_lt w (by decide)⟩
  have heq : 256 * b.val + i.val = w := by
    dsimp only [b, i]
    omega
  have hlocal : normalizedS0 (256 * b.val + i.val) := by
    rw [heq]
    exact hn
  have hwitness := all_blocks b i hlocal
  rw [heq] at hwitness
  exact hwitness

end Paper6S0Witnesses

#print axioms Paper6S0Witnesses.all_blocks
#print axioms Paper6S0Witnesses.check_ThmB_witnesses
