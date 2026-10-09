import Research.Backfill.Paper6.Calib174Part06

/-! Weight 174, blocks 56 through 63. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block56 : blockCount masks174 3584 = 2 := by
  decide +kernel

theorem calib174_prefix57 : countPrefix masks174 3648 = 138 := by
  calc
    countPrefix masks174 3648 = countPrefix masks174 3584 + blockCount masks174 3584 :=
      prefix_step masks174 3584
    _ = 138 := by rw [calib174_prefix56, calib174_block56]

theorem calib174_block57 : blockCount masks174 3648 = 2 := by
  decide +kernel

theorem calib174_prefix58 : countPrefix masks174 3712 = 140 := by
  calc
    countPrefix masks174 3712 = countPrefix masks174 3648 + blockCount masks174 3648 :=
      prefix_step masks174 3648
    _ = 140 := by rw [calib174_prefix57, calib174_block57]

theorem calib174_block58 : blockCount masks174 3712 = 6 := by
  decide +kernel

theorem calib174_prefix59 : countPrefix masks174 3776 = 146 := by
  calc
    countPrefix masks174 3776 = countPrefix masks174 3712 + blockCount masks174 3712 :=
      prefix_step masks174 3712
    _ = 146 := by rw [calib174_prefix58, calib174_block58]

theorem calib174_block59 : blockCount masks174 3776 = 10 := by
  decide +kernel

theorem calib174_prefix60 : countPrefix masks174 3840 = 156 := by
  calc
    countPrefix masks174 3840 = countPrefix masks174 3776 + blockCount masks174 3776 :=
      prefix_step masks174 3776
    _ = 156 := by rw [calib174_prefix59, calib174_block59]

theorem calib174_block60 : blockCount masks174 3840 = 6 := by
  decide +kernel

theorem calib174_prefix61 : countPrefix masks174 3904 = 162 := by
  calc
    countPrefix masks174 3904 = countPrefix masks174 3840 + blockCount masks174 3840 :=
      prefix_step masks174 3840
    _ = 162 := by rw [calib174_prefix60, calib174_block60]

theorem calib174_block61 : blockCount masks174 3904 = 4 := by
  decide +kernel

theorem calib174_prefix62 : countPrefix masks174 3968 = 166 := by
  calc
    countPrefix masks174 3968 = countPrefix masks174 3904 + blockCount masks174 3904 :=
      prefix_step masks174 3904
    _ = 166 := by rw [calib174_prefix61, calib174_block61]

theorem calib174_block62 : blockCount masks174 3968 = 2 := by
  decide +kernel

theorem calib174_prefix63 : countPrefix masks174 4032 = 168 := by
  calc
    countPrefix masks174 4032 = countPrefix masks174 3968 + blockCount masks174 3968 :=
      prefix_step masks174 3968
    _ = 168 := by rw [calib174_prefix62, calib174_block62]

theorem calib174_block63 : blockCount masks174 4032 = 6 := by
  decide +kernel

theorem calib174_prefix64 : countPrefix masks174 4096 = 174 := by
  calc
    countPrefix masks174 4096 = countPrefix masks174 4032 + blockCount masks174 4032 :=
      prefix_step masks174 4032
    _ = 174 := by rw [calib174_prefix63, calib174_block63]


end Paper6Calib

#print axioms Paper6Calib.calib174_block56
#print axioms Paper6Calib.calib174_prefix57
#print axioms Paper6Calib.calib174_block57
#print axioms Paper6Calib.calib174_prefix58
#print axioms Paper6Calib.calib174_block58
#print axioms Paper6Calib.calib174_prefix59
#print axioms Paper6Calib.calib174_block59
#print axioms Paper6Calib.calib174_prefix60
#print axioms Paper6Calib.calib174_block60
#print axioms Paper6Calib.calib174_prefix61
#print axioms Paper6Calib.calib174_block61
#print axioms Paper6Calib.calib174_prefix62
#print axioms Paper6Calib.calib174_block62
#print axioms Paper6Calib.calib174_prefix63
#print axioms Paper6Calib.calib174_block63
#print axioms Paper6Calib.calib174_prefix64
