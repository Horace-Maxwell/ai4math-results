import Research.Backfill.Paper6.Calib174Part04

/-! Weight 174, blocks 40 through 47. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block40 : blockCount masks174 2560 = 2 := by
  decide +kernel

theorem calib174_prefix41 : countPrefix masks174 2624 = 66 := by
  calc
    countPrefix masks174 2624 = countPrefix masks174 2560 + blockCount masks174 2560 :=
      prefix_step masks174 2560
    _ = 66 := by rw [calib174_prefix40, calib174_block40]

theorem calib174_block41 : blockCount masks174 2624 = 10 := by
  decide +kernel

theorem calib174_prefix42 : countPrefix masks174 2688 = 76 := by
  calc
    countPrefix masks174 2688 = countPrefix masks174 2624 + blockCount masks174 2624 :=
      prefix_step masks174 2624
    _ = 76 := by rw [calib174_prefix41, calib174_block41]

theorem calib174_block42 : blockCount masks174 2688 = 6 := by
  decide +kernel

theorem calib174_prefix43 : countPrefix masks174 2752 = 82 := by
  calc
    countPrefix masks174 2752 = countPrefix masks174 2688 + blockCount masks174 2688 :=
      prefix_step masks174 2688
    _ = 82 := by rw [calib174_prefix42, calib174_block42]

theorem calib174_block43 : blockCount masks174 2752 = 6 := by
  decide +kernel

theorem calib174_prefix44 : countPrefix masks174 2816 = 88 := by
  calc
    countPrefix masks174 2816 = countPrefix masks174 2752 + blockCount masks174 2752 :=
      prefix_step masks174 2752
    _ = 88 := by rw [calib174_prefix43, calib174_block43]

theorem calib174_block44 : blockCount masks174 2816 = 6 := by
  decide +kernel

theorem calib174_prefix45 : countPrefix masks174 2880 = 94 := by
  calc
    countPrefix masks174 2880 = countPrefix masks174 2816 + blockCount masks174 2816 :=
      prefix_step masks174 2816
    _ = 94 := by rw [calib174_prefix44, calib174_block44]

theorem calib174_block45 : blockCount masks174 2880 = 14 := by
  decide +kernel

theorem calib174_prefix46 : countPrefix masks174 2944 = 108 := by
  calc
    countPrefix masks174 2944 = countPrefix masks174 2880 + blockCount masks174 2880 :=
      prefix_step masks174 2880
    _ = 108 := by rw [calib174_prefix45, calib174_block45]

theorem calib174_block46 : blockCount masks174 2944 = 2 := by
  decide +kernel

theorem calib174_prefix47 : countPrefix masks174 3008 = 110 := by
  calc
    countPrefix masks174 3008 = countPrefix masks174 2944 + blockCount masks174 2944 :=
      prefix_step masks174 2944
    _ = 110 := by rw [calib174_prefix46, calib174_block46]

theorem calib174_block47 : blockCount masks174 3008 = 2 := by
  decide +kernel

theorem calib174_prefix48 : countPrefix masks174 3072 = 112 := by
  calc
    countPrefix masks174 3072 = countPrefix masks174 3008 + blockCount masks174 3008 :=
      prefix_step masks174 3008
    _ = 112 := by rw [calib174_prefix47, calib174_block47]


end Paper6Calib

#print axioms Paper6Calib.calib174_block40
#print axioms Paper6Calib.calib174_prefix41
#print axioms Paper6Calib.calib174_block41
#print axioms Paper6Calib.calib174_prefix42
#print axioms Paper6Calib.calib174_block42
#print axioms Paper6Calib.calib174_prefix43
#print axioms Paper6Calib.calib174_block43
#print axioms Paper6Calib.calib174_prefix44
#print axioms Paper6Calib.calib174_block44
#print axioms Paper6Calib.calib174_prefix45
#print axioms Paper6Calib.calib174_block45
#print axioms Paper6Calib.calib174_prefix46
#print axioms Paper6Calib.calib174_block46
#print axioms Paper6Calib.calib174_prefix47
#print axioms Paper6Calib.calib174_block47
#print axioms Paper6Calib.calib174_prefix48
