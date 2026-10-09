import Research.Backfill.Paper6.Calib166Part04

/-! Weight 166, blocks 40 through 47. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block40 : blockCount masks166 2560 = 0 := by
  decide +kernel

theorem calib166_prefix41 : countPrefix masks166 2624 = 82 := by
  calc
    countPrefix masks166 2624 = countPrefix masks166 2560 + blockCount masks166 2560 :=
      prefix_step masks166 2560
    _ = 82 := by rw [calib166_prefix40, calib166_block40]

theorem calib166_block41 : blockCount masks166 2624 = 4 := by
  decide +kernel

theorem calib166_prefix42 : countPrefix masks166 2688 = 86 := by
  calc
    countPrefix masks166 2688 = countPrefix masks166 2624 + blockCount masks166 2624 :=
      prefix_step masks166 2624
    _ = 86 := by rw [calib166_prefix41, calib166_block41]

theorem calib166_block42 : blockCount masks166 2688 = 0 := by
  decide +kernel

theorem calib166_prefix43 : countPrefix masks166 2752 = 86 := by
  calc
    countPrefix masks166 2752 = countPrefix masks166 2688 + blockCount masks166 2688 :=
      prefix_step masks166 2688
    _ = 86 := by rw [calib166_prefix42, calib166_block42]

theorem calib166_block43 : blockCount masks166 2752 = 4 := by
  decide +kernel

theorem calib166_prefix44 : countPrefix masks166 2816 = 90 := by
  calc
    countPrefix masks166 2816 = countPrefix masks166 2752 + blockCount masks166 2752 :=
      prefix_step masks166 2752
    _ = 90 := by rw [calib166_prefix43, calib166_block43]

theorem calib166_block44 : blockCount masks166 2816 = 4 := by
  decide +kernel

theorem calib166_prefix45 : countPrefix masks166 2880 = 94 := by
  calc
    countPrefix masks166 2880 = countPrefix masks166 2816 + blockCount masks166 2816 :=
      prefix_step masks166 2816
    _ = 94 := by rw [calib166_prefix44, calib166_block44]

theorem calib166_block45 : blockCount masks166 2880 = 6 := by
  decide +kernel

theorem calib166_prefix46 : countPrefix masks166 2944 = 100 := by
  calc
    countPrefix masks166 2944 = countPrefix masks166 2880 + blockCount masks166 2880 :=
      prefix_step masks166 2880
    _ = 100 := by rw [calib166_prefix45, calib166_block45]

theorem calib166_block46 : blockCount masks166 2944 = 4 := by
  decide +kernel

theorem calib166_prefix47 : countPrefix masks166 3008 = 104 := by
  calc
    countPrefix masks166 3008 = countPrefix masks166 2944 + blockCount masks166 2944 :=
      prefix_step masks166 2944
    _ = 104 := by rw [calib166_prefix46, calib166_block46]

theorem calib166_block47 : blockCount masks166 3008 = 6 := by
  decide +kernel

theorem calib166_prefix48 : countPrefix masks166 3072 = 110 := by
  calc
    countPrefix masks166 3072 = countPrefix masks166 3008 + blockCount masks166 3008 :=
      prefix_step masks166 3008
    _ = 110 := by rw [calib166_prefix47, calib166_block47]


end Paper6Calib

#print axioms Paper6Calib.calib166_block40
#print axioms Paper6Calib.calib166_prefix41
#print axioms Paper6Calib.calib166_block41
#print axioms Paper6Calib.calib166_prefix42
#print axioms Paper6Calib.calib166_block42
#print axioms Paper6Calib.calib166_prefix43
#print axioms Paper6Calib.calib166_block43
#print axioms Paper6Calib.calib166_prefix44
#print axioms Paper6Calib.calib166_block44
#print axioms Paper6Calib.calib166_prefix45
#print axioms Paper6Calib.calib166_block45
#print axioms Paper6Calib.calib166_prefix46
#print axioms Paper6Calib.calib166_block46
#print axioms Paper6Calib.calib166_prefix47
#print axioms Paper6Calib.calib166_block47
#print axioms Paper6Calib.calib166_prefix48
