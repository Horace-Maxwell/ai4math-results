import Research.Backfill.Paper6.Calib162Part04

/-! Unverified candidate: weight 162, point blocks 40 through 47. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block40 : blockCount masks162 2560 = 1 := by
  decide +kernel

theorem calib162_prefix41 : countPrefix masks162 2624 = 69 := by
  calc
    countPrefix masks162 2624 = countPrefix masks162 2560 + blockCount masks162 2560 :=
      prefix_step masks162 2560
    _ = 69 := by rw [calib162_prefix40, calib162_block40]

theorem calib162_block41 : blockCount masks162 2624 = 1 := by
  decide +kernel

theorem calib162_prefix42 : countPrefix masks162 2688 = 70 := by
  calc
    countPrefix masks162 2688 = countPrefix masks162 2624 + blockCount masks162 2624 :=
      prefix_step masks162 2624
    _ = 70 := by rw [calib162_prefix41, calib162_block41]

theorem calib162_block42 : blockCount masks162 2688 = 7 := by
  decide +kernel

theorem calib162_prefix43 : countPrefix masks162 2752 = 77 := by
  calc
    countPrefix masks162 2752 = countPrefix masks162 2688 + blockCount masks162 2688 :=
      prefix_step masks162 2688
    _ = 77 := by rw [calib162_prefix42, calib162_block42]

theorem calib162_block43 : blockCount masks162 2752 = 9 := by
  decide +kernel

theorem calib162_prefix44 : countPrefix masks162 2816 = 86 := by
  calc
    countPrefix masks162 2816 = countPrefix masks162 2752 + blockCount masks162 2752 :=
      prefix_step masks162 2752
    _ = 86 := by rw [calib162_prefix43, calib162_block43]

theorem calib162_block44 : blockCount masks162 2816 = 1 := by
  decide +kernel

theorem calib162_prefix45 : countPrefix masks162 2880 = 87 := by
  calc
    countPrefix masks162 2880 = countPrefix masks162 2816 + blockCount masks162 2816 :=
      prefix_step masks162 2816
    _ = 87 := by rw [calib162_prefix44, calib162_block44]

theorem calib162_block45 : blockCount masks162 2880 = 1 := by
  decide +kernel

theorem calib162_prefix46 : countPrefix masks162 2944 = 88 := by
  calc
    countPrefix masks162 2944 = countPrefix masks162 2880 + blockCount masks162 2880 :=
      prefix_step masks162 2880
    _ = 88 := by rw [calib162_prefix45, calib162_block45]

theorem calib162_block46 : blockCount masks162 2944 = 7 := by
  decide +kernel

theorem calib162_prefix47 : countPrefix masks162 3008 = 95 := by
  calc
    countPrefix masks162 3008 = countPrefix masks162 2944 + blockCount masks162 2944 :=
      prefix_step masks162 2944
    _ = 95 := by rw [calib162_prefix46, calib162_block46]

theorem calib162_block47 : blockCount masks162 3008 = 9 := by
  decide +kernel

theorem calib162_prefix48 : countPrefix masks162 3072 = 104 := by
  calc
    countPrefix masks162 3072 = countPrefix masks162 3008 + blockCount masks162 3008 :=
      prefix_step masks162 3008
    _ = 104 := by rw [calib162_prefix47, calib162_block47]


end Paper6Calib

#print axioms Paper6Calib.calib162_block40
#print axioms Paper6Calib.calib162_prefix41
#print axioms Paper6Calib.calib162_block41
#print axioms Paper6Calib.calib162_prefix42
#print axioms Paper6Calib.calib162_block42
#print axioms Paper6Calib.calib162_prefix43
#print axioms Paper6Calib.calib162_block43
#print axioms Paper6Calib.calib162_prefix44
#print axioms Paper6Calib.calib162_block44
#print axioms Paper6Calib.calib162_prefix45
#print axioms Paper6Calib.calib162_block45
#print axioms Paper6Calib.calib162_prefix46
#print axioms Paper6Calib.calib162_block46
#print axioms Paper6Calib.calib162_prefix47
#print axioms Paper6Calib.calib162_block47
#print axioms Paper6Calib.calib162_prefix48
