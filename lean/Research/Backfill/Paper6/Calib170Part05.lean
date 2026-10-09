import Research.Backfill.Paper6.Calib170Part04

/-! Weight 170, blocks 40 through 47. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block40 : blockCount masks170 2560 = 2 := by
  decide +kernel

theorem calib170_prefix41 : countPrefix masks170 2624 = 66 := by
  calc
    countPrefix masks170 2624 = countPrefix masks170 2560 + blockCount masks170 2560 :=
      prefix_step masks170 2560
    _ = 66 := by rw [calib170_prefix40, calib170_block40]

theorem calib170_block41 : blockCount masks170 2624 = 10 := by
  decide +kernel

theorem calib170_prefix42 : countPrefix masks170 2688 = 76 := by
  calc
    countPrefix masks170 2688 = countPrefix masks170 2624 + blockCount masks170 2624 :=
      prefix_step masks170 2624
    _ = 76 := by rw [calib170_prefix41, calib170_block41]

theorem calib170_block42 : blockCount masks170 2688 = 2 := by
  decide +kernel

theorem calib170_prefix43 : countPrefix masks170 2752 = 78 := by
  calc
    countPrefix masks170 2752 = countPrefix masks170 2688 + blockCount masks170 2688 :=
      prefix_step masks170 2688
    _ = 78 := by rw [calib170_prefix42, calib170_block42]

theorem calib170_block43 : blockCount masks170 2752 = 2 := by
  decide +kernel

theorem calib170_prefix44 : countPrefix masks170 2816 = 80 := by
  calc
    countPrefix masks170 2816 = countPrefix masks170 2752 + blockCount masks170 2752 :=
      prefix_step masks170 2752
    _ = 80 := by rw [calib170_prefix43, calib170_block43]

theorem calib170_block44 : blockCount masks170 2816 = 2 := by
  decide +kernel

theorem calib170_prefix45 : countPrefix masks170 2880 = 82 := by
  calc
    countPrefix masks170 2880 = countPrefix masks170 2816 + blockCount masks170 2816 :=
      prefix_step masks170 2816
    _ = 82 := by rw [calib170_prefix44, calib170_block44]

theorem calib170_block45 : blockCount masks170 2880 = 10 := by
  decide +kernel

theorem calib170_prefix46 : countPrefix masks170 2944 = 92 := by
  calc
    countPrefix masks170 2944 = countPrefix masks170 2880 + blockCount masks170 2880 :=
      prefix_step masks170 2880
    _ = 92 := by rw [calib170_prefix45, calib170_block45]

theorem calib170_block46 : blockCount masks170 2944 = 2 := by
  decide +kernel

theorem calib170_prefix47 : countPrefix masks170 3008 = 94 := by
  calc
    countPrefix masks170 3008 = countPrefix masks170 2944 + blockCount masks170 2944 :=
      prefix_step masks170 2944
    _ = 94 := by rw [calib170_prefix46, calib170_block46]

theorem calib170_block47 : blockCount masks170 3008 = 2 := by
  decide +kernel

theorem calib170_prefix48 : countPrefix masks170 3072 = 96 := by
  calc
    countPrefix masks170 3072 = countPrefix masks170 3008 + blockCount masks170 3008 :=
      prefix_step masks170 3008
    _ = 96 := by rw [calib170_prefix47, calib170_block47]


end Paper6Calib

#print axioms Paper6Calib.calib170_block40
#print axioms Paper6Calib.calib170_prefix41
#print axioms Paper6Calib.calib170_block41
#print axioms Paper6Calib.calib170_prefix42
#print axioms Paper6Calib.calib170_block42
#print axioms Paper6Calib.calib170_prefix43
#print axioms Paper6Calib.calib170_block43
#print axioms Paper6Calib.calib170_prefix44
#print axioms Paper6Calib.calib170_block44
#print axioms Paper6Calib.calib170_prefix45
#print axioms Paper6Calib.calib170_block45
#print axioms Paper6Calib.calib170_prefix46
#print axioms Paper6Calib.calib170_block46
#print axioms Paper6Calib.calib170_prefix47
#print axioms Paper6Calib.calib170_block47
#print axioms Paper6Calib.calib170_prefix48
