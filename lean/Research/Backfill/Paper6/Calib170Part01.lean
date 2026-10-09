import Research.Backfill.Paper6.Calib170Part00

/-! Weight 170, blocks 8 through 15. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block08 : blockCount masks170 512 = 0 := by
  decide +kernel

theorem calib170_prefix09 : countPrefix masks170 576 = 16 := by
  calc
    countPrefix masks170 576 = countPrefix masks170 512 + blockCount masks170 512 :=
      prefix_step masks170 512
    _ = 16 := by rw [calib170_prefix08, calib170_block08]

theorem calib170_block09 : blockCount masks170 576 = 0 := by
  decide +kernel

theorem calib170_prefix10 : countPrefix masks170 640 = 16 := by
  calc
    countPrefix masks170 640 = countPrefix masks170 576 + blockCount masks170 576 :=
      prefix_step masks170 576
    _ = 16 := by rw [calib170_prefix09, calib170_block09]

theorem calib170_block10 : blockCount masks170 640 = 4 := by
  decide +kernel

theorem calib170_prefix11 : countPrefix masks170 704 = 20 := by
  calc
    countPrefix masks170 704 = countPrefix masks170 640 + blockCount masks170 640 :=
      prefix_step masks170 640
    _ = 20 := by rw [calib170_prefix10, calib170_block10]

theorem calib170_block11 : blockCount masks170 704 = 4 := by
  decide +kernel

theorem calib170_prefix12 : countPrefix masks170 768 = 24 := by
  calc
    countPrefix masks170 768 = countPrefix masks170 704 + blockCount masks170 704 :=
      prefix_step masks170 704
    _ = 24 := by rw [calib170_prefix11, calib170_block11]

theorem calib170_block12 : blockCount masks170 768 = 4 := by
  decide +kernel

theorem calib170_prefix13 : countPrefix masks170 832 = 28 := by
  calc
    countPrefix masks170 832 = countPrefix masks170 768 + blockCount masks170 768 :=
      prefix_step masks170 768
    _ = 28 := by rw [calib170_prefix12, calib170_block12]

theorem calib170_block13 : blockCount masks170 832 = 4 := by
  decide +kernel

theorem calib170_prefix14 : countPrefix masks170 896 = 32 := by
  calc
    countPrefix masks170 896 = countPrefix masks170 832 + blockCount masks170 832 :=
      prefix_step masks170 832
    _ = 32 := by rw [calib170_prefix13, calib170_block13]

theorem calib170_block14 : blockCount masks170 896 = 0 := by
  decide +kernel

theorem calib170_prefix15 : countPrefix masks170 960 = 32 := by
  calc
    countPrefix masks170 960 = countPrefix masks170 896 + blockCount masks170 896 :=
      prefix_step masks170 896
    _ = 32 := by rw [calib170_prefix14, calib170_block14]

theorem calib170_block15 : blockCount masks170 960 = 0 := by
  decide +kernel

theorem calib170_prefix16 : countPrefix masks170 1024 = 32 := by
  calc
    countPrefix masks170 1024 = countPrefix masks170 960 + blockCount masks170 960 :=
      prefix_step masks170 960
    _ = 32 := by rw [calib170_prefix15, calib170_block15]


end Paper6Calib

#print axioms Paper6Calib.calib170_block08
#print axioms Paper6Calib.calib170_prefix09
#print axioms Paper6Calib.calib170_block09
#print axioms Paper6Calib.calib170_prefix10
#print axioms Paper6Calib.calib170_block10
#print axioms Paper6Calib.calib170_prefix11
#print axioms Paper6Calib.calib170_block11
#print axioms Paper6Calib.calib170_prefix12
#print axioms Paper6Calib.calib170_block12
#print axioms Paper6Calib.calib170_prefix13
#print axioms Paper6Calib.calib170_block13
#print axioms Paper6Calib.calib170_prefix14
#print axioms Paper6Calib.calib170_block14
#print axioms Paper6Calib.calib170_prefix15
#print axioms Paper6Calib.calib170_block15
#print axioms Paper6Calib.calib170_prefix16
