import Research.Backfill.Paper6.Calib166Part00

/-! Weight 166, blocks 8 through 15. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block08 : blockCount masks166 512 = 0 := by
  decide +kernel

theorem calib166_prefix09 : countPrefix masks166 576 = 16 := by
  calc
    countPrefix masks166 576 = countPrefix masks166 512 + blockCount masks166 512 :=
      prefix_step masks166 512
    _ = 16 := by rw [calib166_prefix08, calib166_block08]

theorem calib166_block09 : blockCount masks166 576 = 4 := by
  decide +kernel

theorem calib166_prefix10 : countPrefix masks166 640 = 20 := by
  calc
    countPrefix masks166 640 = countPrefix masks166 576 + blockCount masks166 576 :=
      prefix_step masks166 576
    _ = 20 := by rw [calib166_prefix09, calib166_block09]

theorem calib166_block10 : blockCount masks166 640 = 0 := by
  decide +kernel

theorem calib166_prefix11 : countPrefix masks166 704 = 20 := by
  calc
    countPrefix masks166 704 = countPrefix masks166 640 + blockCount masks166 640 :=
      prefix_step masks166 640
    _ = 20 := by rw [calib166_prefix10, calib166_block10]

theorem calib166_block11 : blockCount masks166 704 = 4 := by
  decide +kernel

theorem calib166_prefix12 : countPrefix masks166 768 = 24 := by
  calc
    countPrefix masks166 768 = countPrefix masks166 704 + blockCount masks166 704 :=
      prefix_step masks166 704
    _ = 24 := by rw [calib166_prefix11, calib166_block11]

theorem calib166_block12 : blockCount masks166 768 = 0 := by
  decide +kernel

theorem calib166_prefix13 : countPrefix masks166 832 = 24 := by
  calc
    countPrefix masks166 832 = countPrefix masks166 768 + blockCount masks166 768 :=
      prefix_step masks166 768
    _ = 24 := by rw [calib166_prefix12, calib166_block12]

theorem calib166_block13 : blockCount masks166 832 = 4 := by
  decide +kernel

theorem calib166_prefix14 : countPrefix masks166 896 = 28 := by
  calc
    countPrefix masks166 896 = countPrefix masks166 832 + blockCount masks166 832 :=
      prefix_step masks166 832
    _ = 28 := by rw [calib166_prefix13, calib166_block13]

theorem calib166_block14 : blockCount masks166 896 = 0 := by
  decide +kernel

theorem calib166_prefix15 : countPrefix masks166 960 = 28 := by
  calc
    countPrefix masks166 960 = countPrefix masks166 896 + blockCount masks166 896 :=
      prefix_step masks166 896
    _ = 28 := by rw [calib166_prefix14, calib166_block14]

theorem calib166_block15 : blockCount masks166 960 = 4 := by
  decide +kernel

theorem calib166_prefix16 : countPrefix masks166 1024 = 32 := by
  calc
    countPrefix masks166 1024 = countPrefix masks166 960 + blockCount masks166 960 :=
      prefix_step masks166 960
    _ = 32 := by rw [calib166_prefix15, calib166_block15]


end Paper6Calib

#print axioms Paper6Calib.calib166_block08
#print axioms Paper6Calib.calib166_prefix09
#print axioms Paper6Calib.calib166_block09
#print axioms Paper6Calib.calib166_prefix10
#print axioms Paper6Calib.calib166_block10
#print axioms Paper6Calib.calib166_prefix11
#print axioms Paper6Calib.calib166_block11
#print axioms Paper6Calib.calib166_prefix12
#print axioms Paper6Calib.calib166_block12
#print axioms Paper6Calib.calib166_prefix13
#print axioms Paper6Calib.calib166_block13
#print axioms Paper6Calib.calib166_prefix14
#print axioms Paper6Calib.calib166_block14
#print axioms Paper6Calib.calib166_prefix15
#print axioms Paper6Calib.calib166_block15
#print axioms Paper6Calib.calib166_prefix16
