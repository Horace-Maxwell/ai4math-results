import Research.Backfill.Paper6.Calib174Part00

/-! Weight 174, blocks 8 through 15. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block08 : blockCount masks174 512 = 0 := by
  decide +kernel

theorem calib174_prefix09 : countPrefix masks174 576 = 16 := by
  calc
    countPrefix masks174 576 = countPrefix masks174 512 + blockCount masks174 512 :=
      prefix_step masks174 512
    _ = 16 := by rw [calib174_prefix08, calib174_block08]

theorem calib174_block09 : blockCount masks174 576 = 0 := by
  decide +kernel

theorem calib174_prefix10 : countPrefix masks174 640 = 16 := by
  calc
    countPrefix masks174 640 = countPrefix masks174 576 + blockCount masks174 576 :=
      prefix_step masks174 576
    _ = 16 := by rw [calib174_prefix09, calib174_block09]

theorem calib174_block10 : blockCount masks174 640 = 0 := by
  decide +kernel

theorem calib174_prefix11 : countPrefix masks174 704 = 16 := by
  calc
    countPrefix masks174 704 = countPrefix masks174 640 + blockCount masks174 640 :=
      prefix_step masks174 640
    _ = 16 := by rw [calib174_prefix10, calib174_block10]

theorem calib174_block11 : blockCount masks174 704 = 0 := by
  decide +kernel

theorem calib174_prefix12 : countPrefix masks174 768 = 16 := by
  calc
    countPrefix masks174 768 = countPrefix masks174 704 + blockCount masks174 704 :=
      prefix_step masks174 704
    _ = 16 := by rw [calib174_prefix11, calib174_block11]

theorem calib174_block12 : blockCount masks174 768 = 0 := by
  decide +kernel

theorem calib174_prefix13 : countPrefix masks174 832 = 16 := by
  calc
    countPrefix masks174 832 = countPrefix masks174 768 + blockCount masks174 768 :=
      prefix_step masks174 768
    _ = 16 := by rw [calib174_prefix12, calib174_block12]

theorem calib174_block13 : blockCount masks174 832 = 0 := by
  decide +kernel

theorem calib174_prefix14 : countPrefix masks174 896 = 16 := by
  calc
    countPrefix masks174 896 = countPrefix masks174 832 + blockCount masks174 832 :=
      prefix_step masks174 832
    _ = 16 := by rw [calib174_prefix13, calib174_block13]

theorem calib174_block14 : blockCount masks174 896 = 0 := by
  decide +kernel

theorem calib174_prefix15 : countPrefix masks174 960 = 16 := by
  calc
    countPrefix masks174 960 = countPrefix masks174 896 + blockCount masks174 896 :=
      prefix_step masks174 896
    _ = 16 := by rw [calib174_prefix14, calib174_block14]

theorem calib174_block15 : blockCount masks174 960 = 0 := by
  decide +kernel

theorem calib174_prefix16 : countPrefix masks174 1024 = 16 := by
  calc
    countPrefix masks174 1024 = countPrefix masks174 960 + blockCount masks174 960 :=
      prefix_step masks174 960
    _ = 16 := by rw [calib174_prefix15, calib174_block15]


end Paper6Calib

#print axioms Paper6Calib.calib174_block08
#print axioms Paper6Calib.calib174_prefix09
#print axioms Paper6Calib.calib174_block09
#print axioms Paper6Calib.calib174_prefix10
#print axioms Paper6Calib.calib174_block10
#print axioms Paper6Calib.calib174_prefix11
#print axioms Paper6Calib.calib174_block11
#print axioms Paper6Calib.calib174_prefix12
#print axioms Paper6Calib.calib174_block12
#print axioms Paper6Calib.calib174_prefix13
#print axioms Paper6Calib.calib174_block13
#print axioms Paper6Calib.calib174_prefix14
#print axioms Paper6Calib.calib174_block14
#print axioms Paper6Calib.calib174_prefix15
#print axioms Paper6Calib.calib174_block15
#print axioms Paper6Calib.calib174_prefix16
