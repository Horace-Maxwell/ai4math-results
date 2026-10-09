import Research.Backfill.Paper6.CalibBasic

/-! Historical ANF data for weight 166. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

def masks166 : List ℕ :=
  [72, 73, 74, 75, 76, 77, 78, 79, 200, 201, 202, 203, 328, 329, 330, 331,
   1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1224, 1225, 1226, 1227, 1352, 1353, 1354, 1355,
   2120, 2122, 2124, 2126, 2248, 2250, 2312, 2314, 2321, 2323, 2328, 2330, 2344, 2346, 2353, 2355,
   2360, 2362, 2385, 2387, 2392, 2394, 2408, 2416, 2432, 2433, 2435, 2442, 2448, 2464, 2465, 2467,
   2474, 2480, 2496, 2497, 2499, 2506, 2512, 2528, 2824, 2826, 2833, 2835, 2840, 2842, 2856, 2858,
   2864, 2866, 2888, 2890, 2896, 2898, 2920, 2928, 2944, 2945, 2947, 2954, 2960, 2978, 2984, 2992,
   3010, 3016, 3024, 3040, 3144, 3146, 3148, 3150, 3272, 3274, 3328, 3330, 3360, 3362, 3392, 3394,
   3400, 3402, 3424, 3456, 3488, 3520, 3840, 3842, 3872, 3874, 3904, 3906, 3936, 3968, 4000, 4032]

theorem masks166_bound : ∀ s ∈ masks166, s < 2 ^ 12 := by
  decide +kernel

theorem masks166_degree : masks166.all (fun s => decide (degNat s ≤ 6)) = true := by
  decide +kernel

end Paper6Calib

#print axioms Paper6Calib.masks166_bound
#print axioms Paper6Calib.masks166_degree
