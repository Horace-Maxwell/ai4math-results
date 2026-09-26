import Research.ICGBridgeFinal

/-! Statement audit for the ICG spectral bridge: prints the final statements, the definitions
they depend on, and their axioms. -/

#check @ICGBridge.roldan_q3
#check @ICGBridge.roldan_q3_graph
#check @ICGBridge.energy_Dstar
#check @ICGBridge.energy_icgAdj_eq_exactEnergy
#check @ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft
#check @ICGBridge.eigenvalues_multiset_eq_dft
#check @ICGBridge.dft_connFun
#print ICGBridge.icgAdj
#print ICGBridge.energy
#print ICGBridge.Dstar
#print ICGBridge.icgGraph
#print SimpleGraph.circulantGraph
#check @ICGBridge.fin_sub_val_eq_emod
#print axioms ICGBridge.roldan_q3
#print axioms ICGBridge.roldan_q3_graph
#print axioms ICGBridge.energy_Dstar
#print axioms ICGBridge.energy_icgAdj_eq_exactEnergy
