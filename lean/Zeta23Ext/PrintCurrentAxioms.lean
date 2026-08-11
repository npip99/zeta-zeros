import Zeta23Ext.Current
import Zeta23Ext.CertificateBridge
import Zeta23Ext.CurrentZetaAssembly

/-
Run with `lake env lean Zeta23Ext/PrintCurrentAxioms.lean` to audit the
Lean-checked current-result seams.  The two external inputs are propositions
in theorem arguments, not declared axioms.
-/

#print axioms Zeta23Ext.Weighted.paper_window_summation_250
#print axioms Zeta23Ext.SqrtProfile.block_defect_sqrt
#print axioms Zeta23Ext.ProfileSharpness.tendsto_actualDefect
#print axioms Zeta23Ext.CurrentBlockMatrix.paper_block_matrix
#print axioms Zeta23Ext.CurrentAveraging.current_averaged_defect_normalized
#print axioms Zeta23Ext.Current.target_lt_headline
#print axioms Zeta23Ext.Current.zeta_conditional_target
#print axioms Zeta23Ext.Current.zeta_conditional_target_cumulative
#print axioms Zeta23Ext.CertificateBridge.mainReportAccepted
#print axioms Zeta23Ext.CertificateBridge.fastReportAccepted
#print axioms Zeta23Ext.CertificateBridge.finiteWindowInputs_of_externalSoundness
#print axioms Zeta23Ext.CurrentAssembly.FiniteHeightInputs.toWeightedBlockDefectData
#print axioms Zeta23Ext.CurrentAssembly.AsymptoticInputs.target
#print axioms Zeta23Ext.CurrentZetaAssembly.toCurrentZetaAnalyticInputs
#print axioms Zeta23Ext.CurrentZetaAssembly.zeta_target
