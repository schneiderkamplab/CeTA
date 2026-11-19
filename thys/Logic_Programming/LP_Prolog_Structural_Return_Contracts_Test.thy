theory LP_Prolog_Structural_Return_Contracts_Test
 imports LP_Prolog_Structural_Return_Contracts
begin

definition lpp_return_contract_test where
 "lpp_return_contract_test = LPPRContract 1 2 1
 [LPPRListEffect (True,0) (False,1) 0, LPPRLeafFreeReplacements 0]
 [LPPRRigidity (True,0) (False,1), LPPRTree (False,1)]"
definition lpp_return_contract_test_receipts where
 "lpp_return_contract_test_receipts = [LPPRListAsLeaf 0,LPPRDeriveRigidity 0 2,LPPRDeriveFinite 1]"

lemma lpp_return_contract_test_passes:
 "lpp_check_structural_return_contract lpp_return_contract_test lpp_return_contract_test_receipts"
 by (simp add: lpp_return_contract_test_def lpp_return_contract_test_receipts_def lpp_structural_return_wellformed_def)

lemma lpp_return_contract_missing_condition_rejected:
 "\<not> lpp_check_structural_return_contract
 (LPPRContract 1 2 1 [LPPRListEffect (True,0) (False,1) 0]
 [LPPRRigidity (True,0) (False,1)]) lpp_return_contract_test_receipts"
 by (simp add: lpp_return_contract_test_receipts_def lpp_structural_return_wellformed_def)

lemma lpp_return_contract_wrong_registry_rejected:
 "lpp_structural_return_infer [LPPRLeafEffect (True,0) (False,1) 0,LPPRLeafFreeReplacements 1]
 (LPPRDeriveRigidity 0 1) = None"
 by simp

lemma lpp_return_contract_future_reference_rejected:
 "lpp_structural_return_infer [LPPRTree (True,0)] (LPPRKnown 1) = None"
 by simp

lemma lpp_return_contract_spine_not_tree:
 "\<not> lpp_check_structural_return_contract
 (LPPRContract 1 1 0 [LPPRSpine (True,0)] [LPPRTree (True,0)]) []"
 by (simp add: lpp_structural_return_wellformed_def)

lemma lpp_return_contract_bad_coordinate_rejected:
 "\<not> lpp_check_structural_return_contract
 (LPPRContract 1 1 0 [LPPRTree (True,1)] [LPPRTree (True,1)]) []"
 by (simp add: lpp_structural_return_wellformed_def)

lemma lpp_return_contract_saved_alternative_rejected:
 "\<not> lpp_check_structural_return_contract
 (LPPRContract 1 2 1 [] [LPPRRigidity (True,0) (False,1)]) lpp_return_contract_test_receipts"
 by (simp add: lpp_return_contract_test_receipts_def lpp_structural_return_wellformed_def)

lemma lpp_return_contract_transport_passes:
 "lpp_check_structural_return_transport lpp_return_contract_test [(True,2)] [(False,0),(False,3)]
 (LPPRContract 3 4 1
 [LPPRListEffect (True,2) (False,3) 0, LPPRLeafFreeReplacements 0]
 [LPPRRigidity (True,2) (False,3), LPPRTree (False,3)])"
 by (simp add: lpp_return_contract_test_def lpp_structural_return_wellformed_def
 lpp_return_coordinate_map_def)

lemma lpp_return_contract_transport_missing_condition_rejected:
 "\<not> lpp_check_structural_return_transport lpp_return_contract_test [(True,2)] [(False,0),(False,3)]
 (LPPRContract 3 4 1
 [LPPRListEffect (True,2) (False,3) 0]
 [LPPRRigidity (True,2) (False,3), LPPRTree (False,3)])"
 by (simp add: lpp_return_contract_test_def lpp_structural_return_wellformed_def
 lpp_return_coordinate_map_def)

lemma lpp_return_contract_resumed_input_transport:
 "lpp_check_structural_return_transport lpp_return_contract_test
 [(True,0)] [(True,0),(True,1)]
 (LPPRContract 2 0 1
 [LPPRListEffect (True,0) (True,1) 0, LPPRLeafFreeReplacements 0]
 [LPPRRigidity (True,0) (True,1), LPPRTree (True,1)])"
 by (simp add: lpp_return_contract_test_def lpp_structural_return_wellformed_def
 lpp_return_coordinate_map_def)

lemma lpp_return_contract_list_spines:
 "lpp_check_structural_return_contract
 (LPPRContract 1 2 1 [LPPRListEffect (True,0) (False,1) 0]
 [LPPRSpine (True,0), LPPRSpine (False,1)]) [LPPRListSpine 0 True,LPPRListSpine 1 False]"
 by (simp add: lpp_structural_return_wellformed_def)

lemma lpp_return_contract_leaf_not_spine:
 "lpp_structural_return_infer [LPPRLeafEffect (True,0) (False,1) 0]
 (LPPRListSpine 0 False) = None"
 by simp

lemma lpp_return_contract_spine_missing_effect:
 "lpp_structural_return_infer [] (LPPRListSpine 0 False) = None"
 by simp

lemma lpp_return_contract_attached_leaf_list:
 "lpp_check_structural_return_contract
 (LPPRContract 1 2 1
 [LPPRLeafEffect (True,0) (False,1) 0, LPPRSpine (True,0), LPPRLeafFreeReplacements 0]
 [LPPRListEffect (True,0) (False,1) 0, LPPRSpine (False,1), LPPRRigidity (True,0) (False,1)])
 [LPPRLeafAsList 0 1, LPPRListSpine 0 False, LPPRDeriveRigidity 2 4]"
 by (simp add: lpp_structural_return_wellformed_def)

lemma lpp_return_contract_wrong_spine_rejected:
 "lpp_structural_return_infer [LPPRLeafEffect (True,0) (False,1) 0,LPPRSpine (False,1)]
 (LPPRLeafAsList 0 1) = None"
 by simp

lemma lpp_return_contract_tree_not_spine_rejected:
 "lpp_structural_return_infer [LPPRLeafEffect (True,0) (False,1) 0,LPPRTree (True,0)]
 (LPPRLeafAsList 0 1) = None"
 by simp

end
