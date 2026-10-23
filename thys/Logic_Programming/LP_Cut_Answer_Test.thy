theory LP_Cut_Answer_Test
  imports LP_Cut_MGU_XML
begin

definition answer_test_nodes :: "string lpc_node list" where
  "answer_test_nodes = [
    \<lparr>lpcn_state=[LPCGoals [LPCAtom (Fun (LPCUser ''p'') [Var ''X'']),LPCCut 0]],
      lpcn_ground=[],lpcn_guards=[],lpcn_vars=[''X''],lpcn_pred=LPCUser ''entry''\<rparr>,
    \<lparr>lpcn_state=[LPCGoals [LPCCut 0]],
      lpcn_ground=[],lpcn_guards=[],lpcn_vars=[''X''],lpcn_pred=LPCUser ''continued''\<rparr>]"

definition answer_test_program :: "(string,string) lp_cut_program" where
  "answer_test_program = [(Fun (LPCUser ''p'') [Var ''X''],[])]"

definition answer_test_residual :: "(string lp_cut_symbol,string) lp_clause list" where
  "answer_test_residual = [((LPCTruth,[]),[]),((LPCUser ''p'',[Var ''X'']),[]),
    ((LPCUser ''entry'',[Var ''X'']),[(LPCUser ''p'',[Var ''X'']),(LPCUser ''continued'',[Var ''X''])])]"

definition answer_test_action :: "string lpc_action" where
  "answer_test_action = LPCAAnswerSplit [LPCAtom (Fun (LPCUser ''p'') [Var ''X''])] [LPCCut 0] [''p''] [] 1"

lemma answer_test_accept:
  "lpc_check_action 10 answer_test_program answer_test_residual answer_test_nodes
    (answer_test_nodes!0) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_mgu_accept:
  "lpc_mgu_check_action 10 answer_test_program answer_test_residual answer_test_nodes [[],[]]
    (answer_test_nodes!0) [] answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_missing_residual_rejected:
  "\<not> lpc_check_action 10 answer_test_program (take 2 answer_test_residual) answer_test_nodes
    (answer_test_nodes!0) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_unproved_ground_rejected:
  "\<not> lpc_check_action 10 answer_test_program answer_test_residual
    (answer_test_nodes[1 := (answer_test_nodes!1)\<lparr>lpcn_ground := [''X'']\<rparr>])
    (answer_test_nodes!0) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_unproved_free_rejected:
  "\<not> lpc_mgu_check_action 10 answer_test_program answer_test_residual answer_test_nodes [[],[''X'']]
    (answer_test_nodes!0) [] answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_lost_scope_rejected:
  "\<not> lpc_check_action 10 answer_test_program answer_test_residual
    (answer_test_nodes[1 := (answer_test_nodes!1)\<lparr>lpcn_state := [LPCGoals [LPCCut 1]]\<rparr>])
    (answer_test_nodes!0) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_incomplete_program_rejected:
  "\<not> lpc_check_action 10
    (answer_test_program @ [(Fun (LPCUser ''p'') [Var ''X''],[LPCMeta (Var ''X'')])])
    answer_test_residual answer_test_nodes (answer_test_nodes!0) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps lpc_mgu_check_action.simps; eval)

lemma answer_test_preserved_ground_accept:
  "lpc_check_action 10 answer_test_program answer_test_residual
    (answer_test_nodes[1 := (answer_test_nodes!1)\<lparr>lpcn_ground := [''X'']\<rparr>])
    ((answer_test_nodes!0)\<lparr>lpcn_ground := [''X'']\<rparr>) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps; eval)

lemma answer_test_preserved_negative_accept:
  "lpc_check_action 10 answer_test_program answer_test_residual
    (answer_test_nodes[1 := (answer_test_nodes!1)\<lparr>lpcn_guards := [LPCEqGuard (Var ''X'') (Fun (LPCUser ''a'') []) False]\<rparr>])
    ((answer_test_nodes!0)\<lparr>lpcn_guards := [LPCEqGuard (Var ''X'') (Fun (LPCUser ''a'') []) False]\<rparr>) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps; eval)

lemma answer_test_positive_guard_rejected:
  "\<not> lpc_check_action 10 answer_test_program answer_test_residual
    (answer_test_nodes[1 := (answer_test_nodes!1)\<lparr>lpcn_guards := [LPCEqGuard (Var ''X'') (Fun (LPCUser ''a'') []) True]\<rparr>])
    ((answer_test_nodes!0)\<lparr>lpcn_guards := [LPCEqGuard (Var ''X'') (Fun (LPCUser ''a'') []) True]\<rparr>) answer_test_action"
  by (simp only: answer_test_action_def lpc_check_action.simps; eval)

end
