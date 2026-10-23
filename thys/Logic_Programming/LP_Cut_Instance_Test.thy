theory LP_Cut_Instance_Test
  imports LP_Cut_Instance
begin

lemma checked_instance_does_not_invent_groundness:
  "\<not>lp_cut_check_instance ([]::(nat,string) term lp_cut_entry list) [] []
    [] [''X''] [] [] []"
  by (simp add: lp_cut_check_instance_def lp_cut_instance_subst_def)

lemma checked_instance_does_not_invent_guards:
  "\<not>lp_cut_check_instance ([]::(nat,string) term lp_cut_entry list) [] []
    [] [] [LPCEqGuard (Var ''X'') (Var ''Y'') True] [] []"
  by (simp add: lp_cut_check_instance_def lp_cut_instance_subst_def)

lemma checked_instance_keeps_saved_choices:
  "\<not>lp_cut_check_instance
    ([LPCGoals [LPCFail]]::(nat,string) term lp_cut_entry list) [] []
    [] [] [] [] []"
  by (simp add: lp_cut_check_instance_def lp_cut_state_map_def)

lemma checked_instance_scope_swap:
  "lp_cut_check_instance
    ([LPCGoals [LPCCut 7],LPCBarrier 7]::(nat,string) term lp_cut_entry list) [] []
    [LPCGoals [LPCCut 0],LPCBarrier 0] [] [] [] [(0,7)]"
  by (simp add: lp_cut_check_instance_def lp_cut_state_map_def lp_cut_scope_swap_def)

lemma checked_instance_does_not_merge_scopes:
  "\<not>lp_cut_check_instance
    ([LPCGoals [LPCCut 7],LPCBarrier 7]::(nat,string) term lp_cut_entry list) [] []
    [LPCGoals [LPCCut 0],LPCBarrier 1] [] [] [] [(0,7)]"
  by (simp add: lp_cut_check_instance_def lp_cut_state_map_def lp_cut_scope_swap_def)

end
