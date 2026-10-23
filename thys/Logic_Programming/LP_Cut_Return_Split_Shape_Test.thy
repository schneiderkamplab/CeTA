theory LP_Cut_Return_Split_Shape_Test
  imports LP_Cut_Return_Split_Shape
begin

definition return_split_pre :: "string lpc_term lp_cut_goal list" where
  "return_split_pre = [LPCAtom (Fun (LPCUser ''p'') [Var ''X'',Var ''Y''])]"
definition return_split_rest :: "string lpc_term lp_cut_goal list" where
  "return_split_rest = [LPCAtom (Fun (LPCUser ''q'') [Var ''Y'']),LPCCut 3]"
definition return_split_original :: "(string lpc_term lp_cut_entry \<times> string lpc_term list) list" where
  "return_split_original = [(LPCGoals (return_split_pre@return_split_rest),[Var ''X''])]"

lemma return_split_keeps_continuation_only_variable:
  "lpc_check_return_split_shape [(''Y'',1)] [0] return_split_pre return_split_rest
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

lemma return_split_rejects_wrong_route:
  "\<not>lpc_check_return_split_shape [(''Y'',0)] [0] return_split_pre return_split_rest
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

lemma return_split_rejects_missing_route:
  "\<not>lpc_check_return_split_shape [] [0] return_split_pre return_split_rest
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

lemma return_split_rejects_changed_output:
  "\<not>lpc_check_return_split_shape [(''Y'',1)] [1] return_split_pre return_split_rest
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

lemma return_split_rejects_dropped_continuation:
  "\<not>lpc_check_return_split_shape [] [0] return_split_pre []
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

lemma return_split_rejects_out_of_bounds:
  "\<not>lpc_check_return_split_shape [(''Y'',2)] [0] return_split_pre return_split_rest
    [Var ''X'',Var ''Y''] return_split_original"
  by eval

end
