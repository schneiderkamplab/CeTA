theory LP_Prolog_Helper_Return_Recipe_Controls
  imports LP_Prolog_Helper_Return_Recipe
begin

definition lpp_helper_control_recipe where
  "lpp_helper_control_recipe = \<lparr>lpphr_clause=0, lpphr_predicate=''3:combine'',
    lpphr_head=[''a'',''b'',''out''], lpphr_inputs=[''a'',''b''], lpphr_prefix=[],
    lpphr_output=''out'', lpphr_expression=LPPEAdd (LPPEVariable ''a'') (LPPEVariable ''b'')\<rparr>"
definition lpp_helper_control_clause where
  "lpp_helper_control_clause = (Fun (LPCUser ''3:combine'') (map Var [''a'',''b'',''out'']),
    [lpp_recurrence_goal (LPPRSet ''out'' (LPPEAdd (LPPEVariable ''a'') (LPPEVariable ''b'')))])"

lemma lpp_helper_control_positive:
  "lpp_check_helper_return_recipe [lpp_helper_control_clause] lpp_helper_control_recipe"
  by (simp add: lpp_check_helper_return_recipe_def lpp_helper_control_recipe_def
    lpp_helper_control_clause_def lp_cut_slice_def lpp_builtin_signature_def)

lemma lpp_helper_control_later_answer:
  "\<not>lpp_check_helper_return_recipe [lpp_helper_control_clause,lpp_helper_control_clause]
    lpp_helper_control_recipe"
  by (simp add: lpp_check_helper_return_recipe_def lpp_helper_control_recipe_def
    lpp_helper_control_clause_def lp_cut_slice_def)

lemma lpp_helper_control_missing_input:
  "\<not>lpp_check_helper_return_recipe [lpp_helper_control_clause]
    (lpp_helper_control_recipe\<lparr>lpphr_inputs:=[''a'']\<rparr>)"
  by (simp add: lpp_check_helper_return_recipe_def lpp_helper_control_recipe_def)

lemma lpp_helper_control_bound_output:
  "\<not>lpp_check_helper_return_recipe [lpp_helper_control_clause]
    (lpp_helper_control_recipe\<lparr>lpphr_inputs:=[''a'',''b'',''out'']\<rparr>)"
  by (simp add: lpp_check_helper_return_recipe_def lpp_helper_control_recipe_def)

lemma lpp_helper_control_missing_body:
  "\<not>lpp_check_helper_return_recipe [(fst lpp_helper_control_clause,[])] lpp_helper_control_recipe"
  by (simp add: lpp_check_helper_return_recipe_def lpp_helper_control_recipe_def)

ML \<open>
val checked = [@{thm lpp_helper_control_positive}, @{thm lpp_helper_control_later_answer},
  @{thm lpp_helper_control_missing_input}, @{thm lpp_helper_control_bound_output},
  @{thm lpp_helper_control_missing_body}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper recipe controls" else ();
\<close>
end
