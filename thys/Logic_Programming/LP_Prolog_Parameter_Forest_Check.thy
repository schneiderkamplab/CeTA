theory LP_Prolog_Parameter_Forest_Check
 imports LP_Prolog_Parameter_Leaf_Prefix LP_Answer_Clause_Rename
begin

definition lpp_parameter_forest_program where
 "lpp_parameter_forest_program gp gs lr ls list_predicate er es f g =
  lpp_ground_observation_program gp gs @ lpp_parameter_leaf_program lr ls f g @
  lpp_list_leaf_clauses list_predicate er 1 @ lpp_parameter_leaf_program er es f g"

definition lpp_check_parameter_forest_program where
 "lpp_check_parameter_forest_program Q predicate_map symbol_map gp gs lr ls list_predicate er es f g receipts =
  lp_answer_check_renamed_program
   (lp_answer_map_program predicate_map symbol_map
    (lpp_parameter_forest_program gp gs lr ls list_predicate er es f g)) Q receipts"

theorem lpp_checked_parameter_forest_prefix:
 assumes checked: "lpp_check_parameter_forest_program Q predicate_map symbol_map
   gp gs lr ls list_predicate er es f g receipts"
 and ground: "vars_term c = {}"
 and leaf_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c) s leaf_value"
 and leaf_observed: "lpp_runtime_structure leaf_value t"
 and list_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c)
    (lpp_structural_argument_list xs) list_value"
 and list_observed: "lpp_runtime_structure list_value ys"
 shows "((map (lp_answer_map_iatom predicate_map symbol_map)
   (lpp_ground_tree_goal gp (lpp_structure_template c)#
    lpp_leaf_relation_goal lr s t
     [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#
    lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs) ys
     [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest),
    \<lambda>x. map_lp_iterm symbol_map id (env x)),
   (map (lp_answer_map_iatom predicate_map symbol_map) rest,
    \<lambda>x. map_lp_iterm symbol_map id (env x)))\<in>(lp_seg_answer_step Q)\<^sup>*"
proof -
 let ?P = "lpp_parameter_forest_program gp gs lr ls list_predicate er es f g"
 have ground_core: "set (lpp_ground_observation_program gp gs) \<subseteq> set ?P"
 and leaf_core: "set (lpp_parameter_leaf_program lr ls f g) \<subseteq> set ?P"
 and list_core: "set (lpp_list_leaf_clauses list_predicate er 1) \<subseteq> set ?P"
 and element_core: "set (lpp_parameter_leaf_program er es f g) \<subseteq> set ?P"
  by (auto simp: lpp_parameter_forest_program_def)
 have renamed: "lp_answer_check_renamed_program (lp_answer_map_program predicate_map symbol_map ?P) Q receipts"
  using checked by (simp add: lpp_check_parameter_forest_program_def)
 show ?thesis
  by (rule lp_answer_checked_renamed_path[OF renamed], rule lp_answer_symbol_path,
      rule lpp_runtime_parameter_forest_guarded_prefix[OF ground_core leaf_core list_core element_core
        ground leaf_effect leaf_observed list_effect list_observed])
qed

ML \<open>
val checked = @{thms lpp_checked_parameter_forest_prefix};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked forest prefix" else ();
\<close>
end
