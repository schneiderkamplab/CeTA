theory LP_Prolog_Parameter_Return_Prefix
 imports LP_Prolog_Parameter_Forest_Check LP_Prolog_Parameter_Return_Composition
begin

text \<open>Compose a checked residual helper family with effects established
under a returned parameter. The ordered residual prefix still uses its original
parameter coordinate. Its relation to the returned parameter is an explicit
source obligation, as are both actual runtime effects.\<close>

theorem lpp_checked_parameter_forest_return_prefix:
 assumes checked: "lpp_check_parameter_forest_program Q predicate_map symbol_map
   gp gs lr ls list_predicate er es f g receipts"
 and ground: "vars_term c = {}"
 and returned: "lpp_parameter_return c d"
 and leaf_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g d) s leaf_value"
 and leaf_observed: "lpp_runtime_structure leaf_value t"
 and list_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g d)
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
 by (rule lpp_checked_parameter_forest_prefix[OF checked ground
   lpp_parameter_return_runtime_effect[OF leaf_effect returned] leaf_observed
   lpp_parameter_return_runtime_effect[OF list_effect returned] list_observed])

ML \<open>
val checked = @{thms lpp_checked_parameter_forest_return_prefix};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter return prefix" else ();
\<close>
end
