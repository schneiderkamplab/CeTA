theory LP_Prolog_Parameter_Leaf_Prefix
 imports LP_Prolog_Parameter_Leaf_Program LP_Prolog_Ground_Observation_Program
   LP_Prolog_Runtime_Leaf_Invariant LP_Prolog_List_Leaf_Program
begin

text \<open>Embed the successful leaf relation into the complete residual program.
The caller environment and ordered continuation are preserved. The actual
runtime effect remains a premise; termination of the residual cannot supply it.\<close>

lemma lpp_parameter_leaf_program_success_in:
 assumes included: "set (lpp_parameter_leaf_program rel spine_predicate f g) \<subseteq> set P"
 and effect: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s t"
 shows "((lpp_leaf_relation_goal rel s t
   [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
proof (rule lpp_leaf_relation_success[OF _ _ effect])
 show "set (lpp_leaf_core_clauses rel spine_predicate
   (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])) \<subseteq> set P"
  using included by (auto simp: lpp_parameter_leaf_program_def)
next
 fix u assume member: "u\<in>lpp_parameter_leaf_templates f g c"
 show "\<exists>pattern nu.
   ((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters
      (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])),[])\<in>set P \<and>
   map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters
      (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])) =
     [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar] \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure (lpp_structure_template u)) LPIVar"
  using lpp_parameter_leaf_replacement_coverage[OF member, of rel spine_predicate] included by (auto; blast)
qed

lemma lpp_runtime_parameter_leaf_program_success:
 assumes included: "set (lpp_parameter_leaf_program rel spine_predicate f g) \<subseteq> set P"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c) s returned_value"
 and observed: "lpp_runtime_structure returned_value t"
 shows "((lpp_leaf_relation_goal rel s t
   [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
proof -
 obtain u where actual: "lpp_runtime_structure returned_value u"
 and related: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s u"
  using effect unfolding lpp_runtime_leaf_effect_def by blast
 have "u=t" by (rule lpp_runtime_structure_unique[OF actual observed])
 then have effect_actual: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s t"
  using related by simp
 show ?thesis by (rule lpp_parameter_leaf_program_success_in[OF included effect_actual])
qed

lemma lpp_runtime_parameter_leaf_guarded_prefix:
 assumes core: "set (lpp_ground_observation_program ground_predicate ground_spine) \<subseteq> set P"
 and included: "set (lpp_parameter_leaf_program rel spine_predicate f g) \<subseteq> set P"
 and ground: "vars_term c = {}"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c) s returned_value"
 and observed: "lpp_runtime_structure returned_value t"
 shows "((lpp_ground_tree_goal ground_predicate (lpp_structure_template c)#
   lpp_leaf_relation_goal rel s t
    [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
proof -
 let ?call = "lpp_leaf_relation_goal rel s t
    [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]"
 have guard: "((lpp_ground_tree_goal ground_predicate (lpp_structure_template c)#?call#rest,env),
    (?call#rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  by (rule lpp_ground_template_observation_success[OF core ground])
 have related: "((?call#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  by (rule lpp_runtime_parameter_leaf_program_success[OF included effect observed])
 show ?thesis by (rule rtrancl_trans[OF guard related])
qed

lemma lpp_runtime_parameter_list_program_success:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel 1) \<subseteq> set P"
 and included: "set (lpp_parameter_leaf_program element_rel spine_predicate f g) \<subseteq> set P"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c)
   (lpp_structural_argument_list xs) returned_value"
 and observed: "lpp_runtime_structure returned_value t"
 shows "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs) t
   [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
proof -
 obtain u where actual: "lpp_runtime_structure returned_value u"
 and related: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) (lpp_structural_argument_list xs) u"
  using effect unfolding lpp_runtime_leaf_effect_def by blast
 have "u=t" by (rule lpp_runtime_structure_unique[OF actual observed])
 then have actual_effect: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c)
   (lpp_structural_argument_list xs) t" using related by simp
 show ?thesis
  apply (rule lpp_list_leaf_effect_program_success[where element_rel=element_rel, OF _ _ actual_effect])
  subgoal using clauses by simp
  subgoal for s t rest by (rule lpp_parameter_leaf_program_success_in[OF included]) assumption
  done
qed

lemma lpp_runtime_parameter_forest_guarded_prefix:
 assumes ground_core: "set (lpp_ground_observation_program ground_predicate ground_spine) \<subseteq> set P"
 and leaf_core: "set (lpp_parameter_leaf_program leaf_rel leaf_spine f g) \<subseteq> set P"
 and list_core: "set (lpp_list_leaf_clauses list_predicate element_rel 1) \<subseteq> set P"
 and element_core: "set (lpp_parameter_leaf_program element_rel element_spine f g) \<subseteq> set P"
 and ground: "vars_term c = {}"
 and leaf_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c) s leaf_value"
 and leaf_observed: "lpp_runtime_structure leaf_value t"
 and list_effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g c)
    (lpp_structural_argument_list xs) list_value"
 and list_observed: "lpp_runtime_structure list_value ys"
 shows "((lpp_ground_tree_goal ground_predicate (lpp_structure_template c)#
   lpp_leaf_relation_goal leaf_rel s t
    [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#
   lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs) ys
    [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
proof -
 let ?ps = "[lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]"
 let ?tail = "lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs) ys ?ps"
 have first: "((lpp_ground_tree_goal ground_predicate (lpp_structure_template c)#
   lpp_leaf_relation_goal leaf_rel s t ?ps#?tail#rest,env),(?tail#rest,env))\<in>
   (lp_seg_answer_step P)\<^sup>*"
  by (rule lpp_runtime_parameter_leaf_guarded_prefix[OF ground_core leaf_core ground leaf_effect leaf_observed])
 have last: "((?tail#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  by (rule lpp_runtime_parameter_list_program_success[OF list_core element_core list_effect list_observed])
 show ?thesis by (rule rtrancl_trans[OF first last])
qed

ML \<open>
val checked = @{thms lpp_parameter_leaf_program_success_in lpp_runtime_parameter_leaf_program_success
 lpp_runtime_parameter_leaf_guarded_prefix lpp_runtime_parameter_list_program_success
 lpp_runtime_parameter_forest_guarded_prefix};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter leaf prefix" else ();
\<close>
end
