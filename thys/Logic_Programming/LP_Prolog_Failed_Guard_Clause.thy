theory LP_Prolog_Failed_Guard_Clause
 imports LP_Prolog_Failed_Guard_Tree LP_Prolog_Scalar_Recurrence_Interface
begin

lemma lpp_failed_tree_bind:
 "map (lp_cut_bind mark f) (lpp_failed_tree_goals tree) =
  map (lp_cut_map f) (lpp_failed_tree_goals tree)"
 by (induct tree) (auto simp: lpp_scalar_guard_goal_def)

lemma lpp_failed_tree_clause:
 assumes index: "d<length P"
   and clause: "P!d=(Fun (LPCUser q) (map Var xs),
       lpp_failed_tree_goals tree @ remaining)"
   and checked: "lpp_failed_tree_check value_table tree"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
   and covered: "\<And>x w. value_table x=Some w \<Longrightarrow> x\<in>set xs"
 shows "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var xs)) eta)#gs) d mark#es,es)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 let ?a = "lp_ieval (Fun (LPCUser q) (map Var xs)) eta"
 let ?rho = "lpc_fresh_head_environment xs eta"
 let ?body = "lpp_failed_tree_goals tree @ remaining"
 let ?rest = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs"
 let ?s = "LPCClause (LPCAtom ?a#gs) d mark#es"
 let ?t = "LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho)) ?body @ ?rest)#es"
 have mgu: "lpc_mgu_resolve ?a gs (fst (P!d)) (snd (P!d)) lpc_fresh_caller ?rho"
   using lpc_fresh_head_mgu[where eta=eta and f="LPCUser q" and xs=xs and gs=gs and bs="?body"]
   by (simp add: clause)
 have resolved: "(?s,?t)\<in>lp_cut_mgu_source P"
   using lp_cut_mgu_source.resolve[OF index mgu, of mark es] by (simp add: clause)
 have source_resolved: "(?s,?t)\<in>?R"
   using resolved by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 have fresh_parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (?rho x) (lpp_machine_value w)" if "value_table x=Some w" for x w
   by (rule lpp_scalar_fresh_parameters[where value_table=value_table])
     (use parameters covered that in auto)
 have body: "(?t,es)\<in>?R\<^sup>+"
   using lpp_failed_tree_sound[where V=value_table and eta="?rho", OF checked fresh_parameters, where P=P and gs="map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho)) remaining @ ?rest" and es=es]
     by (simp add: lpp_failed_tree_bind)
 show ?thesis by (rule trancl_trans[OF r_into_trancl[OF source_resolved] body])
qed

end
