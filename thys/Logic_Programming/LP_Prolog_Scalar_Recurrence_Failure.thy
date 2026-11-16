theory LP_Prolog_Scalar_Recurrence_Failure
 imports LP_Prolog_Scalar_Recurrence_Steps
begin

lemma lpp_scalar_fresh_parameters:
 assumes parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
   and covered: "\<And>x w. value_table x=Some w \<Longrightarrow> x\<in>set xs"
   and selected: "value_table x=Some w"
 shows "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lpc_fresh_head_environment xs eta x) (lpp_machine_value w)"
 using lpp_stable_scalar_evaluation_subst[OF parameters[OF selected], of lpc_fresh_caller]
   covered[OF selected]
 by (simp add: lpc_fresh_head_environment_def lpp_machine_value_named)

lemma lpp_scalar_guard_prefix:
 assumes checked: "list_all (\<lambda>g. lpp_scalar_guard_check value_table g=Some True) guards"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta))
     (map lpp_scalar_guard_goal guards) @ gs)#es,LPCGoals gs#es)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked
proof (induct guards)
 case Nil show ?case by simp
next
 case (Cons g guards)
 have checked: "lpp_scalar_guard_check value_table g=Some True" and tail:
   "list_all (\<lambda>g. lpp_scalar_guard_check value_table g=Some True) guards"
   using Cons.prems by simp_all
 let ?rest = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta)) (map lpp_scalar_guard_goal guards) @ gs"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 have step: "(LPCGoals (lp_cut_bind mark (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal g)#?rest)#es,
      LPCGoals ?rest#es)\<in>?R"
   using lpp_scalar_guard_step[OF checked parameters, where gs="?rest" and es=es and P=P]
   by (simp add: lpp_scalar_guard_goal_def)
 show ?case using rtrancl_trans[OF r_into_rtrancl[OF step] Cons.hyps[OF tail]] by simp
qed

lemma lpp_scalar_failed_body:
 assumes successful: "list_all (\<lambda>g. lpp_scalar_guard_check value_table g=Some True) guards"
   and failed: "lpp_scalar_guard_check value_table failure=Some False"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta))
     (map lpp_scalar_guard_goal guards @ lpp_scalar_guard_goal failure # remaining) @ gs)#es,es)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 let ?rest = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta)) remaining @ gs"
 let ?last = "lp_cut_bind mark (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_goal failure)"
 have initial: "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t eta))
     (map lpp_scalar_guard_goal guards) @ ?last # ?rest)#es,LPCGoals (?last#?rest)#es)\<in>?R\<^sup>*"
   by (rule lpp_scalar_guard_prefix[OF successful parameters])
 have final: "(LPCGoals (?last#?rest)#es,es)\<in>?R"
   using lpp_scalar_guard_step[OF failed parameters, where gs="?rest" and es=es and P=P]
   by (simp add: lpp_scalar_guard_goal_def)
 show ?thesis using rtrancl_trancl_trancl[OF initial r_into_trancl[OF final]] by simp
qed

lemma lpp_scalar_failed_clause:
 assumes index: "d<length P"
   and clause: "P!d=(Fun (LPCUser q) (map Var xs),
       map lpp_scalar_guard_goal guards @ lpp_scalar_guard_goal failure # remaining)"
   and successful: "list_all (\<lambda>g. lpp_scalar_guard_check value_table g=Some True) guards"
   and failed: "lpp_scalar_guard_check value_table failure=Some False"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
   and covered: "\<And>x w. value_table x=Some w \<Longrightarrow> x\<in>set xs"
 shows "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var xs)) eta)#gs) d mark#es,es)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 let ?a = "lp_ieval (Fun (LPCUser q) (map Var xs)) eta"
 let ?rho = "lpc_fresh_head_environment xs eta"
 let ?body = "map lpp_scalar_guard_goal guards @ lpp_scalar_guard_goal failure # remaining"
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
   by (rule lpp_scalar_failed_body[OF successful failed fresh_parameters])
 show ?thesis by (rule trancl_trans[OF r_into_trancl[OF source_resolved] body])
qed

ML \<open>
val checked = [@{thm lpp_scalar_failed_body}, @{thm lpp_scalar_failed_clause}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence failed-alternative dependency" else ();
\<close>
end
