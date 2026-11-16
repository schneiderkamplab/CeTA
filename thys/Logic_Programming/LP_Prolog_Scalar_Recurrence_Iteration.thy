theory LP_Prolog_Scalar_Recurrence_Iteration
 imports LP_Prolog_Scalar_Recurrence_Failure LP_Cut_Failed_Clause_Sequence
begin

lemma lpp_scalar_selected_iteration:
 assumes selection: "lp_cut_slice P (LPCUser q) (length xs)=earlier@c#cs"
   and index: "c<length P"
   and clause: "P!c=(Fun (LPCUser q) (map Var xs),
     map lpp_scalar_prefix_goal actions @ LPCAtom tail # remaining)"
   and ordinary: "(q,length xs)\<notin>lpp_builtin_signature"
   and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
     (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var xs)) eta)#gs) d mark#saved,saved)\<in>
       (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   and checked: "list_all (lpp_scalar_prefix_check value_table) actions"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
   and covered: "\<And>x w. value_table x=Some w \<Longrightarrow> x\<in>set xs"
 shows "\<exists>pending saved. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var xs)) eta)#gs)#es,
   LPCGoals (LPCAtom (lp_ieval tail (lpc_fresh_head_environment xs eta))#pending)#saved)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 let ?a = "lp_ieval (Fun (LPCUser q) (map Var xs)) eta"
 let ?s = "LPCGoals (LPCAtom ?a#gs)#es"
 let ?rho = "lpc_fresh_head_environment xs eta"
 let ?body = "map lpp_scalar_prefix_goal actions @ LPCAtom tail # remaining"
 obtain mark where fresh: "lp_cut_fresh mark ?s" using lpc_uniform_fresh by blast
 let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?a#gs) d mark) cs @ LPCBarrier mark#es"
 let ?chosen = "LPCClause (LPCAtom ?a#gs) c mark#?saved"
 let ?alternatives = "map (\<lambda>d. LPCClause (LPCAtom ?a#gs) d mark) earlier @ ?chosen"
 have called: "(?s,?alternatives)\<in>lp_cut_mgu_source P"
   using lp_cut_mgu_source.case_call[of mark q "map eta xs" gs es P] fresh
   by (simp add: selection o_def)
 have defined: "lpp_defined P (q,length xs)"
   unfolding lpp_defined_def list_ex_iff
   by (rule bexI[of _ "P!c"]) (use nth_mem[OF index] clause in auto)
 have source_called: "(?s,?alternatives)\<in>?R"
   using called ordinary defined
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 have skipped: "(?alternatives,?chosen)\<in>?R\<^sup>*"
   by (rule lpc_failed_clause_sequence) (rule failed)
 have mgu: "lpc_mgu_resolve ?a gs (fst (P!c)) (snd (P!c)) lpc_fresh_caller ?rho"
   using lpc_fresh_head_mgu[where eta=eta and f="LPCUser q" and xs=xs and gs=gs and bs="?body"]
   by (simp add: clause)
 let ?pending = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho)) remaining @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs"
 let ?rest = "LPCAtom (lp_ieval tail ?rho)#?pending"
 let ?resolved = "LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho))
     (map lpp_scalar_prefix_goal actions) @ ?rest)#?saved"
 have resolved: "(?chosen,?resolved)\<in>lp_cut_mgu_source P"
   using lp_cut_mgu_source.resolve[OF index mgu, of mark "?saved"] by (simp add: clause)
 have source_resolved: "(?chosen,?resolved)\<in>?R"
   using resolved by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 have fresh_parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (?rho x) (lpp_machine_value w)" if "value_table x=Some w" for x w
   by (rule lpp_scalar_fresh_parameters[where value_table=value_table])
     (use parameters covered that in auto)
 have body_exists: "\<exists>saved. (?resolved,LPCGoals ?rest#saved)\<in>?R\<^sup>*"
   by (rule lpp_scalar_successful_prefix[where value_table=value_table])
     (use checked fresh_parameters in auto)
 obtain saved where body: "(?resolved,LPCGoals ?rest#saved)\<in>?R\<^sup>*"
   using body_exists by blast
 have entry: "(?s,?resolved)\<in>?R\<^sup>+"
   using source_called skipped source_resolved
   by (meson r_into_trancl trancl_rtrancl_trancl trancl_trans)
 show ?thesis using trancl_rtrancl_trancl[OF entry body] by blast
qed

ML \<open>
val checked = [@{thm lpp_scalar_selected_iteration}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence iteration dependency" else ();
\<close>
end
