theory LP_Prolog_Guarded_Domain_Iteration
 imports LP_Prolog_Domain_Guards
begin

lemma lpp_guarded_domain_selected_iteration:
 assumes selection: "lp_cut_slice P (LPCUser q) (length H)=earlier@c#cs"
   and index: "c<length P"
   and clause: "P!c=(Fun (LPCUser q) (map Var H),
     lpp_scalar_guard_goal gate # map lpp_domain_prefix_goal actions @ LPCAtom tail # remaining)"
   and ordinary: "(q,length H)\<notin>lpp_builtin_signature"
   and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
     (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) eta)#gs) d mark#saved,saved)\<in>
       (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   and gate: "lpp_scalar_guard_check value_table gate=Some True"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
   and gate_covered: "\<And>x w. value_table x=Some w \<Longrightarrow> x\<in>set H"
   and checked: "lpp_domain_prefix_check H [] domains actions"
   and environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains eta"
   and covered: "\<And>x d. domains x=Some d \<Longrightarrow> x\<in>set H"
 shows "\<exists>scalar_values pending saved.
   lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback)
     (lpp_domain_prefix_domains domains actions)
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values eta) \<and>
   (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) eta)#gs)#es,
    LPCGoals (LPCAtom (lp_ieval tail
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values eta))#pending)#saved)\<in>
     (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?a = "lp_ieval (Fun (LPCUser q) (map Var H)) eta"
 let ?s = "LPCGoals (LPCAtom ?a#gs)#es"
 let ?rho = "lpc_fresh_head_environment H eta"
 let ?body = "lpp_scalar_guard_goal gate # map lpp_domain_prefix_goal actions @ LPCAtom tail # remaining"
 obtain mark where fresh: "lp_cut_fresh mark ?s" using lpc_uniform_fresh by blast
 let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?a#gs) d mark) cs @ LPCBarrier mark#es"
 let ?chosen = "LPCClause (LPCAtom ?a#gs) c mark#?saved"
 let ?alternatives = "map (\<lambda>d. LPCClause (LPCAtom ?a#gs) d mark) earlier @ ?chosen"
 have called: "(?s,?alternatives)\<in>lp_cut_mgu_source P"
   using lp_cut_mgu_source.case_call[of mark q "map eta H" gs es P] fresh
   by (simp add: selection o_def)
 have defined: "lpp_defined P (q,length H)"
   unfolding lpp_defined_def list_ex_iff
   by (rule bexI[of _ "P!c"]) (use nth_mem[OF index] clause in auto)
 have source_called: "(?s,?alternatives)\<in>?R"
   using called ordinary defined
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 have skipped: "(?alternatives,?chosen)\<in>?R\<^sup>*"
   by (rule lpc_failed_clause_sequence) (rule failed)
 have mgu: "lpc_mgu_resolve ?a gs (fst (P!c)) (snd (P!c)) lpc_fresh_caller ?rho"
   using lpc_fresh_head_mgu[where eta=eta and f="LPCUser q" and xs=H and gs=gs and bs="?body"]
   by (simp add: clause)
 let ?resolved = "LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho)) ?body @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#?saved"
 have resolved: "(?chosen,?resolved)\<in>lp_cut_mgu_source P"
   using lp_cut_mgu_source.resolve[OF index mgu, of mark "?saved"] by (simp add: clause)
 have source_resolved: "(?chosen,?resolved)\<in>?R"
   using resolved by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 let ?after_gate = "LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho))
   (map lpp_domain_prefix_goal actions @ LPCAtom tail # remaining) @
   map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#?saved"
 have fresh_parameters: "lpp_stable_scalar_evaluation ?operation (?rho x) (lpp_machine_value w)"
   if "value_table x=Some w" for x w
   by (rule lpp_scalar_fresh_parameters[where value_table=value_table and eta=eta and xs=H])
     (use parameters gate_covered that in auto)
 have gate_step: "(?resolved,?after_gate)\<in>?R"
   using lpp_scalar_guard_step[OF gate fresh_parameters,
     where P=P and es="?saved" and gs="map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho))
      (map lpp_domain_prefix_goal actions @ LPCAtom tail # remaining) @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs"]
   by (simp add: lpp_scalar_guard_goal_def)
 have fresh_environment: "lpp_recurrent_domain_environment ?operation domains
     (lpp_recurrent_assignment_environment H [] (\<lambda>_. LPPMachineInteger 0) eta)"
   unfolding lpp_recurrent_environment_initial
   by (rule lpp_domain_fresh_environment[OF environment covered])
 let ?rest = "map (lp_cut_bind mark id) (LPCAtom tail#remaining)"
 obtain scalar_values where final_environment: "lpp_recurrent_domain_environment ?operation
     (lpp_domain_prefix_domains domains actions)
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values eta)"
   and steps: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_recurrent_assignment_environment H [] (\<lambda>_. LPPMachineInteger 0) eta)))
       (map lpp_domain_prefix_goal actions @ ?rest) @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#?saved,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values eta))) ?rest @
       map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#?saved)\<in>?R\<^sup>*"
   using lpp_domain_prefix_source_steps[OF checked fresh_environment,
      where rest="?rest" and pending=gs and es="?saved" and P=P] by blast
 let ?env = "lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values eta"
 let ?pending = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env)) remaining @
     map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs"
 have body: "(?after_gate,LPCGoals (LPCAtom (lp_ieval tail ?env)#?pending)#?saved)\<in>?R\<^sup>*"
   using steps by (simp add: lpp_recurrent_environment_initial map_map o_def lp_cut_map_bind lpp_domain_prefix_bind)
 have entry: "(?s,?after_gate)\<in>?R\<^sup>+"
   using source_called skipped source_resolved gate_step
   by (meson r_into_trancl trancl_rtrancl_trancl trancl_trans)
 show ?thesis using final_environment trancl_rtrancl_trancl[OF entry body] by blast
qed

ML \<open>
val checked = [@{thm lpp_guarded_domain_selected_iteration}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar domain source iteration dependency" else ();
\<close>
end
