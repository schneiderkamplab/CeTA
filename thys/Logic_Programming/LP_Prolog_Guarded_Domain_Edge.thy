theory LP_Prolog_Guarded_Domain_Edge
 imports LP_Prolog_Guarded_Domain_Iteration
begin

definition lpp_guarded_domain_edge_check where
 "lpp_guarded_domain_edge_check P q observations selection H gate actions outputs recipes dest_q target_observations =
   (let clauses = lp_cut_slice P (LPCUser q) (length observations);
        c = clauses!selection;
        body = snd (P!c);
        value_table = lpp_scalar_value_table H observations
    in selection<length clauses \<and> c<length P \<and>
       distinct H \<and> length H=length observations \<and>
       fst (P!c)=Fun (LPCUser q) (map Var H) \<and>
       Suc (length actions)<length body \<and>
       take (Suc (length actions)) body=lpp_scalar_guard_goal gate # map lpp_domain_prefix_goal actions \<and>
       body!Suc (length actions)=LPCAtom (Fun (LPCUser dest_q) outputs) \<and>
       (q,length observations)\<notin>lpp_builtin_signature \<and>
       lpp_domain_prefix_check H [] value_table actions \<and>
       lpp_domain_outputs_check (lpp_domain_prefix_domains value_table actions) target_observations outputs recipes)"

lemma lpp_guarded_domain_edge_progress:
 assumes checked: "lpp_guarded_domain_edge_check P q observations selection H gate actions outputs recipes dest_q target_observations"
   and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback) observations actuals"
   and gate: "lpp_scalar_guard_check
     (lpp_domain_concrete_table (lpp_binary64_profile_operation fallback)
       (lpp_scalar_value_table H observations) (lpp_partial_arguments H actuals)) gate=Some True"
   and failed: "\<And>d mark saved. d\<in>set (take selection (lp_cut_slice P (LPCUser q) (length observations))) \<Longrightarrow>
     (LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
 shows "\<exists>next_args pending saved.
   lpp_domain_observations (lpp_binary64_profile_operation fallback) target_observations next_args \<and>
   (LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser dest_q) next_args)#pending)#saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?clauses = "lp_cut_slice P (LPCUser q) (length observations)"
 let ?c = "?clauses!selection"
 let ?earlier = "take selection ?clauses"
 let ?later = "drop (Suc selection) ?clauses"
 let ?table = "lpp_scalar_value_table H observations"
 let ?eta = "lpp_partial_arguments H actuals"
 let ?rho = "lpc_fresh_head_environment H ?eta"
 let ?remaining = "drop (Suc (Suc (length actions))) (snd (P!?c))"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 have selected: "selection<length ?clauses" and index: "?c<length P"
   and distinct: "distinct H" and lengths: "length H=length observations"
   and ordinary: "(q,length observations)\<notin>lpp_builtin_signature"
   and prefix_checked: "lpp_domain_prefix_check H [] ?table actions"
   and outputs_checked: "lpp_domain_outputs_check (lpp_domain_prefix_domains ?table actions) target_observations outputs recipes"
   using checked by (auto simp: lpp_guarded_domain_edge_check_def Let_def)
 have split: "lp_cut_slice P (LPCUser q) (length H)= ?earlier @ ?c # ?later"
   using selected lengths by (simp add: id_take_nth_drop)
 have body_bound: "Suc (length actions)<length (snd (P!?c))"
   using checked by (simp add: lpp_guarded_domain_edge_check_def Let_def)
 have body_split: "snd (P!?c)=take (Suc (length actions)) (snd (P!?c)) @
     (snd (P!?c))!Suc (length actions) # ?remaining"
   using body_bound by (simp add: id_take_nth_drop)
 have clause: "P!?c=(Fun (LPCUser q) (map Var H),
     lpp_scalar_guard_goal gate # map lpp_domain_prefix_goal actions @ LPCAtom (Fun (LPCUser dest_q) outputs) # ?remaining)"
   using checked body_split by (cases "P!?c") (auto simp: lpp_guarded_domain_edge_check_def Let_def)
 have actual_length: "length H=length actuals" using observed lengths
   by (simp add: lpp_domain_observations_def)
 have head: "lp_ieval (Fun (LPCUser q) (map Var H)) ?eta=LPIFun (LPCUser q) actuals"
   using lpp_partial_arguments_exact[OF actual_length distinct] by (simp add: map_map o_def)
 have environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) ?table ?eta"
   by (rule lpp_domain_observed_environment[OF lengths distinct observed])
 have covered: "x\<in>set H" if "?table x=Some w" for x w
   by (rule lpp_scalar_table_covered[OF lengths that])
 let ?concrete = "lpp_domain_concrete_table (lpp_binary64_profile_operation fallback) ?table ?eta"
 have parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
   (?eta x) (lpp_machine_value v)" if "?concrete x=Some v" for x v
   by (rule lpp_domain_concrete_parameters[OF environment that])
 have gate_covered: "x\<in>set H" if "?concrete x=Some v" for x v
   using that covered by (auto simp: lpp_domain_concrete_table_def split: option.splits)
 have failures: "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) ?eta)#gs) d mark#saved,saved)\<in>?R\<^sup>+"
   if "d\<in>set ?earlier" for d mark saved
   using failed[OF that, of mark saved] head by simp
 have step_exists: "\<exists>scalar_values pending saved.
   lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback)
     (lpp_domain_prefix_domains ?table actions)
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values ?eta) \<and>
   (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) ?eta)#gs)#es,
    LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser dest_q) outputs)
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values ?eta))#pending)#saved)\<in>?R\<^sup>+"
   by (rule lpp_guarded_domain_selected_iteration[where domains="?table" and value_table="?concrete", OF split index clause])
     (use ordinary lengths failures gate parameters gate_covered prefix_checked environment covered in auto)
 obtain scalar_values pending saved where final_environment:
   "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback)
     (lpp_domain_prefix_domains ?table actions)
     (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values ?eta)"
   and step: "(LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser dest_q) (map (\<lambda>t. lp_ieval t
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values ?eta)) outputs))#pending)#saved)\<in>?R\<^sup>+"
   using step_exists head by auto
 have next_observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback) target_observations
    (map (\<lambda>t. lp_ieval t
      (lpp_recurrent_assignment_environment H (lpp_domain_prefix_known [] actions) scalar_values ?eta)) outputs)"
   by (rule lpp_domain_outputs_sound[OF outputs_checked final_environment])
 show ?thesis using step next_observed by blast
qed

ML \<open>
val checked = [@{thm lpp_guarded_domain_edge_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence complete-clause dependency" else ();
\<close>
end
