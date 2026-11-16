theory LP_Prolog_Scalar_Recurrence_Check
 imports LP_Prolog_Scalar_Recurrence_Failure_Check LP_Source_Recurrent_Simulation
begin

definition lpp_scalar_recurrence_check where
 "lpp_scalar_recurrence_check P q observations selection H actions outputs recipes failures =
   (let clauses = lp_cut_slice P (LPCUser q) (length observations);
        c = clauses!selection;
        body = snd (P!c);
        value_table = lpp_scalar_value_table H observations
    in selection<length clauses \<and> c<length P \<and>
       distinct H \<and> length H=length observations \<and>
       fst (P!c)=Fun (LPCUser q) (map Var H) \<and>
       length actions<length body \<and>
       take (length actions) body=map lpp_scalar_prefix_goal actions \<and>
       body!length actions=LPCAtom (Fun (LPCUser q) outputs) \<and>
       (q,length observations)\<notin>lpp_builtin_signature \<and>
       list_all (lpp_scalar_prefix_check value_table) actions \<and>
       lpp_scalar_outputs_check value_table observations outputs recipes \<and>
       length failures=selection \<and>
       list_all (\<lambda>i. lpp_check_scalar_failure P q observations (clauses!i) (failures!i)) [0..<selection])"

lemma lpp_scalar_recurrence_progress:
 assumes checked: "lpp_scalar_recurrence_check P q observations selection H actions outputs recipes failures"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "\<exists>next_args pending saved.
   lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations next_args \<and>
   (LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser q) next_args)#pending)#saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?clauses = "lp_cut_slice P (LPCUser q) (length observations)"
 let ?c = "?clauses!selection"
 let ?earlier = "take selection ?clauses"
 let ?later = "drop (Suc selection) ?clauses"
 let ?table = "lpp_scalar_value_table H observations"
 let ?eta = "lpp_partial_arguments H actuals"
 let ?rho = "lpc_fresh_head_environment H ?eta"
 let ?remaining = "drop (Suc (length actions)) (snd (P!?c))"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 have selected: "selection<length ?clauses" and index: "?c<length P"
   and distinct: "distinct H" and lengths: "length H=length observations"
   and ordinary: "(q,length observations)\<notin>lpp_builtin_signature"
   and prefix_checked: "list_all (lpp_scalar_prefix_check ?table) actions"
   and outputs_checked: "lpp_scalar_outputs_check ?table observations outputs recipes"
   using checked by (auto simp: lpp_scalar_recurrence_check_def Let_def)
 have split: "lp_cut_slice P (LPCUser q) (length H)= ?earlier @ ?c # ?later"
   using selected lengths by (simp add: id_take_nth_drop)
 have body_bound: "length actions<length (snd (P!?c))"
   using checked by (simp add: lpp_scalar_recurrence_check_def Let_def)
 have body_split: "snd (P!?c)=take (length actions) (snd (P!?c)) @
     (snd (P!?c))!length actions # ?remaining"
   using body_bound by (simp add: id_take_nth_drop)
 have clause: "P!?c=(Fun (LPCUser q) (map Var H),
     map lpp_scalar_prefix_goal actions @ LPCAtom (Fun (LPCUser q) outputs) # ?remaining)"
   using checked body_split by (cases "P!?c") (auto simp: lpp_scalar_recurrence_check_def Let_def)
 have actual_length: "length H=length actuals" using observed lengths
   by (simp add: lpp_scalar_observations_def)
 have head: "lp_ieval (Fun (LPCUser q) (map Var H)) ?eta=LPIFun (LPCUser q) actuals"
   using lpp_partial_arguments_exact[OF actual_length distinct] by (simp add: map_map o_def)
 have parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (?eta x) (lpp_machine_value w)" if "?table x=Some w" for x w
   by (rule lpp_scalar_observed_argument[OF lengths distinct observed that])
 have covered: "x\<in>set H" if "?table x=Some w" for x w
   by (rule lpp_scalar_table_covered[OF lengths that])
 have failed: "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) ?eta)#gs) d mark#saved,saved)\<in>?R\<^sup>+"
   if member: "d\<in>set ?earlier" for d mark saved
 proof -
  obtain i where bound: "i < selection" and same: "d= ?clauses!i"
    using member selected by (auto simp: in_set_conv_nth)
  have failure_checked: "lpp_check_scalar_failure P q observations (?clauses!i) (failures!i)"
    using checked bound by (auto simp: lpp_scalar_recurrence_check_def Let_def list_all_iff)
  show ?thesis using lpp_check_scalar_failure_sound[OF failure_checked observed,
      where gs=gs and mark=mark and saved=saved] head same by simp
 qed
 have step_exists: "\<exists>pending saved. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) ?eta)#gs)#es,
    LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser q) outputs) ?rho)#pending)#saved)\<in>?R\<^sup>+"
   by (rule lpp_scalar_selected_iteration[where value_table="?table", OF split index clause])
     (use ordinary lengths failed prefix_checked parameters covered in auto)
 obtain pending saved where step: "(LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t ?rho) outputs))#pending)#saved)\<in>?R\<^sup>+"
   using step_exists head by auto
 have fresh_parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (?rho x) (lpp_machine_value w)" if "?table x=Some w" for x w
   by (rule lpp_scalar_fresh_parameters[where value_table="?table"])
     (use parameters covered that in auto)
 have next_observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations
    (map (\<lambda>t. lp_ieval t ?rho) outputs)"
   by (rule lpp_scalar_outputs_sound[where value_table="?table", OF outputs_checked])
     (use fresh_parameters in auto)
 show ?thesis using step next_observed by blast
qed

ML \<open>
val checked = [@{thm lpp_scalar_recurrence_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence complete-clause dependency" else ();
\<close>
end
