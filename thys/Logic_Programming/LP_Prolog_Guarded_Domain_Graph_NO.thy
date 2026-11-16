theory LP_Prolog_Guarded_Domain_Graph_NO
 imports LP_Prolog_Guarded_Domain_Graph
begin

definition lpp_guarded_domain_graph_source_check where
 "lpp_guarded_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved
     observations initial_recipes start_index modules =
   (lp_cut_source_program P \<and> length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    lpp_checked_builtin_trace (lpp_machine_no_step fuel P)
      [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
      (LPCGoals (LPCAtom (Fun (LPCUser core) actuals)#pending)#saved) \<and>
    lpp_domain_outputs_check (\<lambda>_. None) observations actuals initial_recipes \<and>
    start_index<length modules \<and> core=lpp_guarded_module_q (modules!start_index) \<and>
    observations=lpp_guarded_module_observations (modules!start_index) \<and> lpp_guarded_domain_graph_check P modules)"

theorem lpp_guarded_domain_graph_source_sound:
 assumes checked: "lpp_guarded_domain_graph_source_check fuel P q modes argv initial_steps core actuals pending saved
     observations initial_recipes start_index modules"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?initial = "[LPCGoals [LPCAtom (Fun (LPCUser q) argv)]]"
 let ?reached = "LPCGoals (LPCAtom (Fun (LPCUser core) actuals)#pending)#saved"
 interpret trace: lpp_builtin_trace_checker P "lpp_stable_source_builtin ?operation" "lpp_machine_no_step fuel P"
   by unfold_locales (rule lpp_machine_no_step_sound)
 have initial_checked: "lpp_domain_outputs_check (\<lambda>_. None) observations actuals initial_recipes"
   and recurrence: "lpp_guarded_domain_graph_check P modules"
   using checked by (auto simp: lpp_guarded_domain_graph_source_check_def)
 have empty_environment: "lpp_recurrent_domain_environment ?operation (\<lambda>_. None) LPIVar"
   by (simp add: lpp_recurrent_domain_environment_def)
 have observed: "lpp_domain_observations ?operation observations (map (\<lambda>t. lp_ieval t LPIVar) actuals)"
   by (rule lpp_domain_outputs_sound[OF initial_checked empty_environment])
 have bound: "start_index<length modules" and core: "core=lpp_guarded_module_q (modules!start_index)"
   and interface: "observations=lpp_guarded_module_observations (modules!start_index)"
   using checked by (auto simp: lpp_guarded_domain_graph_source_check_def)
 have observed': "lpp_domain_observations ?operation (lpp_guarded_module_observations (modules!start_index))
     (map (\<lambda>t. lp_ieval t LPIVar) actuals)" using observed interface by simp
 have loop: "\<not>SN_on ?R {lp_cut_state_eval ?reached LPIVar}"
   using lpp_guarded_domain_graph_nontermination[OF recurrence bound observed',
     where gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) pending"
       and es="lp_cut_state_eval saved LPIVar"]
   by (simp add: lp_cut_state_map_def core)
 have reach: "(lp_cut_state_eval ?initial LPIVar,lp_cut_state_eval ?reached LPIVar)\<in>?R\<^sup>*"
   by (rule trace.trace_sound[where steps=initial_steps])
     (use checked in \<open>auto simp: lpp_guarded_domain_graph_source_check_def\<close>)
 have root: "\<not>SN_on ?R {lp_cut_state_eval ?initial LPIVar}"
 proof
  assume sn: "SN_on ?R {lp_cut_state_eval ?initial LPIVar}"
  have included: "{lp_cut_state_eval ?reached LPIVar}\<subseteq>?R\<^sup>* `` {lp_cut_state_eval ?initial LPIVar}"
    using reach by auto
  have "SN_on ?R {lp_cut_state_eval ?reached LPIVar}"
    by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
  with loop show False by contradiction
 qed
 show ?thesis using checked root
   by (auto simp: lpp_guarded_domain_graph_source_check_def lp_cut_state_map_def)
qed

ML \<open>
val checked = [@{thm lpp_guarded_domain_graph_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar domain source nontermination dependency" else ();
\<close>
end
