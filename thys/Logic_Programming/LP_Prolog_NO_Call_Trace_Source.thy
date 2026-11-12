theory LP_Prolog_NO_Call_Trace_Source
 imports LP_Prolog_NO_Call_Trace_Check LP_Prolog_Binary64_NO
begin

definition lpp_no_call_trace_check_source where
 "lpp_no_call_trace_check_source fuel P q modes argv initial_steps a rest saved reserved vs calls edges =
   (length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    lpp_checked_builtin_trace (lpp_machine_no_step fuel P)
      [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
      (LPCGoals (LPCAtom a#rest)#saved) \<and>
    lpp_no_call_trace_check fuel P reserved vs calls edges a)"

theorem lpp_no_call_trace_check_source_sound:
 assumes checked: "lpp_no_call_trace_check_source fuel P q modes argv initial_steps a rest saved reserved vs calls edges"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not> SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 interpret trace: lpp_builtin_trace_checker P
   "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)" "lpp_machine_no_step fuel P"
   by unfold_locales (rule lpp_machine_no_step_sound)
 have loop: "\<not> SN_on ?R {lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar}"
   by (rule lpp_no_call_trace_check_sound[where fuel=fuel and reserved=reserved and vs=vs and calls=calls and edges=edges]) (use checked in \<open>simp add: lpp_no_call_trace_check_source_def\<close>)
 have reach: "(lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar,
   lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar)\<in>?R\<^sup>*"
   by (rule trace.trace_sound[where steps=initial_steps])
     (use checked in \<open>simp add: lpp_no_call_trace_check_source_def\<close>)
 have root: "\<not> SN_on ?R {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
 proof
  assume sn: "SN_on ?R {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
  have included: "{lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar} \<subseteq>
    ?R\<^sup>* `` {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
    using reach by auto
  have "SN_on ?R {lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar}"
    by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
  with loop show False by contradiction
 qed
 show ?thesis using checked root
   by (simp add: lpp_no_call_trace_check_source_def lp_cut_state_map_def)
qed

ML \<open>
val checked = [@{thm lpp_no_call_trace_check_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted original-query call recurrence" else ();
\<close>
end
