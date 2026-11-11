theory LP_Prolog_Binary64_NO_Code
 imports LP_Prolog_Binary64_NO_XML
begin

text \<open>Expose the executable locale definition through its concrete checker.
This equation is proved from the existing definition; it adds no checking rule.\<close>

lemma lpp_machine_no_check_source_code [code]:
 "lpp_machine_no_check_source fuel P q modes argv a before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     lp_cut_barriers before \<and> lp_cut_barriers after \<and> steps \<noteq> [] \<and>
     lpp_checked_builtin_trace (lpp_machine_no_step fuel P) [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpp_checked_builtin_trace (lpp_machine_no_step fuel P) [LPCGoals [LPCAtom a]] steps
       ([LPCGoals [LPCAtom a]] @ after))"
proof -
 interpret trace: lpp_builtin_trace_checker P "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)" "lpp_machine_no_step fuel P"
   by unfold_locales (rule lpp_machine_no_step_sound)
 show ?thesis by (simp only: lpp_machine_no_check_source_def trace.check_source_def)
qed

end
