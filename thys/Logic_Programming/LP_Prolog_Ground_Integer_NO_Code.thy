theory LP_Prolog_Ground_Integer_NO_Code
 imports LP_Prolog_Ground_Integer_NO_XML
begin

text \<open>Expose the executable locale definition through its concrete checker.
This equation is proved from the existing definition; it adds no checking rule.\<close>

lemma lpp_ground_integer_no_check_source_code [code]:
 "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     (lp_cut_barriers before \<and> lp_cut_barriers after \<or>
       list_all (\<lambda>x. snd x\<noteq>[] \<and> lpc_no_suffix_safe (snd x)) steps) \<and> steps \<noteq> [] \<and>
     lpp_checked_builtin_trace (lpp_ground_integer_no_step fuel P) [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpp_checked_builtin_trace (lpp_ground_integer_no_step fuel P) [LPCGoals [LPCAtom a]] steps
       ([LPCGoals [LPCAtom a]] @ after))"
proof -
 interpret trace: lpp_builtin_trace_checker P lpp_ground_integer_no_builtin "lpp_ground_integer_no_step fuel P"
   by unfold_locales (rule lpp_ground_integer_no_step_sound)
 show ?thesis by (simp only: lpp_ground_integer_no_check_source_def trace.check_source_def)
qed

end
