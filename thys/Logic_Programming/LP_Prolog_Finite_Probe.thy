theory LP_Prolog_Finite_Probe
  imports LP_Prolog_Finite_Source
begin

lemma lpp_finite_probe_step:
  assumes name: "lpp_probe_name f"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [LPIFun (LPCUser g) argv])#gs),active)#saved) event tt"
  shows "event=None \<and> (\<exists>m n.
    lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
    lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
    tt=lpp_probe_stack (LPIFun (LPCUser g) argv) (f=''1:once'') m n gs active saved)"
proof -
  have domain: "lpp_probe_domain f [LPIFun (LPCUser g) argv]"
    using name by (auto simp: lpp_probe_domain_def)
  have selected: "(f,length [LPIFun (LPCUser g) argv])\<in>lpp_builtin_signature"
    by (rule lpp_probe_selected[OF domain])
  have outcome: "\<And>out. lpp_finite_source_builtin f [LPIFun (LPCUser g) argv] out =
      (out=LPPBuiltinProbe (LPIFun (LPCUser g) argv) (f=''1:once''))"
    by (simp only: lpp_finite_source_builtin_def name if_True lpp_probe_outcome_def domain list.sel; simp)
  show ?thesis using step selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def outcome lpp_probe_stack_def lp_cut_fresh_def)
qed

lemma lpp_finite_probe_domain:
  "lpp_probe_name f \<Longrightarrow>
    lpp_finite_source_domain f [lp_ieval (Fun (LPCUser g) argv) eta]"
  by (auto simp: lpp_finite_source_domain_def lpp_probe_domain_def)

end
