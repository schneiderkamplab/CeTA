theory LP_Prolog_Scoped_Return_Models
 imports LP_Prolog_Return_Models LP_Cut_Scoped_Return_Models
begin

text \<open>The source model accounts for every actual successful builtin
outcome. Failure and uncaught error branches return no value. Unsupported
operations remain protected by the existing domain envelope.\<close>

theorem lpp_scoped_model_answer_preserved:
  assumes program: "lpc_scoped_model_program P F M"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_model: "\<And>f ts a keep sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> M (lp_isubst a sigma)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_control: "\<And>f ts a keep. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and step: "lpp_answer_transition P B U ss event tt"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
  shows "list_all (lpc_scoped_model_frame F M K) tt"
  using step known
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis by (rule lpc_scoped_model_answer_preserved[OF program]) (use base known in auto)
next
  case (success f ts sigma gs eta es)
  have member: "f\<in>F" using success known by simp
  have model: "M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule builtin[OF member]) (use success in simp)
  have before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using success known by simp
  have continued: "lpc_model_goals M K (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
    (\<lambda>x. lp_isubst (eta x) sigma)"
    by (rule lpc_model_builtin[OF before model stable])
  have control: "list_all (lpc_return_control_igoal F) gs" using success known by simp
  show ?thesis using success known continued lpc_return_control_subst[OF control] by simp
next
  case (probe f ts a keep m gs es n eta)
  have member: "f\<in>F" using probe known by simp
  have before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using probe known by simp
  have models: "\<And>sigma. (\<not>keep \<or> M (lp_isubst a sigma)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule probe_model[OF member probe(4)])
  have control: "lpc_return_control_igoal F (LPCAtom a)"
    by (rule probe_control[OF member probe(4)])
  show ?thesis using probe known before models control
    by (cases keep) (auto simp: lpp_probe_goals_def lpp_probe_else_def lpc_model_goals_def)
qed (use known in auto)

lemma lpp_scoped_model_domain_answer_preserved:
  assumes program: "lpc_scoped_model_program P F M"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_model: "\<And>f ts a keep sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> M (lp_isubst a sigma)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_control: "\<And>f ts a keep. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and step: "lpp_domain_answers P B U D ss event tt"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
  shows "list_all (lpc_scoped_model_frame F M K) tt"
  using step known lpp_scoped_model_answer_preserved[OF program builtin probe_model probe_control stable]
  by (auto simp: lpp_domain_answers_def)

theorem lpp_scoped_model_actual_return:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry * ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes program: "lpc_scoped_model_program P F M"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_model: "\<And>f ts a keep sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> M (lp_isubst a sigma)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_control: "\<And>f ts a keep. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
  shows "K rho"
proof -
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and event: "lpp_domain_answers P B U D us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have invariant: "list_all (lpc_scoped_model_frame F M K) us" using path
  proof (induct rule: rtrancl_induct)
    case base show ?case by (rule known)
  next
    case (step us vs)
    then obtain ev where transition: "lpp_domain_answers P B U D us ev vs"
      by (auto simp: lp_answer_steps_def)
    show ?case by (rule lpp_scoped_model_domain_answer_preserved[OF program builtin probe_model probe_control stable transition step.hyps(3)])
  qed
  have transition: "lpp_answer_transition P B U us (Some rho) tail"
    using event by (simp add: lpp_domain_answers_def)
  have shape: "us=(LPCGoals [],rho)#tail"
    by (rule lpp_answer_event_is_success[OF transition])
  have all: "\<forall>sigma. K (\<lambda>x. lp_isubst (rho x) sigma)"
    using invariant by (simp add: shape lpc_model_goals_def)
  show ?thesis using all[THEN spec, of LPIVar] by simp
qed


lemma lpp_scoped_model_actual_return_without_probe:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry * ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes program: "lpc_scoped_model_program P F M"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and no_probe: "\<And>f ts a keep. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinProbe a keep)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
  shows "K rho"
  by (rule lpp_scoped_model_actual_return[OF program builtin _ _ stable known actual])
    (use no_probe in blast)+

end
