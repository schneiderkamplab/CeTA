theory LP_Prolog_Return_Models
 imports LP_Cut_Return_Models LP_Prolog_Domain_Modular LP_Scoped_Answer_Composition
begin

text \<open>The source model accounts for every actual successful builtin
outcome. Failure and uncaught error branches return no value. Unsupported
operations remain protected by the existing domain envelope.\<close>

theorem lpp_model_answer_preserved:
  assumes program: "lpc_model_program P M"
    and builtin: "\<And>f ts sigma. U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and step: "lpp_answer_transition P B U ss event tt"
    and known: "list_all (lpc_model_frame M K) ss"
  shows "list_all (lpc_model_frame M K) tt"
  using step known
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis by (rule lpc_model_answer_preserved[OF program]) (use base known in auto)
next
  case (success f ts sigma gs eta es)
  have model: "M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule builtin) (use success in simp)
  have before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using success known by simp
  have continued: "lpc_model_goals M K (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)
    (\<lambda>x. lp_isubst (eta x) sigma)"
    by (rule lpc_model_builtin[OF before model stable])
  show ?thesis using success known continued by simp
qed (use known in auto)

lemma lpp_model_domain_answer_preserved:
  assumes program: "lpc_model_program P M"
    and builtin: "\<And>f ts sigma. U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and step: "lpp_domain_answers P B U D ss event tt"
    and known: "list_all (lpc_model_frame M K) ss"
  shows "list_all (lpc_model_frame M K) tt"
  using step known lpp_model_answer_preserved[OF program builtin stable]
  by (auto simp: lpp_domain_answers_def)

theorem lpp_model_actual_return:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry * ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes program: "lpc_model_program P M"
    and builtin: "\<And>f ts sigma. U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "list_all (lpc_model_frame M K) ss"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
  shows "K rho"
proof -
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and event: "lpp_domain_answers P B U D us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have invariant: "list_all (lpc_model_frame M K) us" using path
  proof (induct rule: rtrancl_induct)
    case base show ?case by (rule known)
  next
    case (step us vs)
    then obtain ev where transition: "lpp_domain_answers P B U D us ev vs"
      by (auto simp: lp_answer_steps_def)
    show ?case by (rule lpp_model_domain_answer_preserved[OF program builtin stable transition step.hyps(3)])
  qed
  have transition: "lpp_answer_transition P B U us (Some rho) tail"
    using event by (simp add: lpp_domain_answers_def)
  have shape: "us=(LPCGoals [],rho)#tail"
    by (rule lpp_answer_event_is_success[OF transition])
  have all: "\<forall>sigma. K (\<lambda>x. lp_isubst (rho x) sigma)"
    using invariant by (simp add: shape lpc_model_goals_def)
  show ?thesis using all[THEN spec, of LPIVar] by simp
qed

end
