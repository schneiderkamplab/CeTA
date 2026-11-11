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
    and call_model: "\<And>f ts a sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      M (lp_isubst a sigma) \<Longrightarrow> M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch_model: "\<And>f ts cs ys ns sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call_control: "\<And>f ts a. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and branch_control: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      list_all (lpc_return_control_igoal F) (cs@ys@ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
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
next
  case (call f ts a gs eta es)
  have member: "f\<in>F" using call known by simp
  have before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using call known by simp
  have models: "\<And>sigma. M (lp_isubst a sigma) \<Longrightarrow>
    M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule call_model[OF member call(4)])
  have control: "lpc_return_control_igoal F (LPCAtom a)"
    by (rule call_control[OF member call(4)])
  show ?thesis using call known before models control
    by (auto simp: lpc_model_goals_def)
next
  case (branch f ts cs ys ns m gs es n eta)
  have member: "f\<in>F" using branch known by simp
  have safe: "list_all lpc_model_safe_goal (cs@ys@ns)"
    using branch(5) by (auto simp: list_all_iff dest: lpp_plain_goal_model_safe)
  have before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using branch known by simp
  have models: "\<And>sigma.
      (list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule branch_model[OF member branch(4)])
  have control: "list_all (lpc_return_control_igoal F) (cs@ys@ns)"
    by (rule branch_control[OF member branch(4)])
  show ?thesis using branch known safe before models control
    by (auto simp: lpc_model_goals_def)
next
  case (choice f ts left right gs eta es)
  have member: "f\<in>F" using choice known by simp
  show ?thesis using no_choice[OF member] choice(4) by blast
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
    and call_model: "\<And>f ts a sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      M (lp_isubst a sigma) \<Longrightarrow> M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch_model: "\<And>f ts cs ys ns sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call_control: "\<And>f ts a. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and branch_control: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      list_all (lpc_return_control_igoal F) (cs@ys@ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and step: "lpp_domain_answers P B U D ss event tt"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
  shows "list_all (lpc_scoped_model_frame F M K) tt"
  using step known lpp_scoped_model_answer_preserved[where U=U and M=M and F=F, OF program builtin probe_model probe_control call_model branch_model call_control branch_control no_choice stable]
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
    and call_model: "\<And>f ts a sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      M (lp_isubst a sigma) \<Longrightarrow> M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch_model: "\<And>f ts cs ys ns sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call_control: "\<And>f ts a. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and branch_control: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      list_all (lpc_return_control_igoal F) (cs@ys@ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
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
    show ?case by (rule lpp_scoped_model_domain_answer_preserved[where U=U and M=M and F=F, OF program builtin probe_model probe_control call_model branch_model call_control branch_control no_choice stable transition step.hyps(3)])
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
    and no_call: "\<And>f ts a. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinCall a)"
    and no_branch: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinBranch cs ys ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
    and stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
  shows "K rho"
  by (rule lpp_scoped_model_actual_return[where U=U and M=M and F=F, OF program builtin _ _ _ _ _ _ no_choice stable known actual])
    (use no_probe no_call no_branch in blast)+

end
