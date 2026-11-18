theory LP_Prolog_Attached_Univ_Finite_Steps
 imports LP_Prolog_Checked_Attached_Finite
begin

lemma lpp_attached_univ_finite_equality_steps:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first_step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) first_event middle"
 and second_step: "lpc_answer_transition P middle second_event result"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved))"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 shows "first_event=None \<and> second_event=None \<and> lpp_finite_execution middle \<and> lpp_finite_execution result"
proof -
 let ?left = "LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]"
 let ?right = "lpp_argument_list (LPIFun (names f) []#ts)"
 obtain sigma where first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify ?left ?right#(pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)) sigma"
 and silent: "first_event=None"
 and middle_shape: "middle=(LPCGoals (LPCUnify (lp_isubst ?left sigma) (lp_isubst ?right sigma)#
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t env) sigma)) rest)),
     \<lambda>slot. lp_isubst (env slot) sigma)#lpc_attach_answers rest saved"
  using first_step[unfolded lpc_attach_answers_def, simplified]
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: lpc_attach_answers_def lp_cut_map_comp o_def)
 have finite_middle: "lpp_finite_execution middle"
  by (rule lpp_finite_attached_reflexive_step[OF first_step finite refl])
 have finite_arguments: "list_all lpp_finite_term ts"
 and finite_pending: "lpp_finite_goals (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)"
 and finite_saved: "lpp_finite_execution (lpc_attach_answers rest saved)"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have success: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t tau))
    (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t env) sigma)) rest))"
  if second: "lpc_mgu_unify (lp_isubst ?left sigma) (lp_isubst ?right sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t env) sigma)) rest) tau" for tau
 proof -
  have actual_second: "lpc_mgu_unify (lp_isubst ?left sigma) (lp_isubst ?right sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
     (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)) tau"
   using second by (simp add: map_map lp_cut_map_comp o_def)
  show ?thesis using lpp_normalized_univ_sequence_finite[where names=names and f=f and ts=ts
    and x=x and y=y and sigma=sigma and tau=tau, OF first actual_second finite_arguments finite_pending distinct fresh]
   by (simp add: map_map lp_cut_map_comp o_def)
 qed
 show ?thesis using second_step silent finite_middle finite_saved success
  by (auto simp: middle_shape lpp_finite_execution_def elim: lpc_answer_transition.cases)
qed

lemma lpp_attached_univ_domain_invariants:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first_step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) first_event middle"
 and second_step: "lpp_domain_answers P B U D middle second_event result"
 and invariant: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#saved)"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved))"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow> {x,y}\<inter>set2_lp_iterm (env slot)={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "first_event=None \<and> second_event=None \<and> lpp_finite_execution middle \<and> lpp_finite_execution result \<and> lpp_leaf_stack_invariant A specs result"
proof -
 have first_base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) first_event middle"
  using first_step by (auto simp: lpc_attach_answers_def intro: lpp_observer_equality_base)
 obtain a b gs rho es where middle_shape: "middle=(LPCGoals (LPCUnify a b#gs),rho)#es"
  using first_base[unfolded lpc_attach_answers_def, simplified]
  by (cases rule: lpc_answer_transition.cases) auto
 have second_base: "lpc_answer_transition P middle second_event result"
  using second_step unfolding middle_shape by (rule lpp_observer_equality_base)
 have finite_arguments: "list_all lpp_finite_term ts"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have finite_results: "first_event=None \<and> second_event=None \<and>
   lpp_finite_execution middle \<and> lpp_finite_execution result"
  by (rule lpp_attached_univ_finite_equality_steps[where names=names and f=f and ts=ts and x=x and y=y
    and env=env and rest=rest and pending=pending, OF first_base second_base finite distinct fresh])
 have leaf_result: "first_event=None \<and> second_event=None \<and> lpp_leaf_stack_invariant A specs result"
  by (rule lpp_attached_univ_domain_equality_steps[where names=names and f=f and ts=ts and x=x and y=y
    and env=env and rest=rest and pending=pending, OF first_step second_step invariant finite_arguments distinct fresh protected covered])
 show ?thesis using finite_results leaf_result by simp
qed

ML \<open>
val checked = @{thms lpp_attached_univ_finite_equality_steps lpp_attached_univ_domain_invariants};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted finite attached univ sequence" else ();
\<close>
end
