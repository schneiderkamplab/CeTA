theory LP_Prolog_Separation_Univ_Transport
 imports LP_Prolog_Finite_Pair_Unify LP_Prolog_Finite_Execution_Step
begin

text \<open>Support separation follows the actual constructor observation and
  initialization equation, not syntactic variable names. The reflexive MGU
  transport below requires occurrence in its actual continuation.\<close>

lemma lpp_functor_observation_support:
 "lpp_functor_observation names value_term name_term arglist \<Longrightarrow>
  set2_lp_iterm value_term=set2_lp_iterm arglist"
 by (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def lpp_argument_list_support)

lemma lpp_initialized_univ_pair_separation:
 assumes observation: "lpp_functor_fact_holds names eta (LPPFunctorFact value_term name_term arglist)"
 and equation: "lp_ieval input_template eta=lp_ieval value_term eta"
 and separated: "list_all (lpp_separation_holds eta)
   [LPPSeparate input_template output_name,LPPSeparate input_template output_args]"
 shows "lpp_separation_holds eta
   (LPPSeparate (Fun f [output_name,output_args]) (Fun f [name_term,arglist]))"
 using observation equation separated
 by (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def lpp_argument_list_support)

lemma lpp_reflexive_pair_context_transport:
 assumes mgu: "lpc_mgu_unify input_value input_value
   (LPCUnify (lp_ieval left_term eta) (lp_ieval right_term eta)#gs) sigma"
 and finite: "lpp_finite_goals (LPCUnify (lp_ieval left_term eta) (lp_ieval right_term eta)#gs)"
 and separated: "lpp_separation_holds eta (LPPSeparate left_term right_term)"
 shows "lpp_separation_holds (\<lambda>x. lp_isubst (eta x) sigma) (LPPSeparate left_term right_term)"
proof -
 have inputs: "lpp_finite_term (lp_ieval left_term eta)" "lpp_finite_term (lp_ieval right_term eta)"
  using finite by (auto simp: lpp_finite_goals_def lp_cut_terms.simps)
 have disjoint: "set2_lp_iterm (lp_ieval left_term eta)\<inter>set2_lp_iterm (lp_ieval right_term eta)={}"
  using separated by simp
 have after: "set2_lp_iterm (lp_isubst (lp_ieval left_term eta) sigma)\<inter>
   set2_lp_iterm (lp_isubst (lp_ieval right_term eta) sigma)={}"
  by (rule lpp_reflexive_mgu_continuation_separation[OF mgu, where
    g="LPCUnify (lp_ieval left_term eta) (lp_ieval right_term eta)" and
    h="LPCUnify (lp_ieval left_term eta) (lp_ieval right_term eta)"])
    (use inputs disjoint in \<open>auto simp: lp_cut_terms.simps\<close>)
 show ?thesis using after by (simp add: lp_ieval_subst[symmetric])
qed

lemma lpp_finite_separated_pair_base_step:
 assumes step: "lpc_answer_transition P
   ((LPCGoals (LPCUnify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b])#gs),eta)#saved) event tt"
 and finite: "lpp_finite_execution
   ((LPCGoals (LPCUnify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b])#gs),eta)#saved)"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 shows "lpp_finite_execution tt"
 using step finite distinct fresh
 by (cases rule: lpc_answer_transition.cases)
   (auto simp: lpp_finite_execution_def lpp_finite_goals_def list_all_iff
     dest: lpp_separated_pair_mgu_finite_goals)

ML \<open>
val checked = @{thms lpp_functor_observation_support lpp_initialized_univ_pair_separation
 lpp_reflexive_pair_context_transport lpp_finite_separated_pair_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ separation transport dependency" else ();
\<close>
end
