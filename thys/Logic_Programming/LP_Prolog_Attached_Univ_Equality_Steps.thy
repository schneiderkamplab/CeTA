theory LP_Prolog_Attached_Univ_Equality_Steps
 imports LP_Prolog_Observer_Univ_Contract LP_Prolog_Attached_Pair_Intermediate
begin

text \<open>These are actual transitions, including arbitrary most-general
unifiers on the full continuation. Saved alternatives keep their own
observation environments. The first equality may rename live variables.\<close>

lemma lpp_attached_reflexive_pair_step:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify input_term input_term#LPCUnify left right#pending),env)#saved)) event result"
 and invariant: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and finite_left: "lpp_finite_term left"
 and finite_right: "lpp_finite_term right"
 and separated: "set2_lp_iterm left\<inter>set2_lp_iterm right={}"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm left\<inter>set2_lp_iterm (env slot)={}"
 shows "event=None \<and> lpp_leaf_stack_invariant A specs result"
proof -
 obtain sigma where mgu: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#(pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)) sigma"
 and silent: "event=None"
 and result_shape: "result=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
   (LPCUnify left right#(pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest))),
    \<lambda>slot. lp_isubst (env slot) sigma)#lpc_attach_answers rest saved"
  using step by (auto simp: lpc_attach_answers_def elim: lpc_answer_transition.cases)
 have original: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#lpc_attach_answers rest saved)"
  using invariant by (simp add: lpp_leaf_stack_invariant_def lpc_attach_answers_def list_all_iff)
 have preserved: "lpp_leaf_stack_invariant A specs result"
  using lpp_attached_pair_intermediate_stack[OF mgu original covered finite_left finite_right separated protected]
  by (simp add: result_shape)
 show ?thesis using silent preserved by blast
qed

lemma lpp_attached_univ_equality_steps:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first_step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) first_event middle"
 and second_step: "lpc_answer_transition P middle second_event result"
 and invariant: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#saved)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow> {x,y}\<inter>set2_lp_iterm (env slot)={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "first_event=None \<and> second_event=None \<and> lpp_leaf_stack_invariant A specs result"
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
 have original: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#lpc_attach_answers rest saved)"
  using invariant by (simp add: lpp_leaf_stack_invariant_def lpc_attach_answers_def list_all_iff)
 have success: "lpp_leaf_stack_invariant A specs ((next_entry,\<lambda>slot. lp_isubst (lp_isubst (env slot) sigma) tau)#lpc_attach_answers rest saved)"
  if second: "lpc_mgu_unify (lp_isubst ?left sigma) (lp_isubst ?right sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) pending @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t env) sigma)) rest) tau" for tau next_entry
  by (rule lpp_attached_normalized_univ_leaf_stack[where eta=env and sigma=sigma and tau=tau and names=names and f=f and ts=ts and x=x and y=y and pending_goals=pending and gs=rest, OF first second original finite distinct fresh protected covered])
 have fallback: "lpp_leaf_stack_invariant A specs (lpc_attach_answers rest saved)"
  using invariant by (simp add: lpp_leaf_stack_invariant_def lpc_attach_answers_def list_all_iff)
 show ?thesis using second_step silent success fallback
  by (auto simp: middle_shape elim: lpc_answer_transition.cases)
qed

lemma lpp_attached_univ_domain_equality_steps:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first_step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
       (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) first_event middle"
 and second_step: "lpp_domain_answers P B U D middle second_event result"
 and invariant: "lpp_leaf_stack_invariant A specs ((frame_entry,env)#saved)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow> {x,y}\<inter>set2_lp_iterm (env slot)={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "first_event=None \<and> second_event=None \<and> lpp_leaf_stack_invariant A specs result"
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
 show ?thesis by (rule lpp_attached_univ_equality_steps[where names=names and f=f and ts=ts and x=x and y=y and env=env and rest=rest and pending=pending, OF first_base second_base invariant finite distinct fresh protected covered])
qed

ML \<open>
val checked = @{thms lpp_attached_reflexive_pair_step lpp_attached_univ_equality_steps lpp_attached_univ_domain_equality_steps};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached equality steps" else ();
\<close>
end
