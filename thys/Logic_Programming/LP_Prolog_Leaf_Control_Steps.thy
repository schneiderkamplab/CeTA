theory LP_Prolog_Leaf_Control_Steps
 imports LP_Prolog_Univ_Leaf_Node_Contract LP_Prolog_Separation_Ordinary_Check
begin

lemma lpp_leaf_stack_scope:
 "lpp_leaf_stack_invariant A specs (lpc_return_scope r ss) = lpp_leaf_stack_invariant A specs ss"
 by (auto simp: lpp_leaf_stack_invariant_def list_all_iff)

lemma lpp_leaf_stack_scopes:
 "lpp_leaf_stack_invariant A specs (lpc_return_scope_word swaps ss) = lpp_leaf_stack_invariant A specs ss"
proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons pair swaps)
 obtain a b where pair: "pair=(a,b)" by (cases pair) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_leaf_stack_scope)
qed

lemma lpp_leaf_simple_base_step:
 assumes simple: "lpp_simple_control_frame ss"
 and step: "lpc_answer_transition P ss event tt"
 and invariant: "lpp_leaf_stack_invariant A specs ss"
 shows "lpp_leaf_stack_invariant A specs tt"
 by (rule lpp_leaf_stack_base_step[OF step invariant]) (use simple in auto)

lemma lpp_leaf_functor_test_step:
 assumes name: "lpp_var_name f"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved))"
 shows "lpp_leaf_stack_invariant A specs tt"
 using step invariant
 by (auto simp: lpp_domain_answers_def lpc_return_eval_def lpp_univ_term_test_step[OF name]
   lpp_leaf_stack_invariant_def split: if_splits)

lemma lpp_leaf_is_normalization:
 assumes invariant: "lpp_leaf_stack_invariant A specs (lpc_return_eval eta
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved))"
 shows "lpp_leaf_stack_invariant A specs ((LPCGoals
   (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
 using invariant by (simp add: lpc_return_eval_def lpp_leaf_stack_invariant_def)

ML \<open>
val checked = @{thms lpp_leaf_stack_scope lpp_leaf_stack_scopes lpp_leaf_simple_base_step
 lpp_leaf_functor_test_step lpp_leaf_is_normalization};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf control steps" else ();
\<close>
end
