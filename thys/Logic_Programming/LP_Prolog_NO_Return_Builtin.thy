theory LP_Prolog_NO_Return_Builtin
 imports LP_Prolog_Binary64_NO LP_Cut_NO_Return_Attachment
begin

text \<open>Builtin witnesses use the existing exact source outcome. Successful
substitutions update the active continuation and its return environment only;
failure resumes the saved frame with its own environment.\<close>

lemma lpp_return_success_attach:
 assumes outcome: "U f input_terms (LPPBuiltinSuccess sigma)"
 shows "lpp_answer_transition P B U
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),eta)#es)) None
   (lpc_attach_answers rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
     \<lambda>x. lp_isubst (eta x) sigma)#es))"
 using lpp_answer_transition.success[where U=U and f=f and ts=input_terms and sigma=sigma and P=P and B=B
   and gs="gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest"
   and eta=eta and es="lpc_attach_answers rest es", OF outcome]
 by (simp add: lpc_attach_answers_def map_map o_def lp_cut_map_comp lp_ieval_subst)

lemma lpp_return_success_attach_source:
 assumes selected: "(f,length input_terms)\<in>lpp_builtin_signature"
   and outcome: "U f input_terms (LPPBuiltinSuccess sigma)"
 shows "(lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),eta)#es),
   lpc_attach rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
     \<lambda>x. lp_isubst (eta x) sigma)#es)) \<in> lpp_builtin_source P U"
proof -
 note step = lpp_return_success_attach[where U=U and f=f and input_terms=input_terms and sigma=sigma, OF outcome, of P lpp_builtin_signature rest gs eta es]
 have raw: "(lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),eta)#es),
   lpc_attach rest ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
     \<lambda>x. lp_isubst (eta x) sigma)#es)) \<in> lpp_atomic_source P lpp_builtin_signature U"
   using lpp_answer_transition_erases[OF step] by (simp add: lpc_attach_answers_erases)
 show ?thesis using raw selected by (auto simp: lp_prolog_source_def lpp_builtin_active_def)
qed

lemma lpp_return_failure_attach_source:
 assumes selected: "(f,length input_terms)\<in>lpp_builtin_signature"
   and outcome: "U f input_terms LPPBuiltinFailure"
 shows "(lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),eta)#es),
   lpc_attach rest es) \<in> lpp_builtin_source P U"
 using lpp_atomic_source.failure[where U=U and f=f and ts=input_terms and P=P and B=lpp_builtin_signature
   and gs="gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest" and es="lpc_attach rest es", OF outcome] selected
 by (auto simp: lp_prolog_source_def lpp_builtin_active_def)

lemma lpp_machine_is_success_outcome:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
   and chosen: "lpp_machine_unifier a v=Some mu"
 shows "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback) ''2:is''
   [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]
   (LPPBuiltinSuccess (\<lambda>x. lp_ieval (mu x) LPIVar))"
proof -
 have evaluated_source: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
   (lp_ieval (lpp_machine_expression_term e) LPIVar) (LPIFun (LPCUser (lpp_machine_name v)) [])"
   using lpp_machine_evaluation_sound[OF evaluated, where eta=LPIVar and fallback=fallback]
   by (simp only: lpp_machine_value_named)
 note outcome = lpp_stable_source_is_evaluated[OF lpp_binary64_profile_integer_compatible evaluated_source, of "lp_ieval a LPIVar"]
 have unifier: "lpp_scalar_unifier (lp_ieval a LPIVar) (lpp_machine_name v) =
   Some (\<lambda>x. lp_ieval (mu x) LPIVar)"
   using lpp_machine_unifier_evaluation[OF lpp_machine_value_named[of v], of a] chosen by simp
 show ?thesis using outcome by (simp only: unifier option.case)
qed

lemma lpp_machine_is_return_attach:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
   and chosen: "lpp_machine_unifier a v=Some mu"
 shows "(lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,lpp_machine_expression_term e])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs),map (\<lambda>t. t\<cdot>mu) payload)#saved)))
   \<in> lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 note outcome = lpp_machine_is_success_outcome[OF evaluated chosen, of fallback]
 have selected: "(''2:is'',length [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar])\<in>lpp_builtin_signature"
   by (simp add: lpp_builtin_signature_def)
 note step = lpp_return_success_attach_source[where U="lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
   and f="''2:is''" and input_terms="[lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]"
   and sigma="\<lambda>x. lp_ieval (mu x) LPIVar", OF selected outcome,
   of rest "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs" "lpc_return_env payload LPIVar"
     "lpc_return_eval LPIVar saved" P]
 have answers: "lpc_return_env (map (\<lambda>t. t\<cdot>mu) payload) LPIVar =
   (\<lambda>x. lp_isubst (lpc_return_env payload LPIVar x) (\<lambda>y. lp_ieval (mu y) LPIVar))"
   by (rule lpc_return_env_active) (simp add: map_map o_def lp_ieval_finite_subst lp_ieval_subst)
 show ?thesis using step by (simp add: lpc_return_eval_def answers map_map o_def
   lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst)
qed

lemma lpp_return_boolean_attach_source:
 assumes selected: "(f,length input_terms)\<in>lpp_builtin_signature"
   and outcome: "U f input_terms (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 shows "(lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),eta)#es),
   lpc_attach rest (if held then (LPCGoals gs,eta)#es else es))\<in>lpp_builtin_source P U"
proof (cases held)
 case True
 have success: "U f input_terms (LPPBuiltinSuccess LPIVar)" using outcome True by simp
 note step = lpp_return_success_attach_source[where U=U and f=f and input_terms=input_terms and sigma=LPIVar,
   OF selected success, of rest gs eta es P]
 show ?thesis using step True by simp
next
 case False
 have failure: "U f input_terms LPPBuiltinFailure" using outcome False by simp
 note step = lpp_return_failure_attach_source[where U=U and f=f and input_terms=input_terms,
   OF selected failure, of rest gs eta es P]
 show ?thesis using step False by simp
qed

lemma lpp_machine_comparison_return_attach:
 assumes name: "lpp_comparison_descriptor f comparison reversed"
   and left: "lpp_machine_evaluate left=Some x"
   and right: "lpp_machine_evaluate right=Some y"
   and held: "held=lpp_integer_compare comparison
     (fst (lpp_machine_fraction (if reversed then y else x)) * snd (lpp_machine_fraction (if reversed then x else y)))
     (fst (lpp_machine_fraction (if reversed then x else y)) * snd (lpp_machine_fraction (if reversed then y else x)))"
 shows "(lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser f) [lpp_machine_expression_term left,lpp_machine_expression_term right])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar (if held then (LPCGoals gs,payload)#saved else saved)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?a = "lp_ieval (lpp_machine_expression_term left) LPIVar"
 let ?b = "lp_ieval (lpp_machine_expression_term right) LPIVar"
 let ?U = "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
 have compared: "lpp_stable_compare_values (lpp_binary64_profile_operation fallback) comparison
   (if reversed then ?b else ?a) (if reversed then ?a else ?b) held"
   using lpp_machine_comparison_value[OF left right, where eta=LPIVar and comparison=comparison and fallback=fallback]
     lpp_machine_comparison_value[OF right left, where eta=LPIVar and comparison=comparison and fallback=fallback]
   by (cases reversed) (simp_all add: held)
 have outcome: "?U f [?a,?b] (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
   by (rule lpp_stable_source_comparison_evaluated[OF lpp_binary64_profile_integer_compatible name compared])
 have selected: "(f,length [?a,?b])\<in>lpp_builtin_signature"
   using lpp_comparison_selected[OF name] by (simp add: numeral_2_eq_2)
 note step = lpp_return_boolean_attach_source[where U="?U" and f=f and input_terms="[?a,?b]" and held=held,
   OF selected outcome, of rest "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
     "lpc_return_env payload LPIVar" "lpc_return_eval LPIVar saved" P]
 show ?thesis using step by (cases held) (simp_all add: lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_return_success_attach_source}, @{thm lpp_return_failure_attach_source},
 @{thm lpp_machine_is_return_attach}, @{thm lpp_machine_comparison_return_attach}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted builtin return attachment dependency" else ();
\<close>
end
