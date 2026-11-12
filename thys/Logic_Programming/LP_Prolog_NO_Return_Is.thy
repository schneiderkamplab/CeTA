theory LP_Prolog_NO_Return_Is
 imports LP_Prolog_NO_Return_Ordinary
begin

lemma lpp_machine_is_failure_outcome:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
   and rejected: "lpp_machine_unifier a v=None"
 shows "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback) ''2:is''
   [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar] LPPBuiltinFailure"
proof -
 have evaluated_source: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
   (lp_ieval (lpp_machine_expression_term e) LPIVar) (LPIFun (LPCUser (lpp_machine_name v)) [])"
   using lpp_machine_evaluation_sound[OF evaluated, where eta=LPIVar and fallback=fallback]
   by (simp only: lpp_machine_value_named)
 note outcome = lpp_stable_source_is_evaluated[OF lpp_binary64_profile_integer_compatible evaluated_source, of "lp_ieval a LPIVar"]
 have unifier: "lpp_scalar_unifier (lp_ieval a LPIVar) (lpp_machine_name v)=None"
   using lpp_machine_unifier_evaluation[OF lpp_machine_value_named[of v], of a] rejected by simp
 show ?thesis using outcome by (simp only: unifier option.case)
qed

lemma lpp_machine_is_return_failure_attach:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
   and rejected: "lpp_machine_unifier a v=None"
 shows "(lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,lpp_machine_expression_term e])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar saved))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 note outcome = lpp_machine_is_failure_outcome[OF evaluated rejected, of fallback]
 have selected: "(''2:is'',length [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar])\<in>lpp_builtin_signature"
   by (simp add: lpp_builtin_signature_def)
 note step = lpp_return_failure_attach_source[where U="lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
   and f="''2:is''" and input_terms="[lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]",
   OF selected outcome, of rest "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
     "lpc_return_env payload LPIVar" "lpc_return_eval LPIVar saved" P]
 show ?thesis using step by (simp add: lpc_return_eval_def)
qed

fun lpp_no_return_is where
 "lpp_no_return_is e ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),payload)#saved) tt =
   (f=''2:is'' \<and> b=lpp_machine_expression_term e \<and>
    (case lpp_machine_evaluate e of None \<Rightarrow> False | Some v \<Rightarrow>
      tt=(case lpp_machine_unifier a v of None \<Rightarrow> saved | Some mu \<Rightarrow>
        (LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs),map (\<lambda>t. t\<cdot>mu) payload)#saved)))"
| "lpp_no_return_is e ss tt = False"

lemma lpp_no_return_is_sound:
 assumes checked: "lpp_no_return_is e ss tt"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),lpc_attach rest (lpc_return_eval LPIVar tt))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 using checked
 by (induct e ss tt rule: lpp_no_return_is.induct)
   (auto intro: lpp_machine_is_return_attach lpp_machine_is_return_failure_attach split: option.splits)

ML \<open>
val checked = [@{thm lpp_machine_is_failure_outcome}, @{thm lpp_machine_is_return_failure_attach},
 @{thm lpp_no_return_is_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked binary64 return evaluation" else ();
\<close>
end
