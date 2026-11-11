theory LP_Prolog_Binary64_Steps
 imports LP_Prolog_Binary64_Builtin
begin

lemma lpp_checked_boolean_step:
 assumes selected: "(f,length input_terms)\<in>lpp_builtin_signature"
   and outcome: "U f (map (\<lambda>t. lp_ieval t LPIVar) input_terms)
     (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 shows "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) input_terms)#gs)#es) LPIVar,
   lp_cut_state_eval (if held then LPCGoals gs#es else es) LPIVar)\<in>lpp_builtin_source P U"
 using lpp_atomic_source.success[where U=U and f=f
   and ts="(map (\<lambda>t. lp_ieval t LPIVar) input_terms)" and sigma=LPIVar and P=P and B=lpp_builtin_signature
   and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es"]
   lpp_atomic_source.failure[where U=U and f=f
   and ts="(map (\<lambda>t. lp_ieval t LPIVar) input_terms)" and P=P and B=lpp_builtin_signature
   and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es"] selected outcome
 by (cases held) (auto simp: lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def)

lemma lpp_machine_is_step:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
 shows "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,lpp_machine_expression_term e])#gs)#es) LPIVar,
   lp_cut_state_eval (case lpp_machine_unifier a v of None \<Rightarrow> es
     | Some mu \<Rightarrow> LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs)#es) LPIVar)
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?operation="lpp_binary64_profile_operation fallback"
 let ?U="lpp_stable_source_builtin ?operation"
 let ?f="lpp_machine_name v"
 have ev: "lpp_stable_scalar_evaluation ?operation
   (lp_ieval (lpp_machine_expression_term e) LPIVar) (LPIFun (LPCUser ?f) [])"
   using lpp_machine_evaluation_sound[OF evaluated, where fallback=fallback and eta=LPIVar]
   by (simp only: lpp_machine_value_named)
 have outcome: "?U ''2:is'' [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]
   (case lpp_scalar_unifier (lp_ieval a LPIVar) ?f of None \<Rightarrow> LPPBuiltinFailure
    | Some sigma \<Rightarrow> LPPBuiltinSuccess sigma)"
   by (rule lpp_stable_source_is_evaluated[OF lpp_binary64_profile_integer_compatible ev])
 have unifier: "map_option (\<lambda>mu x. lp_ieval (mu x) LPIVar) (lpp_machine_unifier a v)=
   lpp_scalar_unifier (lp_ieval a LPIVar) ?f"
   by (rule lpp_machine_unifier_evaluation[OF lpp_machine_value_named])
 show ?thesis
 proof (cases "lpp_machine_unifier a v")
  case None
  have failed: "?U ''2:is'' [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar] LPPBuiltinFailure"
    using outcome unifier None by simp
  show ?thesis using lpp_atomic_source.failure[where U="?U" and f="''2:is''"
    and ts="[lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]" and P=P and B=lpp_builtin_signature
    and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
    and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF failed]
    by (simp add: None lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def lpp_builtin_signature_def)
 next
  case (Some mu)
  have chosen: "lpp_scalar_unifier (lp_ieval a LPIVar) (lpp_machine_name v)=
    Some (\<lambda>x. lp_ieval (mu x) LPIVar)"
    using unifier Some by simp
  have success: "?U ''2:is'' [lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]
    (LPPBuiltinSuccess (\<lambda>x. lp_ieval (mu x) LPIVar))"
    using outcome by (simp only: chosen option.case)
  show ?thesis using lpp_atomic_source.success[where U="?U" and f="''2:is''"
    and ts="[lp_ieval a LPIVar,lp_ieval (lpp_machine_expression_term e) LPIVar]"
    and sigma="(\<lambda>x. lp_ieval (mu x) LPIVar)" and P=P and B=lpp_builtin_signature
    and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
    and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF success]
    by (simp add: Some lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def lpp_builtin_signature_def
      map_map o_def lp_cut_map_comp lp_ieval_subst lp_ieval_finite_subst)
 qed
qed

ML \<open>
val checked = [@{thm lpp_checked_boolean_step}, @{thm lpp_machine_is_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 source step dependency" else ();
\<close>
end
