theory LP_Prolog_Finite_Return_Control
 imports LP_Prolog_Spine_Shape
begin

text \<open>Most-generality constrains the selected call, body and continuation.
It does not constrain unrelated answer slots. A ground fact with no continuation
therefore admits arbitrary substitution on a captured variable. This control
prevents treating finite captured values as substitution-invariant return facts.\<close>

lemma lpp_ground_fact_unobserved_substitution:
 "lpc_mgu_resolve (LPIFun f []) [] (Fun f []) [] sigma rho"
 by (simp add: lpc_mgu_resolve_def)

lemma lpp_ground_fact_can_change_unobserved_answer:
 "lpc_answer_transition [(Fun f [],[])]
   [(LPCClause [LPCAtom (LPIFun f [])] 0 m,LPIVar)] None
   [(LPCGoals [],sigma)]"
proof -
 have step: "lpc_answer_transition [(Fun f [],[])]
   [(LPCClause [LPCAtom (LPIFun f [])] 0 m,LPIVar)] None
   [(LPCGoals [],\<lambda>x. lp_isubst (LPIVar x) sigma)]"
   using lpc_answer_transition.resolve[where P="[(Fun f [],[])]" and c=0
     and a="LPIFun f []" and gs="[]" and \<rho>=LPIVar
     and \<sigma>=sigma and \<eta>=LPIVar and es="[]" and m=m]
   by (simp add: lpc_mgu_resolve_def)
 show ?thesis using step by simp
qed


lemma lpp_unobserved_finite_answer_not_preserved:
 assumes cyclic: "cycle_term=LPIFun f [cycle_term]"
 shows "lpp_finite_term (LPIVar x) \<and>
   \<not>lpp_finite_term (lp_isubst (LPIVar x) (LPIVar(x:=cycle_term))) \<and>
   lpc_mgu_resolve (LPIFun g []) [] (Fun g []) [] (LPIVar(x:=cycle_term)) rho"
 using lpp_finite_constructor_not_self_child[of cycle_term f] cyclic
   lpp_ground_fact_unobserved_substitution[of g "LPIVar(x:=cycle_term)" rho] by auto


lemma lpp_ground_fact_preserves_attached_finite_value:
 assumes mgu: "lpc_mgu_resolve (LPIFun f []) gs (Fun f []) [] sigma rho"
 and finite: "lpp_finite_goals gs"
 and observed: "LPCAtom (LPIFun g [LPIVar x])\<in>set gs"
 shows "lpp_finite_term (sigma x)"
proof -
 have comparison: "lp_isubst (LPIFun f []) LPIVar=lp_ieval (Fun f []) LPIVar" by simp
 have terms: "lpp_finite_term (lp_isubst term_value LPIVar)"
   if "goal\<in>set gs" "term_value\<in>set (lp_cut_terms goal)" for goal term_value
   using finite that by (auto simp: lpp_finite_goals_def list_all_iff)
 have member: "LPIFun g [LPIVar x]\<in>set (lp_cut_terms (LPCAtom (LPIFun g [LPIVar x])))"
   by (subst lp_cut_terms.simps(1); rule list.set_intros(1))
 have protected: "lpp_finite_term (lp_isubst (LPIFun g [LPIVar x]) sigma)"
   by (rule lpp_mgu_continuation_finite[OF mgu comparison terms observed member])
 show ?thesis using protected by simp
qed

ML \<open>
val checked = @{thms lpp_ground_fact_unobserved_substitution
 lpp_ground_fact_can_change_unobserved_answer lpp_unobserved_finite_answer_not_preserved
 lpp_ground_fact_preserves_attached_finite_value};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite return control" else ();
\<close>
end
