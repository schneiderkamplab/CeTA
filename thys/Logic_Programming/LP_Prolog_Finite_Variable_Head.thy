theory LP_Prolog_Finite_Variable_Head
 imports LP_Prolog_Finite_Term_Transport LP_Prolog_Partial_Integer_Interface
begin

text \<open>A linear variable head has a finite comparison unifier for finite
actual arguments. Most-generality reflects finiteness back to every selected
body term and caller continuation term. This does not cover arbitrary heads
or rational equality steps.\<close>

lemma lpp_partial_arguments_finite:
 assumes finite: "list_all lpp_finite_term actuals"
 shows "lpp_finite_term (lpp_partial_arguments H actuals x)"
proof (cases "map_of (zip H actuals) x")
 case None then show ?thesis by (simp add: lpp_partial_arguments_def)
next
 case (Some t)
 have "(x,t)\<in>set (zip H actuals)" by (rule map_of_SomeD[OF Some])
 then have "t\<in>set actuals" by (rule set_zip_rightD)
 then show ?thesis using finite Some
   by (simp add: lpp_partial_arguments_def list_all_iff)
qed

lemma lpp_variable_head_finite_comparison:
 assumes lengths: "length H=length actuals" and distinct: "distinct H"
 shows "lp_isubst (LPIFun f actuals) LPIVar =
   lp_ieval (Fun f (map Var H)) (lpp_partial_arguments H actuals)"
 using lpp_partial_arguments_exact[OF lengths distinct] by (simp add: map_map o_def)

lemma lpp_variable_head_finite_body:
 assumes mgu: "lpc_mgu_resolve (LPIFun f actuals) gs (Fun f (map Var H)) bs sigma rho"
   and lengths: "length H=length actuals" and distinct: "distinct H"
   and finite: "list_all lpp_finite_term actuals"
   and member: "g\<in>set bs" "t\<in>set (lp_cut_terms g)"
 shows "lpp_finite_term (lp_ieval t rho)"
proof (rule lpp_finite_term_eval)
 fix x assume x: "x\<in>vars_term t"
 show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu
       lpp_variable_head_finite_comparison[OF lengths distinct] member x
       lpp_partial_arguments_finite[OF finite]])
qed

lemma lpp_variable_head_finite_continuation:
 assumes mgu: "lpc_mgu_resolve (LPIFun f actuals) gs (Fun f (map Var H)) bs sigma rho"
   and lengths: "length H=length actuals" and distinct: "distinct H"
   and finite: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow> lpp_finite_term t"
   and member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 shows "lpp_finite_term (lp_isubst t sigma)"
 by (rule lpp_mgu_continuation_finite[OF mgu
     lpp_variable_head_finite_comparison[OF lengths distinct] _ member])
   (simp add: finite)

ML \<open>
val checked = [@{thm lpp_variable_head_finite_body}, @{thm lpp_variable_head_finite_continuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite variable-head transport" else ();
\<close>
end
