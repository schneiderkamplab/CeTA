theory LP_Prolog_Functor_Leaf_Support
 imports LP_Prolog_Return_Leaf_Node_Contract
begin

lemma lpp_argument_list_runtime_support:
 "set2_lp_iterm (lpp_argument_list ts) = (\<Union>t\<in>set ts. set2_lp_iterm t)"
 by (induct ts) auto

lemma lpp_functor_observation_runtime_support:
 assumes "lpp_functor_observation names term_value name_term arglist"
 shows "set2_lp_iterm term_value = set2_lp_iterm arglist"
 using assms by (cases "term_value")
  (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def
    lpp_argument_list_runtime_support)

lemma lpp_functor_fact_runtime_support:
 "lpp_functor_fact_holds names eta (LPPFunctorFact term_value name_term arglist) \<Longrightarrow>
  set2_lp_iterm (lp_ieval term_value eta) = set2_lp_iterm (lp_ieval arglist eta)"
 by (simp add: lpp_functor_observation_runtime_support)

text \<open>An ordered sequence of existing relational facts may extend known
support. This is a finite checked derivation; the semantics concerns runtime
variables, not equality of the syntactic variable names on the two sides.\<close>

fun lpp_functor_support_closure where
 "lpp_functor_support_closure [] V = V"
| "lpp_functor_support_closure (LPPFunctorFact term_value name_term arglist#facts) V =
   lpp_functor_support_closure facts
    (if vars_term arglist \<subseteq> V then V \<union> vars_term term_value else V)"

lemma lpp_functor_support_closure_sound:
 assumes facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and initial: "\<And>x. x\<in>V \<Longrightarrow> set2_lp_iterm (eta x) \<subseteq> S"
 shows "\<And>x. x\<in>lpp_functor_support_closure facts V \<Longrightarrow>
   set2_lp_iterm (eta x) \<subseteq> S"
 using facts initial
proof (induct facts arbitrary: V)
 case Nil then show ?case by simp
next
 case (Cons fact facts)
 obtain term_value name_term arglist where fact: "fact=LPPFunctorFact term_value name_term arglist"
  by (cases fact) auto
 have held: "lpp_functor_fact_holds names eta (LPPFunctorFact term_value name_term arglist)"
  using Cons.prems(2) by (simp add: fact)
 have equal: "(\<Union>x\<in>vars_term term_value. set2_lp_iterm (eta x)) =
   (\<Union>x\<in>vars_term arglist. set2_lp_iterm (eta x))"
  using lpp_functor_fact_runtime_support[OF held]
  by (simp add: lpp_evaluation_runtime_support)
 have extended: "set2_lp_iterm (eta y) \<subseteq> S"
  if "y\<in>(if vars_term arglist \<subseteq> V then V \<union> vars_term term_value else V)" for y
  using that equal Cons.prems(3) by (auto split: if_splits; blast)
 show ?case using Cons.hyps[OF _ _ extended] Cons.prems
  by (auto simp: fact)
qed

lemma lpp_functor_support_attached_positive:
 "''whole'' \<in> lpp_functor_support_closure
   [LPPFunctorFact (Var ''whole'') (Var ''name'') (Var ''children'')] {''children''}"
 by simp

lemma lpp_functor_support_missing_fact_rejected:
 "''whole'' \<notin> lpp_functor_support_closure [] {''children''}"
 by simp

lemma lpp_functor_support_missing_arguments_rejected:
 "''whole'' \<notin> lpp_functor_support_closure
   [LPPFunctorFact (Var ''whole'') (Var ''name'') (Var ''children'')] {''other''}"
 by simp

ML \<open>
val checked = @{thms lpp_argument_list_runtime_support lpp_functor_observation_runtime_support
 lpp_functor_fact_runtime_support lpp_functor_support_closure_sound
 lpp_functor_support_attached_positive lpp_functor_support_missing_fact_rejected
 lpp_functor_support_missing_arguments_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational leaf support" else ();
\<close>
end
