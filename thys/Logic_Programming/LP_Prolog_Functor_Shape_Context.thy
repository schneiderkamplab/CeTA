theory LP_Prolog_Functor_Shape_Context
 imports LP_Prolog_Functor_Context LP_Prolog_Evaluation_Context
begin

definition lpp_spine_grammar where
 "lpp_spine_grammar = [[(LPCUser ''0:prolog_data_5b5d'', []),
   (LPCUser ''2:prolog_data_2e'', [LPReturnAny,LPReturnShape 0])]]"

lemma lpp_argument_list_return_shape:
 "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lpp_argument_list ts)"
proof (induct ts)
 case Nil
 show ?case unfolding lpp_argument_list.simps by (rule lp_return_shape_holds.node[where shapes="[]"])
   (simp_all add: lpp_spine_grammar_def)
next
 case (Cons h ts)
 show ?case unfolding lpp_argument_list.simps by (rule lp_return_shape_holds.node[where shapes="[LPReturnAny,LPReturnShape 0]"])
   (use Cons in \<open>auto simp: lpp_spine_grammar_def less_Suc_eq_0_disj
     intro: lp_return_shape_holds.any\<close>)
qed

lemma lpp_functor_argument_return_shape:
 assumes fact: "lpp_functor_fact_holds names eta (LPPFunctorFact value_term name_term arglist)"
 shows "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval arglist eta)"
 using fact lpp_argument_list_return_shape
 by (auto simp: lpp_functor_observation_def lpp_constructor_arguments_def)

fun lpp_functor_shape_observation where
 "lpp_functor_shape_observation (LPPFunctorFact t n ats) =
   LPPOShape lpp_spine_grammar (LPReturnShape 0) ats"

fun lpp_functor_shape_context where
 "lpp_functor_shape_context (facts,guards,observations) functors =
   (facts,guards,observations @ map lpp_functor_shape_observation functors)"

lemma lpp_functor_shape_context_empty[simp]:
 "lpp_functor_shape_context ctx []=ctx"
 by (cases ctx) simp

lemma lpp_functor_shape_context_evaluation:
 assumes observed: "lpp_evaluation_context_holds E SP ctx eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) fs"
 shows "lpp_evaluation_context_holds E SP (lpp_functor_shape_context ctx fs) eta"
proof -
 have "lpp_evaluation_observation_holds E eta (lpp_functor_shape_observation f)"
   if "f\<in>set fs" for f
   using functors that by (cases f) (auto simp: list_all_iff intro: lpp_functor_argument_return_shape)
 then show ?thesis using observed
   by (cases ctx) (auto simp: lpp_evaluation_context_holds_def list_all_iff)
qed

ML \<open>
val checked = @{thms lpp_functor_argument_return_shape lpp_functor_shape_context_evaluation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted functor shape acquisition" else ();
\<close>
end
