theory LP_Prolog_Separation_Pair_Control
 imports LP_Prolog_Separation_Equality_Contract
begin

fun lpp_check_separated_pair where
 "lpp_check_separated_pair F facts (Fun f [Var x,Var y]) (Fun g [a,b]) =
   (f=g \<and> x\<noteq>y \<and> x\<in>set F \<and> y\<in>set F \<and>
    LPPSeparate (Fun f [Var x,Var y]) (Fun g [a,b])\<in>set facts)"
| "lpp_check_separated_pair F facts a b = False"

lemma lpp_checked_separated_pair_finite_step:
 assumes checked: "lpp_check_separated_pair F facts a b"
 and free: "lpc_free_knowledge (set F) eta"
 and separated: "list_all (lpp_separation_holds eta) facts"
 and step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved))"
 shows "lpp_finite_execution tt"
proof -
 obtain f x y c d where shape: "a=Fun f [Var x,Var y]" "b=Fun f [c,d]"
  and distinct: "x\<noteq>y" and members: "x\<in>set F" "y\<in>set F"
  and fact: "LPPSeparate a b\<in>set facts"
  using checked by (induction F facts a b rule: lpp_check_separated_pair.induct) auto
 obtain u v where images: "eta x=LPIVar u" "eta y=LPIVar v"
  using free members unfolding lpc_free_knowledge_def by blast
 have unequal: "u\<noteq>v"
  using free members distinct images by (auto simp: lpc_free_knowledge_def inj_on_def)
 have fresh: "{u,v}\<inter>(set2_lp_iterm (lp_ieval c eta)\<union>set2_lp_iterm (lp_ieval d eta))={}"
  using separated fact by (auto simp: list_all_iff shape images)
 show ?thesis
  by (rule lpp_finite_separated_pair_base_step[OF _ _ unequal fresh])
    (use step finite in \<open>simp_all add: shape images lpc_return_eval_def\<close>)
qed

lemma lpp_separated_pair_missing_fact_rejected:
 "facts=[] \<Longrightarrow> \<not>lpp_check_separated_pair F facts a b"
 by (induction F facts a b rule: lpp_check_separated_pair.induct) auto

lemma lpp_separated_pair_repeated_variable_rejected:
 "a=Fun f [Var x,Var x] \<Longrightarrow> \<not>lpp_check_separated_pair F facts a b"
 by (induction F facts a b rule: lpp_check_separated_pair.induct) auto

lemma lpp_separated_pair_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))"
 and success_separation: "\<And>eta sigma.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpp_finite_execution (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
   list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
 and failure_separation: "\<And>eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   list_all (lpp_separation_holds eta) no_separation"

 and pair: "lpp_check_separated_pair (Fs!i) (separation_contexts!i) a b"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (rule lpp_separation_equality_node_contract[OF compatible transfer checked shape
  success_transport failure_transport success_separation failure_separation])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have separated: "list_all (lpp_separation_holds eta) (separation_contexts!i)"
   using conditions by (simp add: lpp_separation_node_conditions_def)
 show "lpp_finite_execution ys"
   by (rule lpp_checked_separated_pair_finite_step[OF pair free separated step[unfolded shape] finite[unfolded shape]])
qed

ML \<open>
val checked = @{thms lpp_checked_separated_pair_finite_step lpp_separated_pair_missing_fact_rejected
 lpp_separated_pair_repeated_variable_rejected lpp_separated_pair_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation pair control" else ();
\<close>
end
