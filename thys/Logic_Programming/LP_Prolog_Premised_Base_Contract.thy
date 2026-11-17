theory LP_Prolog_Premised_Base_Contract
 imports LP_Prolog_Functor_Premised_Table
begin

text \<open>Common assembly for actual base-semantics steps. Every step supplies
its represented strict residual successor, actual return coverage and preserved
runtime invariant. Extra node conditions are local to the incoming valuation.\<close>

lemma lpp_premised_functor_base_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes clear: "lpp_no_builtin_frame (states!i)"
 and sound: "\<And>eta ev ys.
   node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   (\<exists>v swaps. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
       (lpc_return_scope_word swaps ys) v) \<and>
   (\<forall>rho. ev=Some rho \<longrightarrow>
      ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and> J ys"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   node_conditions J returned arity i"
 unfolding lpp_premised_functor_node_contract_def
proof (intro allI impI)
 fix eta
 assume conditions: "node_conditions i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and sn: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions vs v \<longrightarrow> J vs \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t = "[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 show "lp_answer_contract ?T (lpc_return_eval eta (states!i)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
 proof (rule lp_answer_contract_intro)
  fix ev ys assume step: "?T (lpc_return_eval eta (states!i)) ev ys"
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
    by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    (lpc_return_eval eta (states!i)) ev ys"
    using step supported by (simp add: lpp_domain_answers_def)
  have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
    by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
  obtain v swaps where strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
   and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_return_scope_word swaps ys) v"
   and emitted: "\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
   and preserved: "J ys"
    using sound[OF conditions known free observed functors invariant base] by blast
  have child: "lp_answer_contract ?T ys (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using lower strict rep preserved unfolding lpp_premised_functor_module_rep_def by blast
  have lifted: "lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  show "(\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using emitted lifted by blast
 qed
qed

lemma lpp_exhausted_premised_functor_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes exhausted: "states!i=[]"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   node_conditions J returned arity i"
 by (rule lpp_premised_functor_base_node_contract)
   (use exhausted in \<open>auto simp: lpc_return_eval_def elim: lpc_answer_transition.cases\<close>)

ML \<open>
val checked = @{thms lpp_premised_functor_base_node_contract lpp_exhausted_premised_functor_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted premised base node contract" else ();
\<close>
end
