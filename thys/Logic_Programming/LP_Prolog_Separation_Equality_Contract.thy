theory LP_Prolog_Separation_Equality_Contract
 imports LP_Prolog_Separation_Equality_Action
begin

lemma lpp_separation_equality_node_contract:
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
   J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
   list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
 and failure_separation: "\<And>eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   list_all (lpp_separation_holds eta) no_separation"
 and stable: "\<And>eta ev ys.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) J returned arity i"
 unfolding lpp_premised_functor_node_contract_def
proof (intro allI impI)
 fix eta
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and sn: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) vs v \<longrightarrow> J vs \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t = "[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 show "lp_answer_contract ?T (lpc_return_eval eta (states!i)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
 proof (rule lp_answer_contract_intro)
  fix ev ys assume step: "?T (lpc_return_eval eta (states!i)) ev ys"
  have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
    by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    (lpc_return_eval eta (states!i)) ev ys"
    using step supported by (simp add: lpp_domain_answers_def)
  have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
    by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
  have separation: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
    by (rule success_separation[OF conditions known free observed functors invariant])
  obtain v swaps where silent: "ev=None" and strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
   and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) v"
    using lpp_separation_functor_equality_node_sound[OF compatible transfer checked success_transport failure_transport
      separation failure_separation[OF conditions] known free observed functors base[unfolded shape]]
    by blast
  have preserved: "J ys" by (rule stable[OF conditions known free observed functors base invariant])
  have child: "lp_answer_contract ?T ys (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using lower strict rep preserved unfolding lpp_premised_functor_module_rep_def by blast
  have lifted: "lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  show "(\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using silent lifted by simp
 qed
qed

ML \<open>
val checked = @{thms lpp_separation_equality_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation equality contract" else ();
\<close>
end
