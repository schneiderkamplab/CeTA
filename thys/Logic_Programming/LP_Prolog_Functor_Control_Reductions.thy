theory LP_Prolog_Functor_Control_Reductions
 imports LP_Prolog_Functor_Table_Contract LP_Prolog_Domain_Modular
begin

text \<open>Control reductions keep every saved alternative and its checked
  relational interface. Their invariant premise is deletion closure, not a
  claim that successful execution preserves facts on a failed alternative.\<close>

theorem lpp_functor_trim_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFTrim successor barriers e fs)"
 and deletion: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
proof (intro allI impI)
 fix eta
 assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<longrightarrow> J vs \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 let ?T="lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t="[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 let ?ret="\<lambda>rho. [(returned,map rho [0..<arity])]"
 have shape: "states!i=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
 and link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts (nds!i) successor
   (lpcn_ground (nds!i)) (lpcn_guards (nds!i)) [] (Fs!i) (contexts!i) (functor_contexts!i) e"
  using checked by (auto simp: lpp_check_functor_source_action_def)
 have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
 obtain v swaps where strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
  using lpp_stable_functor_link_sound[OF compatible transfer link equations refl known free observed functors] by blast
 have child_invariant: "J (lpc_return_eval eta successor)"
  by (rule deletion[OF _ invariant]) (simp add: shape lpc_return_eval_def)
 have child: "lp_answer_contract ?T (lpc_return_eval eta successor) (lp_ild Q) v ?ret"
  using lower strict rep child_invariant by (auto simp: lpp_stable_functor_module_rep_def)
 have lifted: "lp_answer_contract ?T (lpc_return_eval eta successor) (lp_ild Q) ?t ?ret"
  by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
 have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
  using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
 show "lp_answer_contract ?T (lpc_return_eval eta (states!i)) (lp_ild Q) ?t ?ret"
  using lpp_domain_contract_append_barriers[OF lifted suffix] by (simp add: shape lpc_return_eval_def)
qed

theorem lpp_functor_parallel_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFParallel links factss)"
 and deletion: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
proof (intro allI impI)
 fix eta
 assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<longrightarrow> J vs \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 let ?T="lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t="[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 let ?ret="\<lambda>rho. [(returned,map rho [0..<arity])]"
 show "lp_answer_contract ?T (lpc_return_eval eta (states!i)) (lp_ild Q) ?t ?ret"
 proof (rule lpp_domain_contract_singletons)
  fix entry assume member: "entry\<in>set (lpc_return_eval eta (states!i))"
  obtain j where index: "j<length (states!i)" and entry: "[entry]=lpc_return_eval eta [(states!i)!j]"
   using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
  have link: "lpp_check_evaluation_functor_link T (factss!j) fuel Q nds states contexts Fs functor_contexts (nds!i)
    [(states!i)!j] (lpcn_ground (nds!i)) (lpcn_guards (nds!i)) [] (Fs!i) (contexts!i) (functor_contexts!i) (links!j)"
   using checked index by (auto simp: lpp_check_functor_source_action_def list_all_iff)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
  and rep: "lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpc_return_scope_word swaps (lpc_return_eval eta [(states!i)!j])) v"
   using lpp_stable_functor_link_sound[OF compatible transfer link equations refl known free observed functors] by blast
  have child_invariant: "J [entry]"
   by (rule deletion[OF _ invariant]) (use member in auto)
  have child: "lp_answer_contract ?T [entry] (lp_ild Q) v ?ret"
   using lower strict rep child_invariant by (auto simp: lpp_stable_functor_module_rep_def entry)
  show "lp_answer_contract ?T [entry] (lp_ild Q) ?t ?ret"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
 qed
qed

lemma lpp_functor_parallel_missing_alternative_rejected:
 "length links\<noteq>length ss \<Longrightarrow>
  \<not> lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFParallel links factss)"
 by (simp add: lpp_check_functor_source_action_def)

lemma lpp_functor_parallel_missing_context_rejected:
 "length factss\<noteq>length ss \<Longrightarrow>
  \<not> lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFParallel links factss)"
 by (simp add: lpp_check_functor_source_action_def)

lemma lpp_functor_trim_nonbarrier_rejected:
 "\<not>lp_cut_barriers (map fst barriers) \<Longrightarrow>
  \<not> lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFTrim successor barriers e fs)"
 by (simp add: lpp_check_functor_source_action_def)

ML \<open>
val checked = @{thms lpp_functor_trim_node_contract lpp_functor_parallel_node_contract
 lpp_functor_parallel_missing_alternative_rejected lpp_functor_parallel_missing_context_rejected
 lpp_functor_trim_nonbarrier_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor control reduction dependency" else ();
\<close>
end
