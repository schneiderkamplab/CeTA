theory LP_Prolog_Observer_Family
 imports LP_Prolog_Observer_Referenced_Node
begin

definition lpp_observer_family_rep where
 "lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises runtime subject =
  (\<exists>m\<in>members. lpp_premised_functor_module_rep names operation SP (family_nodes m) (states m)
   (contexts m) (frees m) (functors m) (premises m)
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject)"

lemma lpp_observer_family_member:
 "m\<in>members \<Longrightarrow>
  lpp_premised_functor_module_rep names operation SP (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m)
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject \<Longrightarrow>
  lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises runtime subject"
 by (auto simp: lpp_observer_family_rep_def)

theorem lpp_observer_family_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes finite: "finite members"
 and checked: "\<And>m. m\<in>members \<Longrightarrow>
  lpp_check_functor_control T fuel P Q (family_nodes m) (states m) (contexts m) (frees m) (functors m)
   (return_symbols m) (arities m) (actions m)"
 and local: "\<And>m j. m\<in>members \<Longrightarrow> j<length (family_nodes m) \<Longrightarrow>
  lpp_observer_referenced_node_contract names operation SP P B U D Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m)
   (lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises)
   J rest returned j"
 and represented: "lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises runtime subject"
 and invariant: "J runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof -
 let ?T = "lpp_domain_answers P B U D"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?family = "lpp_observer_family_rep names operation SP members family_nodes states contexts frees functors premises"
 let ?rep = "\<lambda>ss t out. out=returned \<and> SN_on (lp_ild Q) {t} \<and>
   (\<exists>joint. ss=lpc_attach_answers rest (lpc_reinterface ?R joint) \<and> J joint \<and> ?family joint t)"
 have initial: "?rep (lpc_attach_answers rest (lpc_reinterface ?R runtime)) subject returned"
  using represented invariant residual by blast
 show ?thesis
 proof (rule lp_answer_contract_modular[where rep="?rep", OF residual initial])
  fix ss t out
  assume rep: "?rep ss t out"
  and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow> ?rep vs v ret \<Longrightarrow>
    lp_answer_contract ?T vs (lp_ild Q) v ret"
  obtain joint m swaps j eta where exact: "ss=lpc_attach_answers rest (lpc_reinterface ?R joint)"
  and inv: "J joint" and member: "m\<in>members" and bound: "j<length (family_nodes m)"
  and conditions: "premises m j eta"
  and shape: "lpc_return_scope_word swaps (lpc_reinterface ?L joint)=lpc_return_eval eta ((states m)!j)"
  and known: "lp_cut_knowledge (set (lpcn_ground ((family_nodes m)!j))) (lpcn_guards ((family_nodes m)!j)) eta"
  and free: "lpc_free_knowledge (set ((frees m)!j)) eta"
  and observed: "lpp_stable_context_holds operation SP ((contexts m)!j) eta"
  and functor_facts: "list_all (lpp_functor_fact_holds names eta) ((functors m)!j)"
  and subject_eq: "t=[(lpcn_pred ((family_nodes m)!j),map eta (lpcn_vars ((family_nodes m)!j)))]"
   using rep by (auto simp: lpp_observer_family_rep_def lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
  have sn: "SN_on (lp_ild Q) {t}" using rep by simp
  have node: "lpp_observer_referenced_node_contract names operation SP P B U D Q
   (family_nodes m) (states m) (contexts m) (frees m) (functors m) (premises m) ?family J rest returned j"
   by (rule local[OF member bound])
  have descendants: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) u returned"
   if strict: "(t,u)\<in>(lp_ild Q)\<^sup>+" and child_rep: "?family child u" and child_inv: "J child" for child u
  proof -
   have child_sn: "SN_on (lp_ild Q) {u}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
     (use trancl_into_rtrancl[OF strict] in auto)
   show ?thesis by (rule lower[OF strict]) (use child_rep child_inv child_sn in blast)
  qed
  have result: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R joint)) (lp_ild Q) t returned"
   using node conditions known free observed functor_facts shape inv sn descendants
   unfolding lpp_observer_referenced_node_contract_def subject_eq by blast
  show "lp_answer_contract ?T ss (lp_ild Q) t out" using result rep exact by simp
 qed
qed

end
