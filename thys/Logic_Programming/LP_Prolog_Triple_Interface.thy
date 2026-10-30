theory LP_Prolog_Triple_Interface
 imports LP_Prolog_Triple_Answers LP_Prolog_Context_Triple_Observed LP_Cut_SEG_Triple_Receipt
begin

lemma lpp_domain_reinterface_path_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(ss,tt)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
  shows "(lpc_reinterface F ss,lpc_reinterface F tt)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "lpp_domain_answers P B U D tt event uu"
    using step by (auto simp: lp_answer_steps_def)
  have edge: "(lpc_reinterface F tt,lpc_reinterface F uu)\<in>lp_answer_steps (lpp_domain_answers P B U D)"
    using lpp_domain_reinterface_forward[where F=F, OF commute event] by (auto simp: lp_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed


lemma lpp_domain_reinterface_path_reflect:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(lpc_reinterface F ss,tt)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
  shows "\<exists>us. (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<and> lpc_reinterface F us=tt"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step tt uu)
  obtain us where reached: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and shape: "lpc_reinterface F us=tt" using step by blast
  obtain event where event: "lpp_domain_answers P B U D (lpc_reinterface F us) event uu"
    using step shape by (auto simp: lp_answer_steps_def)
  obtain ev vs where local: "lpp_domain_answers P B U D us ev vs"
    and out: "lpc_reinterface F vs=uu"
    using lpp_domain_reinterface_reflect[OF commute event] by blast
  have edge: "(us,vs)\<in>lp_answer_steps (lpp_domain_answers P B U D)" using local by (auto simp: lp_answer_steps_def)
  have "(ss,vs)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*" by (rule rtrancl_into_rtrancl[OF reached edge])
  then show ?case using out by blast
qed


theorem lpp_triple_answer_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpp_triple_answer_contract P (lpc_reinterface F ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (F eta)) \<Longrightarrow>
      lp_answer_model Q (final eta)"
  shows "lpp_triple_answer_contract P ss Q final"
proof (unfold lpp_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)) {ss}"
    by (rule lpp_domain_source_answer_SN) (use lpp_triple_answer_contract_SN[OF contract] in simp)
next
  fix eta assume actual: "lpp_actual_return P ss eta"
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain us (Some eta) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have reached: "(lpc_reinterface F ss,lpc_reinterface F us)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    by (rule lpp_domain_reinterface_path_forward[where F=F, OF commute path])
  have emitted: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_reinterface F us) (Some (F eta)) (lpc_reinterface F tail)"
    using lpp_domain_reinterface_forward[where F=F, OF commute event] by simp
  have child: "lpp_actual_return P (lpc_reinterface F ss) (F eta)"
    using reached emitted by (auto simp: lp_actual_answer_def)
  show "lp_answer_model Q (final eta)"
    by (rule bridge[OF lpp_triple_answer_contract_return[OF contract child]])
qed

lemma lpp_actual_return_reinterface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and actual: "lpp_actual_return P (lpc_reinterface F ss) rho"
  obtains eta where "lpp_actual_return P ss eta" "rho=F eta"
proof -
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  obtain vs where reached: "(ss,vs)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpp_domain_reinterface_path_reflect[OF commute path] by blast
  have event': "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpp_domain_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lpp_actual_return P ss eta"
    using reached step ev by (auto simp: lp_actual_answer_def)
  show ?thesis using that source rho by blast
qed

theorem lpp_triple_answer_project_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpp_triple_answer_contract P ss Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret eta) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpp_triple_answer_contract P (lpc_reinterface F ss) Q final"
proof (unfold lpp_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)) {lpc_reinterface F ss}"
    by (rule lpp_domain_source_answer_SN) (use lpp_triple_answer_contract_SN[OF contract] in simp)
next
  fix rho assume actual: "lpp_actual_return P (lpc_reinterface F ss) rho"
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  obtain vs where reached: "(ss,vs)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpp_domain_reinterface_path_reflect[OF commute path] by blast
  have event': "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpp_domain_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lpp_actual_return P ss eta"
    using reached step ev by (auto simp: lp_actual_answer_def)
  show "lp_answer_model Q (final rho)"
    unfolding rho by (rule bridge[OF lpp_triple_answer_contract_return[OF contract source]])
qed

theorem lpp_triple_answer_boundary:
  assumes child_commute: "\<And>eta sigma. G (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (G eta y) sigma)"
    and parent_commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and child: "lpp_triple_answer_contract P (lpc_reinterface G ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (G eta)) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpp_triple_answer_contract P (lpc_reinterface F ss) Q final"
proof -
  have full: "lpp_triple_answer_contract P ss Q (\<lambda>eta. final (F eta))"
    by (rule lpp_triple_answer_lift_interface[OF child_commute child bridge])
  show ?thesis by (rule lpp_triple_answer_project_interface[OF parent_commute full]) simp
qed

theorem lpp_triple_checked_instance_contract:
  fixes P :: "(string,string) lp_cut_program"
  assumes inst: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and receipt: "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma"
    and child_contract: "lpp_triple_answer_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) Q (lp_atom_eval child_out)"
  shows "lpp_triple_answer_contract P (lpc_return_eval eta [(e,observed)]) Q (lp_atom_eval parent_out)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  let ?outputs = "map ?mu child_vars"
  let ?cf = "lpc_seg_observe (map (lpc_seg_position_template vs) ?outputs)"
  let ?pf = "lpc_seg_observe (map (lpc_seg_position_template vs) observed)"
  let ?ss = "lpc_return_eval eta [(e,map Var vs)]"
  have distinct: "distinct vs"
    and out_vars: "\<And>x. x\<in>set ?outputs \<Longrightarrow> vars_term x \<subseteq> set vs"
    and obs_vars: "\<And>x. x\<in>set observed \<Longrightarrow> vars_term x \<subseteq> set vs"
    and annotated: "[(e,?outputs)] = lpc_return_scope_word swaps
      (lpc_return_map (\<lambda>t. t\<cdot>?mu) [(child,map Var child_vars)])"
    using inst by (auto simp: lpc_seg_check_instance_boundary_def Let_def list_all_iff)
  have scoped: "lpp_triple_answer_contract P
    (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])) Q (lp_atom_eval child_out)"
    unfolding lpp_triple_answer_contract_return_contract
    by (rule lpp_domain_contract_scopes[OF program])
      (use child_contract in \<open>simp only: lpp_triple_answer_contract_return_contract\<close>)
  have same: "lpc_return_eval eta [(e,?outputs)] =
    lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child': "lpp_triple_answer_contract P (lpc_reinterface ?cf ?ss) Q (lp_atom_eval child_out)"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "lpp_triple_answer_contract P (lpc_reinterface ?pf ?ss) Q (lp_atom_eval parent_out)"
  proof (rule lpp_triple_answer_boundary[OF lpc_seg_observe_commutes lpc_seg_observe_commutes child'])
    fix rho assume child_model: "lp_answer_model Q (lp_atom_eval child_out (?cf rho))"
    show "lp_answer_model Q (lp_atom_eval parent_out (?pf rho))"
      by (rule lpc_triple_checked_instance_answer[OF receipt child_model])
  qed
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed

end
