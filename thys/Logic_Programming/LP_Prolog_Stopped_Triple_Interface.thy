theory LP_Prolog_Stopped_Triple_Interface
 imports LP_Prolog_Stopped_Triple_Answers LP_Prolog_Stopped_Return_Interface LP_Prolog_Stopped_Scopes LP_Prolog_Finite_Triple_Interface
begin

theorem lpp_stopped_triple_answer_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpp_stopped_triple_answer_contract operation P (lpc_reinterface F ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (F eta)) \<Longrightarrow>
      lp_answer_model Q (final eta)"
  shows "lpp_stopped_triple_answer_contract operation P ss Q final"
proof (unfold lpp_stopped_triple_answer_contract_characterization, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))) {ss}"
    using contract lpp_stopped_reinterface_SN[where F=F, OF commute]
    by (auto simp: lpp_stopped_triple_answer_contract_characterization)
next
  fix eta assume actual: "lpp_stopped_actual_return operation P ss eta"
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    and event: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) us (Some eta) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have reached: "(lpc_reinterface F ss,lpc_reinterface F us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    by (rule lpp_stopped_reinterface_path_forward[where F=F, OF commute path])
  have emitted: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_reinterface F us) (Some (F eta)) (lpc_reinterface F tail)"
    using lpp_stopped_reinterface_forward[where F=F, OF commute event] by simp
  have child: "lpp_stopped_actual_return operation P (lpc_reinterface F ss) (F eta)"
    using reached emitted by (auto simp: lp_actual_answer_def)
  show "lp_answer_model Q (final eta)"
    by (rule bridge[OF lpp_stopped_triple_answer_contract_return[OF contract child]])
qed

lemma lpp_stopped_actual_return_reinterface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and actual: "lpp_stopped_actual_return operation P (lpc_reinterface F ss) rho"
  obtains eta where "lpp_stopped_actual_return operation P ss eta" "rho=F eta"
proof -
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    and event: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  obtain vs where reached: "(ss,vs)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpp_stopped_reinterface_path_reflect[OF commute path] by blast
  have event': "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpp_stopped_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lpp_stopped_actual_return operation P ss eta"
    using reached step ev by (auto simp: lp_actual_answer_def)
  show ?thesis using that source rho by blast
qed

theorem lpp_stopped_triple_answer_project_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpp_stopped_triple_answer_contract operation P ss Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret eta) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_reinterface F ss) Q final"
proof (unfold lpp_stopped_triple_answer_contract_characterization, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))) {lpc_reinterface F ss}"
    using contract lpp_stopped_reinterface_SN[where F=F, OF commute]
    by (auto simp: lpp_stopped_triple_answer_contract_characterization)
next
  fix rho assume actual: "lpp_stopped_actual_return operation P (lpc_reinterface F ss) rho"
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    and event: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  obtain vs where reached: "(ss,vs)\<in>(lp_answer_steps (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)))\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpp_stopped_reinterface_path_reflect[OF commute path] by blast
  have event': "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpp_stopped_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lpp_stopped_actual_return operation P ss eta"
    using reached step ev by (auto simp: lp_actual_answer_def)
  show "lp_answer_model Q (final rho)"
    unfolding rho by (rule bridge[OF lpp_stopped_triple_answer_contract_return[OF contract source]])
qed

theorem lpp_stopped_triple_answer_boundary:
  assumes child_commute: "\<And>eta sigma. G (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (G eta y) sigma)"
    and parent_commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and child: "lpp_stopped_triple_answer_contract operation P (lpc_reinterface G ss) Q ret"
    and bridge: "\<And>eta. lp_answer_model Q (ret (G eta)) \<Longrightarrow>
      lp_answer_model Q (final (F eta))"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_reinterface F ss) Q final"
proof -
  have full: "lpp_stopped_triple_answer_contract operation P ss Q (\<lambda>eta. final (F eta))"
    by (rule lpp_stopped_triple_answer_lift_interface[OF child_commute child bridge])
  show ?thesis by (rule lpp_stopped_triple_answer_project_interface[OF parent_commute full]) simp
qed

theorem lpp_stopped_triple_checked_instance_contract:
  fixes P :: "(string,string) lp_cut_program"
  assumes inst: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and receipt: "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma"
    and child_contract: "lpp_stopped_triple_answer_contract operation P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) Q (lp_atom_eval child_out)"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta [(e,observed)]) Q (lp_atom_eval parent_out)"
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
  have scoped: "lpp_stopped_triple_answer_contract operation P
    (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])) Q (lp_atom_eval child_out)"
    unfolding lpp_stopped_triple_answer_contract_def
    by (rule lpp_stopped_contract_scopes[OF program])
      (use child_contract in \<open>simp only: lpp_stopped_triple_answer_contract_def\<close>)
  have same: "lpc_return_eval eta [(e,?outputs)] =
    lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child': "lpp_stopped_triple_answer_contract operation P (lpc_reinterface ?cf ?ss) Q (lp_atom_eval child_out)"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "lpp_stopped_triple_answer_contract operation P (lpc_reinterface ?pf ?ss) Q (lp_atom_eval parent_out)"
  proof (rule lpp_stopped_triple_answer_boundary[OF lpc_seg_observe_commutes lpc_seg_observe_commutes child'])
    fix rho assume child_model: "lp_answer_model Q (lp_atom_eval child_out (?cf rho))"
    show "lp_answer_model Q (lp_atom_eval parent_out (?pf rho))"
      by (rule lpc_triple_checked_instance_answer[OF receipt child_model])
  qed
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed


ML \<open>
val checked = [@{thm lpp_stopped_triple_answer_lift_interface}, @{thm lpp_stopped_actual_return_reinterface},
  @{thm lpp_stopped_triple_answer_project_interface}, @{thm lpp_stopped_triple_answer_boundary},
  @{thm lpp_stopped_triple_checked_instance_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped triple interface dependency" else ();
\<close>
end
