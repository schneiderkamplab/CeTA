theory LP_Prolog_Univ_Ground_Receipt
 imports LP_Prolog_Univ_Ground_Return LP_Prolog_Functor_Split_Contract LP_Prolog_Finite_Ground_Receipt
begin

lemma lpp_domain_actual_return_reinterface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) (lpc_reinterface F ss) rho"
  obtains eta where "lp_actual_answer (lpp_domain_answers P B U D) ss eta" "rho=F eta"
proof -
  obtain us tail where path: "(lpc_reinterface F ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and event: "lpp_domain_answers P B U D us (Some rho) tail"
    using actual by (auto simp: lp_actual_answer_def)
  obtain vs where reached: "(ss,vs)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and shape: "lpc_reinterface F vs=us"
    using lpp_domain_reinterface_path_reflect[OF commute path] by blast
  have event': "lpp_domain_answers P B U D (lpc_reinterface F vs) (Some rho) tail"
    using event shape by simp
  obtain ev ws where step: "lpp_domain_answers P B U D vs ev ws"
    and mapped: "map_option F ev=Some rho"
    using lpp_domain_reinterface_reflect[OF commute event'] by blast
  obtain eta where ev: "ev=Some eta" and rho: "rho=F eta"
    using mapped by (cases ev) auto
  have source: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    using reached step ev by (auto simp: lp_actual_answer_def)
  show ?thesis using that source rho by blast
qed

lemma lpp_domain_seg_observed_actual:
  assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) (lpc_return_eval eta [(e,map Var vs)]) rho"
  obtains theta where
    "lp_actual_answer (lpp_domain_answers P B U D) [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    "rho=lpc_return_env (map Var vs) theta"
proof -
  have shape: "lpc_return_eval eta [(e,map Var vs)] =
    lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]"
    by (simp add: lpc_return_eval_def lpc_reinterface_def)
  have observed: "lp_actual_answer (lpp_domain_answers P B U D)
    (lpc_reinterface (lpc_return_env (map Var vs))
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)]) rho"
    using actual by (simp only: shape)
  show ?thesis
    using lpp_domain_actual_return_reinterface[where F="lpc_return_env (map Var vs)",
      OF lpc_return_env_commutes observed] that by blast
qed

lemma lpp_univ_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_ground_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) observations"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) theta \<and>
    list_all (lpp_functor_fact_holds names theta) observations"
proof -
  let ?model = "lppsgr_model evidence"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes evidence"
  let ?K = "lppsgr_ground evidence"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  obtain f ts where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using checked by (auto simp: lpp_finite_ground_receipt_check_def Let_def
      elim!: lpp_finite_ground_prefix_check.elims)
  have program: "lpp_inline_return_program_check P ?F ?SP"
    and builtin: "lpp_inline_builtin_check ?F ?SP"
    and modes: "lpp_guarded_ground_check ?SP ?modes"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_finite_ground_receipt_check_def Let_def)
  obtain theta where source: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_domain_seg_observed_actual[OF actual] by blast
  have evaluated: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) SP incoming_context eta"
    using observed by (simp add: lpp_stable_context_holds_def)
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_stable_scalar_evaluation_ground evaluated]
    by (auto simp: lp_cut_knowledge_def)
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_inline_univ_guarded_ground_return[OF program builtin selected ordinary modes gr])
      (use source in \<open>simp add: pre\<close>)
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context ?K) theta"
    using preserved outputs by (cases incoming_context)
      (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
  proof (rule lpp_actual_return_preserves_finite_value[OF _ source])
    show "lp_seg_ground (eta x)" using gr x by simp
    show "list_all (\<lambda>e. snd e x=eta x)
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)]" by simp
  qed
  have retained: "list_all (lpp_functor_fact_holds names theta) observations"
    by (rule lpp_actual_return_preserves_functors[OF source]) (use functors in simp)
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context retained by blast
qed

ML \<open>
val checked = @{thms lpp_domain_actual_return_reinterface lpp_domain_seg_observed_actual lpp_univ_ground_receipt_return};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted univ ground-return receipt" else ();
\<close>
end
