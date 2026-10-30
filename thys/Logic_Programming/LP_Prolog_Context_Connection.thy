theory LP_Prolog_Context_Connection
 imports LP_Prolog_Context_Triple_Observed LP_Cut_SEG_Triple_Connection
begin

lemma lpp_domain_source_scope_SN:
  fixes s :: "(string lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes program: "lp_cut_source_program P"
    and sn: "SN_on (lpp_domain_source P B U D) {s}"
  shows "SN_on (lpp_domain_source P B U D) {lp_cut_scope_word swaps s}"
proof -
  let ?ss = "map (\<lambda>e. (e,\<lambda>_::nat. (LPIFun LPCTruth [] :: (string lp_cut_symbol,string) lp_iterm))) s"
  have erased: "map fst ?ss=s" by (simp add: map_map o_def)
  have instrumented: "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {?ss}"
    by (rule lpp_domain_source_answer_SN) (use sn in \<open>simp add: map_map o_def\<close>)
  have contract: "lp_answer_contract (lpp_domain_answers P B U D) ?ss ({}::unit rel) () (\<lambda>_. ())"
    using instrumented by (simp add: lp_answer_contract_def lp_answers_covered_def)
  have scoped: "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_scope_word swaps ?ss) ({}::unit rel) () (\<lambda>_. ())"
    by (rule lpp_domain_contract_scopes[OF program contract])
  have "SN_on (lpp_domain_source P B U D) {map fst (lpc_return_scope_word swaps ?ss)}"
    by (rule lpp_domain_instrumentation_SN) (use scoped in \<open>simp add: lp_answer_contract_def\<close>)
  then show ?thesis by (simp add: lpc_return_scope_word_erases map_map o_def)
qed

lemma lpp_checked_instance_domain_SN:
  fixes P :: "(string,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and sn: "SN_on (lpp_domain_source P B U D)
      {lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)}"
  shows "SN_on (lpp_domain_source P B U D) {lp_cut_state_eval s eta}"
proof -
  have source: "s=lp_cut_scope_word swaps
      (lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst bindings) t)"
    using checked by (auto simp: lp_cut_check_instance_def Let_def)
  have shape: "lp_cut_state_eval s eta = lp_cut_scope_word swaps
      (lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta))"
    by (simp add: source lp_cut_scope_word_map[symmetric] lp_cut_state_eval_subst)
  show ?thesis using lpp_domain_source_scope_SN[OF program sn, of swaps] shape by simp
qed

fun lpp_unlift_atom where
  "lpp_unlift_atom (LPCUser p,ts) = (p,ts)"
| "lpp_unlift_atom (_,ts) = ('''',ts)"

definition lpp_check_context_connection where
  "lpp_check_context_connection D facts guards observations roots nd ss inp receipt =
    (lpctc_target receipt<length roots \<and>
      (let root=roots!lpctc_target receipt; child=lpctr_node root;
           mu=lp_cut_instance_subst (lpctc_bindings receipt) in
       case (ss,lpcn_state child) of ([(e,observed)],[ce]) \<Rightarrow>
         lpc_seg_check_instance_boundary e (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd) observed
           ce (lpcn_ground child) (lpcn_guards child) (lpcn_vars child)
           (lpctc_bindings receipt) (lpctc_swaps receipt) \<and>
         lpp_lift_atom (lpp_unlift_atom (lpc_triple_observation_atom observed inp))=
           lpc_triple_observation_atom observed inp \<and>
         lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root \<and>
         lpp_check_observed_call D facts guards observations
           (lpp_unlift_atom (lpc_triple_observation_atom observed inp))
           (lpp_success_atom_subst (lpp_unlift_atom (lpctr_input root)) mu)
           (lpctc_call receipt) (lpctc_call_bindings receipt)
       | _ \<Rightarrow> False))"

theorem lpp_context_connection_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_connection D facts guards observations roots nd ss inp receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and invariant: "lpc_triple_instance_invariant (lpp_lift_iatom a) inp (lpc_return_eval eta ss)"
    and observed_context: "lpp_source_context_holds SP (facts,guards,observations) eta"
    and lower: "\<And>j rho. j<length roots \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!j)))) (lpcn_guards (lpctr_node (roots!j))) rho \<Longrightarrow>
      (a,lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!j))) rho)\<in>lpp_observed_calls (set D) SP \<Longrightarrow>
      SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        {lp_cut_state_eval (lpcn_state (lpctr_node (roots!j))) rho}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta ss)}"
proof -
  let ?i = "lpctc_target receipt"
  let ?root = "roots!?i"
  let ?child = "lpctr_node ?root"
  let ?mu = "lp_cut_instance_subst (lpctc_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" using checked by (simp add: lpp_check_context_connection_def)
  obtain e observed ce where ss: "ss=[(e,observed)]" and state: "lpcn_state ?child=[ce]"
    using checked by (auto simp: lpp_check_context_connection_def Let_def split: list.splits prod.splits;
      metis list.exhaust prod.exhaust)
  have inst: "lpc_seg_check_instance_boundary e (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd) observed
      ce (lpcn_ground ?child) (lpcn_guards ?child) (lpcn_vars ?child)
      (lpctc_bindings receipt) (lpctc_swaps receipt)"
    and head: "lpp_lift_atom (lpp_unlift_atom (lpc_triple_observation_atom observed inp))=
      lpc_triple_observation_atom observed inp"
    and call: "lpp_check_observed_call D facts guards observations
      (lpp_unlift_atom (lpc_triple_observation_atom observed inp))
      (lpp_success_atom_subst (lpp_unlift_atom (lpctr_input ?root)) ?mu)
      (lpctc_call receipt) (lpctc_call_bindings receipt)"
    using checked by (auto simp: lpp_check_context_connection_def Let_def ss state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst known])
  obtain sigma where matching: "lp_iatom_subst (lpp_lift_iatom a) sigma=
      lp_atom_eval (lpc_triple_observation_atom observed inp) eta"
    using invariant by (auto simp: ss lpc_triple_instance_invariant_def
      lpc_return_eval_def lpc_triple_observation_atom_eval)
  have lifted_match: "lp_iatom_subst (lpp_lift_iatom a) sigma=
      lp_atom_eval (lpp_lift_atom (lpp_unlift_atom (lpc_triple_observation_atom observed inp))) eta"
    using matching arg_cong[OF head, of "\<lambda>b. lp_atom_eval b eta"] by metis
  have matching': "lpp_success_iatom_subst a sigma=
      lpp_success_atom_eval (lpp_unlift_atom (lpc_triple_observation_atom observed inp)) eta"
    using lifted_match
    by (simp add: lpp_lift_atom_def lpp_lift_iatom_def
      lp_iatom_subst_def lp_atom_eval_def lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  have edge: "(a,lpp_success_atom_eval (lpp_success_atom_subst (lpp_unlift_atom (lpctr_input ?root)) ?mu) eta)
      \<in>lpp_observed_calls (set D) SP"
    by (rule lpp_checked_observed_call[OF call matching'])
      (use observed_context in \<open>auto simp: lpp_path_context_holds_def list_all_iff\<close>)
  have edge': "(a,lpp_success_atom_eval (lpp_unlift_atom (lpctr_input ?root)) ?eta)\<in>lpp_observed_calls (set D) SP"
    using edge by (simp only: lpp_success_atom_subst_eval)
  have child_sn: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      {lp_cut_state_eval [ce] ?eta}"
    using lower[OF index child_known edge'] by (simp only: state)
  have instance_check: "lp_cut_check_instance [e] (lpcn_ground nd) (lpcn_guards nd)
      [ce] (lpcn_ground ?child) (lpcn_guards ?child) (lpctc_bindings receipt) (lpctc_swaps receipt)"
    using inst by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  have "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      {lp_cut_state_eval [e] eta}"
    by (rule lpp_checked_instance_domain_SN[OF program instance_check child_sn])
  then show ?thesis by (simp add: ss lpc_return_eval_erases)
qed

ML \<open>
val checked = [@{thm lpp_domain_source_scope_SN}, @{thm lpp_checked_instance_domain_SN}, @{thm lpp_context_connection_checked_lower}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual boundary dependency" else ();
\<close>
end
