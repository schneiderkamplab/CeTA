theory LP_Prolog_Stable_Guarded_Region_Descent
 imports LP_Prolog_Stable_Guarded_Descent LP_Prolog_Stable_Guarded_Region LP_Prolog_Finite_Guarded_Region_Descent
begin
hide_const (open) NthRoot.root Term.root Tree_Automata_Containment.entry

theorem lpp_stable_guarded_region_descent_general:
  assumes checked: "lpp_check_guarded_region_descent D roots root region connections boundaries"
    and index: "i<length (lpcsc_nodes (lppftr_control region))"
    and boundary: "boundaries i"
    and observed: "lpp_stable_context_holds operation SP (lppftr_contexts region!i) rho"
    and invariant: "lpc_triple_instance_invariant (lp_atom_eval (lpctr_input root) eta)
      (lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root))
      (lpc_return_eval rho (lpcsc_states (lppftr_control region)!i))"
  shows "(lp_atom_eval (lpctr_input root) eta,
      lp_atom_eval (lpctr_input (roots!lpctc_target (lppftr_connections region!i)))
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings (lppftr_connections region!i)) x) rho))
    \<in>inv_image (lpp_stable_observed_calls operation (set D) SP) lpp_unlift_atom"
proof -
  let ?receipt = "connections!i"
  let ?inp = "lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root)"
  let ?a = "lpp_success_atom_eval (lpp_unlift_atom (lpctr_input root)) eta"
  obtain facts guards observations where context_eq: "lppftr_contexts region!i=(facts,guards,observations)"
    by (cases "lppftr_contexts region!i") auto
  have user: "lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root"
    using checked by (simp add: lpp_check_guarded_region_descent_def)
  have selected: "lpctc_target ?receipt=lpctc_target (lppftr_connections region!i) \<and>
      lpctc_bindings ?receipt=lpctc_bindings (lppftr_connections region!i) \<and>
      (case lppftr_contexts region!i of (fs,gs,os) \<Rightarrow>
        lpp_check_context_connection D fs gs os roots (lpcsc_nodes (lppftr_control region)!i)
          (lpcsc_states (lppftr_control region)!i) ?inp ?receipt)"
    using checked index boundary by (auto simp: lpp_check_guarded_region_descent_def
      list_all_iff Let_def)
  have target: "lpctc_target ?receipt=lpctc_target (lppftr_connections region!i)"
    and bindings: "lpctc_bindings ?receipt=lpctc_bindings (lppftr_connections region!i)"
    and connection: "lpp_check_context_connection D facts guards observations roots
      (lpcsc_nodes (lppftr_control region)!i) (lpcsc_states (lppftr_control region)!i) ?inp ?receipt"
    using selected by (simp_all add: context_eq)
  have lift: "lpp_lift_iatom ?a=lp_atom_eval (lpctr_input root) eta"
    using arg_cong[OF user, of "\<lambda>t. lp_atom_eval t eta"] by (simp only: lpp_lift_atom_eval)
  have inv: "lpc_triple_instance_invariant (lpp_lift_iatom ?a) ?inp
      (lpc_return_eval rho (lpcsc_states (lppftr_control region)!i))"
    using invariant by (simp only: lift)
  have edge: "(?a,lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!lpctc_target ?receipt)))
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings ?receipt) x) rho))
      \<in>lpp_stable_observed_calls operation (set D) SP"
    by (rule lpp_stable_context_connection_descent[OF connection inv])
      (use observed in \<open>simp only: context_eq\<close>)
  show ?thesis using edge by (simp add: inv_image_def lpp_unlift_atom_eval target bindings)
qed

theorem lpp_stable_guarded_region_descent_checked:
  assumes checked: "lpp_check_finite_guarded_region_descent D roots root region connections"
    and index: "i<length (lpcsc_nodes (lppftr_control region))"
    and boundary: "lppftr_actions region!i=None"
    and observed: "lpp_stable_context_holds operation SP (lppftr_contexts region!i) rho"
    and invariant: "lpc_triple_instance_invariant (lp_atom_eval (lpctr_input root) eta)
      (lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root))
      (lpc_return_eval rho (lpcsc_states (lppftr_control region)!i))"
  shows "(lp_atom_eval (lpctr_input root) eta,
      lp_atom_eval (lpctr_input (roots!lpctc_target (lppftr_connections region!i)))
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings (lppftr_connections region!i)) x) rho))
    \<in>inv_image (lpp_stable_observed_calls operation (set D) SP) lpp_unlift_atom"
  by (rule lpp_stable_guarded_region_descent_general[where boundaries="\<lambda>j. lppftr_actions region!j=None" and connections=connections, OF _ index boundary observed invariant])
    (use checked in \<open>simp only: lpp_check_finite_guarded_region_descent_def lpp_check_guarded_region_descent_def\<close>)

theorem lpp_stable_guarded_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_finite_triple_check_region fuel P D Q T roots root_contexts incoming_context root region"
    and descent: "lpp_check_finite_guarded_region_descent OD roots root region connections"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP root_contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  have control: "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region (lppftr_contexts region)"
    using checked by (simp add: lpp_finite_triple_check_region_contexts_def
      lpp_finite_triple_check_region_def lpp_check_evaluation_control_contexts_identity)
  show ?thesis
    by (rule lpp_stable_guarded_region_contexts_checked_lower[where R="inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom", OF compatible control _ program transfer observed known free _ lower])
      (assumption | use lpp_stable_guarded_region_descent_checked[OF descent] in blast)+
qed

ML \<open>
val checked = [@{thm lpp_stable_guarded_region_descent_checked}, @{thm lpp_stable_guarded_region_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable descent dependency" else ();
\<close>
end
