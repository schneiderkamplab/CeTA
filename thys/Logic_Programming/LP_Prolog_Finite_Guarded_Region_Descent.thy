theory LP_Prolog_Finite_Guarded_Region_Descent
 imports LP_Prolog_Finite_Guarded_Region LP_Prolog_Finite_Guarded_Descent
begin

hide_const (open) NthRoot.root Term.root

lemma lpp_unlift_atom_eval:
  "lpp_unlift_atom (lp_atom_eval t eta) = lpp_success_atom_eval (lpp_unlift_atom t) eta"
proof -
  obtain f ts where t: "t=(f,ts)" by (cases t) auto
  show ?thesis by (cases f) (simp_all add: t lp_atom_eval_def lpp_success_atom_eval_def)
qed

definition lpp_check_guarded_region_descent where
  "lpp_check_guarded_region_descent D roots root region connections boundary =
    (lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root \<and>
     length connections=length (lpcsc_nodes (lppftr_control region)) \<and>
     list_all (\<lambda>i. boundary i \<longrightarrow>
       (let receipt=connections!i; original=lppftr_connections region!i;
            inp=lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root)
        in lpctc_target receipt=lpctc_target original \<and>
           lpctc_bindings receipt=lpctc_bindings original \<and>
           (case lppftr_contexts region!i of (facts,guards,observations) \<Rightarrow>
             lpp_check_context_connection D facts guards observations roots
               (lpcsc_nodes (lppftr_control region)!i)
               (lpcsc_states (lppftr_control region)!i) inp receipt)))
       [0..<length (lpcsc_nodes (lppftr_control region))])"

definition lpp_check_finite_guarded_region_descent where
  "lpp_check_finite_guarded_region_descent D roots root region connections =
    (lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root \<and>
     length connections=length (lpcsc_nodes (lppftr_control region)) \<and>
     list_all (\<lambda>i. lppftr_actions region!i=None \<longrightarrow>
       (let receipt=connections!i; original=lppftr_connections region!i;
            inp=lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root)
        in lpctc_target receipt=lpctc_target original \<and>
           lpctc_bindings receipt=lpctc_bindings original \<and>
           (case lppftr_contexts region!i of (facts,guards,observations) \<Rightarrow>
             lpp_check_context_connection D facts guards observations roots
               (lpcsc_nodes (lppftr_control region)!i)
               (lpcsc_states (lppftr_control region)!i) inp receipt)))
       [0..<length (lpcsc_nodes (lppftr_control region))])"

theorem lpp_finite_guarded_region_descent_checked:
  assumes checked: "lpp_check_finite_guarded_region_descent D roots root region connections"
    and index: "i<length (lpcsc_nodes (lppftr_control region))"
    and boundary: "lppftr_actions region!i=None"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lppftr_contexts region!i) rho"
    and invariant: "lpc_triple_instance_invariant (lp_atom_eval (lpctr_input root) eta)
      (lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root))
      (lpc_return_eval rho (lpcsc_states (lppftr_control region)!i))"
  shows "(lp_atom_eval (lpctr_input root) eta,
      lp_atom_eval (lpctr_input (roots!lpctc_target (lppftr_connections region!i)))
        (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings (lppftr_connections region!i)) x) rho))
    \<in>inv_image (lpp_finite_observed_calls (set D) SP) lpp_unlift_atom"
proof -
  let ?receipt = "connections!i"
  let ?inp = "lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root)"
  let ?a = "lpp_success_atom_eval (lpp_unlift_atom (lpctr_input root)) eta"
  obtain facts guards observations where context_eq: "lppftr_contexts region!i=(facts,guards,observations)"
    by (cases "lppftr_contexts region!i") auto
  have user: "lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root"
    using checked by (simp add: lpp_check_finite_guarded_region_descent_def)
  have selected: "lpctc_target ?receipt=lpctc_target (lppftr_connections region!i) \<and>
      lpctc_bindings ?receipt=lpctc_bindings (lppftr_connections region!i) \<and>
      (case lppftr_contexts region!i of (fs,gs,os) \<Rightarrow>
        lpp_check_context_connection D fs gs os roots (lpcsc_nodes (lppftr_control region)!i)
          (lpcsc_states (lppftr_control region)!i) ?inp ?receipt)"
    using checked index boundary by (auto simp: lpp_check_finite_guarded_region_descent_def
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
      \<in>lpp_finite_observed_calls (set D) SP"
    by (rule lpp_finite_context_connection_descent[OF connection inv])
      (use observed in \<open>simp only: context_eq\<close>)
  show ?thesis using edge by (simp add: inv_image_def lpp_unlift_atom_eval target bindings)
qed

theorem lpp_finite_guarded_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_triple_check_region fuel P D Q T roots root_contexts incoming_context root region"
    and descent: "lpp_check_finite_guarded_region_descent OD roots root region connections"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>inv_image (lpp_finite_observed_calls (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_finite_triple_root_rep SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  have control: "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region (lppftr_contexts region)"
    using checked by (simp add: lpp_finite_triple_check_region_contexts_def
      lpp_finite_triple_check_region_def lpp_check_evaluation_control_contexts_identity)
  show ?thesis
    by (rule lpp_finite_guarded_region_contexts_checked_lower[where R="inv_image (lpp_finite_observed_calls (set OD) SP) lpp_unlift_atom", OF control _ program transfer observed known free _ lower])
      (assumption | use lpp_finite_guarded_region_descent_checked[OF descent] in blast)+
qed

end
