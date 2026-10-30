theory LP_Prolog_Triple_Region
 imports LP_Prolog_Triple_Free_Observed LP_Prolog_Triple_Connection LP_Cut_SEG_Triple_Region
begin

hide_const (open) NthRoot.root Term.root

record lpp_triple_region =
  lpptr_contexts :: "string lpp_source_context list"
  lpptr_typings :: "string lpp_transfer_fact list list"
  lpptr_actions :: "lpp_context_module_action option list"
  lpptr_control :: "string lpc_seg_control_data"
  lpptr_free :: "string list list"
  lpptr_connections :: "string lpc_triple_connection list"
  lpptr_emits :: "(nat * (string * string lpc_term) list) list"

definition lpp_triple_check_region where
  "lpp_triple_check_region fuel P D Q T roots root_contexts incoming_context root region =
    (let data=lpptr_control region; nds=lpcsc_nodes data; nd=lpctr_node root;
         states=lpcsc_states data; Fs=lpptr_free region; contexts=lpptr_contexts region;
         inp=lpc_triple_position_atom (lpcn_vars nd) (lpctr_input root) in
      nds\<noteq>[] \<and> nds!0=nd \<and> states!0=lpc_triple_root_state root \<and>
      Fs!0=lpctr_free root \<and> contexts!0=incoming_context \<and> distinct (lpcn_vars nd) \<and>
      set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars nd) \<and>
      length (lpptr_connections region)=length nds \<and>
      length (lpptr_emits region)=length nds \<and>
      lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
      lpp_check_context_free_control fuel P (lpcsc_program data) nds states contexts Fs T (lpptr_typings region)
        (lpcsc_returned data) (lpcsc_arity data) (lpptr_actions region) \<and>
      list_all (\<lambda>i.
        (lpptr_actions region!i=None \<longrightarrow>
          lpp_triple_check_connection fuel D Q roots root_contexts (contexts!i) (nds!i) (Fs!i) (states!i) inp
            (lpctr_output root) (lpptr_connections region!i)) \<and>
        lpc_triple_check_emit Q (lpctr_output root) (states!i)
          (fst (lpptr_emits region!i)) (snd (lpptr_emits region!i))) [0..<length nds])"

theorem lpp_triple_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_triple_check_region fuel P D Q T roots root_contexts incoming_context root region"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_triple_root_rep SP root_contexts roots us b ret \<Longrightarrow> lpp_triple_answer_contract P us Q ret"
  shows "lpp_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  let ?data = "lpptr_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Fs = "lpptr_free region"
  let ?contexts = "lpptr_contexts region"
  let ?nd = "lpctr_node root"
  let ?inp = "lpc_triple_position_atom (lpcn_vars ?nd) (lpctr_input root)"
  let ?a = "lp_atom_eval (lpctr_input root) eta"
  let ?ss = "lpc_return_eval eta (lpc_triple_root_state root)"
  have control: "lpp_check_context_free_control fuel P (lpcsc_program ?data) ?nds ?states ?contexts ?Fs T (lpptr_typings region)
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lpptr_actions region)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state root" "?Fs!0=lpctr_free root" "?contexts!0=incoming_context"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars ?nd)"
    using checked by (auto simp: lpp_triple_check_region_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal intro!: exI[of _ LPIVar])
  have rep: "lpp_context_free_module_rep SP ?nds ?states ?contexts ?Fs ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding lpp_context_free_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpp_context_free_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known free observed in \<open>auto simp: lpp_check_context_free_control_def\<close>)
  show ?thesis
  proof (rule lpp_triple_free_observed_control[OF control ranked transfer program inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lpptr_actions region!i=None"
      and known': "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and observed': "lpp_source_context_holds SP (?contexts!i) rho"
      and free': "lpc_free_knowledge (set (?Fs!i)) rho"
      and inv': "lpc_triple_instance_invariant ?a ?inp (lpc_return_eval rho (?states!i))"
    have connection: "lpp_triple_check_connection fuel D Q roots root_contexts (?contexts!i) (?nds!i) (?Fs!i) (?states!i)
      ?inp (lpctr_output root) (lpptr_connections region!i)"
      using checked index boundary_node by (auto simp: lpp_triple_check_region_def Let_def list_all_iff)
    show "lpp_triple_answer_contract P (lpc_return_eval rho (?states!i)) Q (lp_atom_eval (lpctr_output root))"
      by (rule lpp_triple_connection_checked_lower[OF connection program known' observed' free' inv' lower])
  next
    fix i assume "i<length ?nds"
    then show "lpc_triple_check_emit Q (lpctr_output root) (?states!i)
        (fst (lpptr_emits region!i)) (snd (lpptr_emits region!i))"
      using checked by (auto simp: lpp_triple_check_region_def Let_def list_all_iff)
  qed
qed

end
