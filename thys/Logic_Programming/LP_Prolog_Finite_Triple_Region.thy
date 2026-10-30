theory LP_Prolog_Finite_Triple_Region
 imports LP_Prolog_Finite_Triple_Observed LP_Prolog_Finite_Triple_Connection LP_Cut_SEG_Triple_Region
begin

hide_const (open) NthRoot.root Term.root

record lpp_finite_triple_region =
  lppftr_contexts :: "string lpp_source_context list"
  lppftr_typings :: "string lpp_transfer_fact list list"
  lppftr_actions :: "lpp_evaluation_action option list"
  lppftr_control :: "string lpc_seg_control_data"
  lppftr_free :: "string list list"
  lppftr_connections :: "string lpc_triple_connection list"
  lppftr_emits :: "(nat * (string * string lpc_term) list) list"

definition lpp_finite_triple_check_region where
  "lpp_finite_triple_check_region fuel P D Q T roots root_contexts incoming_context root region =
    (let data=lppftr_control region; nds=lpcsc_nodes data; nd=lpctr_node root;
         states=lpcsc_states data; Fs=lppftr_free region; contexts=lppftr_contexts region;
         inp=lpc_triple_position_atom (lpcn_vars nd) (lpctr_input root) in
      nds\<noteq>[] \<and> nds!0=nd \<and> states!0=lpc_triple_root_state root \<and>
      Fs!0=lpctr_free root \<and> contexts!0=incoming_context \<and> distinct (lpcn_vars nd) \<and>
      set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars nd) \<and>
      length (lppftr_typings region)=length nds \<and>
      length (lppftr_connections region)=length nds \<and>
      length (lppftr_emits region)=length nds \<and>
      lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
      lpp_check_evaluation_control fuel P (lpcsc_program data) nds states contexts Fs T
        (lpcsc_returned data) (lpcsc_arity data) (lppftr_actions region) \<and>
      list_all (\<lambda>i.
        (lppftr_actions region!i=None \<longrightarrow>
          lpp_finite_triple_check_connection T (lppftr_typings region!i) fuel D Q roots root_contexts (contexts!i) (nds!i) (Fs!i) (states!i) inp
            (lpctr_output root) (lppftr_connections region!i)) \<and>
        lpc_triple_check_emit Q (lpctr_output root) (states!i)
          (fst (lppftr_emits region!i)) (snd (lppftr_emits region!i))) [0..<length nds])"

definition lpp_finite_triple_check_region_contexts where
  "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region local_contexts =
    (let data=lppftr_control region; nds=lpcsc_nodes data; nd=lpctr_node root;
         states=lpcsc_states data; Fs=lppftr_free region; contexts=lppftr_contexts region;
         inp=lpc_triple_position_atom (lpcn_vars nd) (lpctr_input root) in
      nds\<noteq>[] \<and> nds!0=nd \<and> states!0=lpc_triple_root_state root \<and>
      Fs!0=lpctr_free root \<and> contexts!0=incoming_context \<and> distinct (lpcn_vars nd) \<and>
      set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars nd) \<and>
      length (lppftr_typings region)=length nds \<and>
      length (lppftr_connections region)=length nds \<and>
      length (lppftr_emits region)=length nds \<and>
      lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
      lpp_check_evaluation_control_contexts fuel P (lpcsc_program data) nds states contexts local_contexts Fs T
        (lpcsc_returned data) (lpcsc_arity data) (lppftr_actions region) \<and>
      list_all (\<lambda>i.
        (lppftr_actions region!i=None \<longrightarrow>
          lpp_finite_triple_check_connection T (lppftr_typings region!i) fuel D Q roots root_contexts (contexts!i) (nds!i) (Fs!i) (states!i) inp
            (lpctr_output root) (lppftr_connections region!i)) \<and>
        lpc_triple_check_emit Q (lpctr_output root) (states!i)
          (fst (lppftr_emits region!i)) (snd (lppftr_emits region!i))) [0..<length nds])"

theorem lpp_finite_triple_region_contexts_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region local_contexts"
    and enrich: "\<And>i rho. i<length (lpcsc_nodes (lppftr_control region)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpcsc_nodes (lppftr_control region)!i)))
        (lpcn_guards (lpcsc_nodes (lppftr_control region)!i)) rho \<Longrightarrow>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lppftr_contexts region!i) rho \<Longrightarrow>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP (local_contexts!i) rho"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  let ?data = "lppftr_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Fs = "lppftr_free region"
  let ?contexts = "lppftr_contexts region"
  let ?nd = "lpctr_node root"
  let ?inp = "lpc_triple_position_atom (lpcn_vars ?nd) (lpctr_input root)"
  let ?a = "lp_atom_eval (lpctr_input root) eta"
  let ?ss = "lpc_return_eval eta (lpc_triple_root_state root)"
  have control: "lpp_check_evaluation_control_contexts fuel P (lpcsc_program ?data) ?nds ?states ?contexts local_contexts ?Fs T
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lppftr_actions region)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state root" "?Fs!0=lpctr_free root" "?contexts!0=incoming_context"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars ?nd)"
    using checked by (auto simp: lpp_finite_triple_check_region_contexts_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal intro!: exI[of _ LPIVar])
  have rep: "lpp_evaluation_module_rep SP ?nds ?states ?contexts ?Fs ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding lpp_evaluation_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpp_evaluation_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known free observed in \<open>auto simp: lpp_check_evaluation_control_contexts_def\<close>)
  show ?thesis
  proof (rule lpp_finite_triple_observed_control_contexts[OF control enrich ranked transfer program inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lppftr_actions region!i=None"
      and known': "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and observed': "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (?contexts!i) rho"
      and free': "lpc_free_knowledge (set (?Fs!i)) rho"
      and inv': "lpc_triple_instance_invariant ?a ?inp (lpc_return_eval rho (?states!i))"
    have connection: "lpp_finite_triple_check_connection T (lppftr_typings region!i) fuel D Q roots root_contexts (?contexts!i) (?nds!i) (?Fs!i) (?states!i)
      ?inp (lpctr_output root) (lppftr_connections region!i)"
      using checked index boundary_node by (auto simp: lpp_finite_triple_check_region_contexts_def Let_def list_all_iff)
    show "lpp_finite_triple_answer_contract P (lpc_return_eval rho (?states!i)) Q (lp_atom_eval (lpctr_output root))"
      by (rule lpp_finite_triple_connection_checked_lower[OF transfer connection program known' observed' free' inv' lower])
  next
    fix i assume "i<length ?nds"
    then show "lpc_triple_check_emit Q (lpctr_output root) (?states!i)
        (fst (lppftr_emits region!i)) (snd (lppftr_emits region!i))"
      using checked by (auto simp: lpp_finite_triple_check_region_contexts_def Let_def list_all_iff)
  qed
qed

theorem lpp_finite_triple_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_triple_check_region fuel P D Q T roots root_contexts incoming_context root region"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  have control: "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region (lppftr_contexts region)"
    using checked by (simp add: lpp_finite_triple_check_region_contexts_def
      lpp_finite_triple_check_region_def lpp_check_evaluation_control_contexts_identity)
  show ?thesis
    by (rule lpp_finite_triple_region_contexts_checked_lower[OF control _ program transfer observed known free lower]) assumption
qed

end
