theory LP_Prolog_Context_Region
 imports LP_Prolog_Context_Connection LP_Cut_SEG_Triple_Region
begin

hide_const (open) NthRoot.root Term.root

record lpp_context_region =
  lppcr_control :: "string lpc_seg_control_data"
  lppcr_contexts :: "string lpp_source_context list"
  lppcr_typings :: "string lpp_transfer_fact list list"
  lppcr_actions :: "lpp_context_module_action option list"
  lppcr_connections :: "string lpc_triple_connection list"

definition lpp_check_context_region where
  "lpp_check_context_region fuel P D T roots root region =
    (let data=lppcr_control region; nds=lpcsc_nodes data; nd=lpctr_node root;
         states=lpcsc_states data; contexts=lppcr_contexts region;
         inp=lpc_triple_position_atom (lpcn_vars nd) (lpctr_input root) in
      nds\<noteq>[] \<and> nds!0=nd \<and> states!0=lpc_triple_root_state root \<and>
      contexts!0=([],[],[]) \<and> distinct (lpcn_vars nd) \<and>
      set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars nd) \<and>
      lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root \<and>
      length (lppcr_connections region)=length nds \<and>
      lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
      lpp_check_context_control fuel P (lpcsc_program data) nds states contexts T (lppcr_typings region)
        (lpcsc_returned data) (lpcsc_arity data) (lppcr_actions region) \<and>
      list_all (\<lambda>i. lppcr_actions region!i=None \<longrightarrow>
        (case contexts!i of (facts,guards,observations) \<Rightarrow>
          lpp_check_context_connection D facts guards observations roots (nds!i) (states!i) inp
            (lppcr_connections region!i))) [0..<length nds])"

theorem lpp_context_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program" and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_check_context_region fuel P D T roots root region"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and lower: "\<And>j rho. j<length roots \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!j)))) (lpcn_guards (lpctr_node (roots!j))) rho \<Longrightarrow>
      (lpp_success_atom_eval (lpp_unlift_atom (lpctr_input root)) eta,
       lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!j))) rho)\<in>lpp_observed_calls (set D) SP \<Longrightarrow>
      SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        {lp_cut_state_eval (lpcn_state (lpctr_node (roots!j))) rho}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {lp_cut_state_eval (lpcn_state (lpctr_node root)) eta}"
proof -
  let ?data = "lppcr_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?contexts = "lppcr_contexts region"
  let ?nd = "lpctr_node root"
  let ?inp = "lpc_triple_position_atom (lpcn_vars ?nd) (lpctr_input root)"
  let ?a = "lpp_success_atom_eval (lpp_unlift_atom (lpctr_input root)) eta"
  let ?ss = "lpc_return_eval eta (lpc_triple_root_state root)"
  have control: "lpp_check_context_control fuel P (lpcsc_program ?data) ?nds ?states ?contexts T (lppcr_typings region)
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lppcr_actions region)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state root" "?contexts!0=([],[],[])"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars ?nd)"
    and lifted: "lpp_lift_atom (lpp_unlift_atom (lpctr_input root))=lpctr_input root"
    using checked by (auto simp: lpp_check_context_region_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=lp_atom_eval (lpctr_input root) eta"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have lifted_eval: "lpp_lift_iatom ?a=lp_atom_eval (lpctr_input root) eta"
    using arg_cong[OF lifted, of "\<lambda>b. lp_atom_eval b eta"] by (simp only: lpp_lift_atom_eval)
  have inv: "lpc_triple_instance_invariant (lpp_lift_iatom ?a) ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal lifted_eval intro!: exI[of _ LPIVar])
  have rep: "lpp_context_module_rep SP ?nds ?states ?contexts ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding lpp_context_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpp_context_return_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known in \<open>auto simp: lpp_check_context_control_def lpp_path_context_holds_def\<close>)
  have source_sn: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {map fst ?ss}"
  proof (rule lpp_context_control_source_SN[OF control ranked transfer program inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lppcr_actions region!i=None"
      and known': "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and observed: "lpp_source_context_holds SP (?contexts!i) rho"
      and inv': "lpc_triple_instance_invariant (lpp_lift_iatom ?a) ?inp (lpc_return_eval rho (?states!i))"
    obtain facts guards observations where ctx: "?contexts!i=(facts,guards,observations)" by (cases "?contexts!i") auto
    have selected: "case ?contexts!i of (fs,gs,os) \<Rightarrow>
      lpp_check_context_connection D fs gs os roots (?nds!i) (?states!i) ?inp (lppcr_connections region!i)"
      using checked index boundary_node by (auto simp: lpp_check_context_region_def Let_def list_all_iff)
    have connection: "lpp_check_context_connection D facts guards observations roots (?nds!i) (?states!i) ?inp (lppcr_connections region!i)"
      using selected by (simp only: ctx prod.case)
    show "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      {map fst (lpc_return_eval rho (?states!i))}"
      by (rule lpp_context_connection_checked_lower[OF connection program known' inv' _ lower])
        (use observed in \<open>simp only: ctx\<close>)
  qed
  show ?thesis using source_sn by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
qed

ML \<open>
val checked = [@{thm lpp_context_region_checked_lower}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual region dependency" else ();
\<close>
end
