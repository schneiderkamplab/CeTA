theory LP_Prolog_Finite_Local_Region
 imports LP_Prolog_Finite_Local_Connection LP_Prolog_Stable_Guarded_Region
begin

hide_const (open) NthRoot.root Term.root

definition lpp_check_finite_local_region where
  "lpp_check_finite_local_region A fuel P D Q T roots root_contexts incoming_context root region local_contexts =
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
      lpp_check_finite_direct_control_contexts fuel P (lpcsc_program data) nds states contexts local_contexts Fs T
        (lpcsc_returned data) (lpcsc_arity data) (lppftr_actions region) \<and>
      lpp_check_local_finite_states A P nds states local_contexts \<and>
      list_all (\<lambda>i.
        (lppftr_actions region!i=None \<longrightarrow>
          lpp_finite_triple_check_connection T (lppftr_typings region!i) fuel D Q roots root_contexts (contexts!i) (nds!i) (Fs!i) (states!i) inp
            (lpctr_output root) (lppftr_connections region!i)) \<and>
        lpp_finite_triple_check_emit fuel (nds!i) (lppftr_actions region!i) Q (lpctr_output root) (states!i)
          (fst (lppftr_emits region!i)) (snd (lppftr_emits region!i))) [0..<length nds])"

theorem lpp_finite_local_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_local_region A fuel P D Q T roots root_contexts incoming_context root region local_contexts"
    and enrich: "\<And>i rho. i<length (lpcsc_nodes (lppftr_control region)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpcsc_nodes (lppftr_control region)!i)))
        (lpcn_guards (lpcsc_nodes (lppftr_control region)!i)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (lppftr_contexts region!i) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) rho"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state root))"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    and descent: "\<And>i rho. i<length (lpcsc_nodes (lppftr_control region)) \<Longrightarrow>
      lppftr_actions region!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpcsc_nodes (lppftr_control region)!i)))
        (lpcn_guards (lpcsc_nodes (lppftr_control region)!i)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (lppftr_contexts region!i) rho \<Longrightarrow>
      lpc_triple_instance_invariant (lp_atom_eval (lpctr_input root) eta)
        (lpc_triple_position_atom (lpcn_vars (lpctr_node root)) (lpctr_input root))
        (lpc_return_eval rho (lpcsc_states (lppftr_control region)!i)) \<Longrightarrow>
      (lp_atom_eval (lpctr_input root) eta,
       lp_atom_eval (lpctr_input (roots!lpctc_target (lppftr_connections region!i)))
         (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings (lppftr_connections region!i)) x) rho))\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state root)) Q
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
  have control: "lpp_check_finite_direct_control_contexts fuel P (lpcsc_program ?data) ?nds ?states ?contexts local_contexts ?Fs T
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lppftr_actions region)"
    and local_states: "lpp_check_local_finite_states A P ?nds ?states local_contexts"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state root" "?Fs!0=lpctr_free root" "?contexts!0=incoming_context"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars ?nd)"
    using checked by (auto simp: lpp_check_finite_local_region_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal intro!: exI[of _ LPIVar])
  have rep: "lpp_stable_module_rep operation SP ?nds ?states ?contexts ?Fs ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding lpp_stable_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpp_stable_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known free observed in \<open>auto simp: lpp_check_finite_direct_control_contexts_def\<close>)
  show ?thesis
  proof (rule lpp_finite_local_triple_observed_control[OF compatible control enrich ranked transfer program finite local_states signature inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lppftr_actions region!i=None"
      and known': "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and observed': "lpp_stable_context_holds operation SP (?contexts!i) rho"
      and free': "lpc_free_knowledge (set (?Fs!i)) rho"
      and finite': "lpp_finite_direct_invariant A (lpc_return_eval rho (?states!i))"
      and inv': "lpc_triple_instance_invariant ?a ?inp (lpc_return_eval rho (?states!i))"
    have connection: "lpp_finite_triple_check_connection T (lppftr_typings region!i) fuel D Q roots root_contexts (?contexts!i) (?nds!i) (?Fs!i) (?states!i)
      ?inp (lpctr_output root) (lppftr_connections region!i)"
      using checked index boundary_node by (auto simp: lpp_check_finite_local_region_def Let_def list_all_iff)
    show "lpp_stable_triple_answer_contract operation P (lpc_return_eval rho (?states!i)) Q (lp_atom_eval (lpctr_output root))"
      by (rule lpp_finite_local_connection_checked_lower[OF compatible transfer connection program known' observed' free' inv' finite' descent[OF index boundary_node known' observed' inv'] lower])
  next
    fix i assume "i<length ?nds"
    then show "lpp_finite_triple_check_emit fuel (?nds!i) (lppftr_actions region!i) Q (lpctr_output root) (?states!i)
        (fst (lppftr_emits region!i)) (snd (lppftr_emits region!i))"
      using checked by (auto simp: lpp_check_finite_local_region_def Let_def list_all_iff)
  qed
qed


ML \<open>
val checked = [@{thm lpp_finite_local_region_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable guarded region dependency" else ();
\<close>
end
