theory LP_Prolog_Stopped_Positive_Region
 imports LP_Prolog_Stopped_Region_Descent LP_Prolog_Stable_Positive_Context
begin
hide_const (open) NthRoot.root Term.root

definition lpp_positive_contexts where
  "lpp_positive_contexts contexts derivations =
    map (\<lambda>i. lpp_positive_context (contexts!i) (derivations!i)) [0..<length contexts]"

definition lpp_check_stopped_positive_region where
  "lpp_check_stopped_positive_region fuel P D Q T roots root_contexts incoming_context root OD region actions connections derivations =
    (let contexts=lppftr_contexts region;
         local_contexts=lpp_positive_contexts contexts derivations in
      length contexts=length (lpcsc_nodes (lppftr_control region)) \<and>
      length derivations=length contexts \<and>
      list_all (\<lambda>i. lpp_check_positive_derivation (snd (snd (contexts!i))) (derivations!i)) [0..<length contexts] \<and>
      lpp_stopped_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region actions local_contexts \<and>
      lpp_check_guarded_region_descent OD roots root (region\<lparr>lppftr_contexts:=local_contexts\<rparr>) connections (\<lambda>i. actions!i=None))"

theorem lpp_stopped_positive_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stopped_positive_region fuel P D Q T roots root_contexts incoming_context root OD region actions connections derivations"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP root_contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  let ?contexts = "lppftr_contexts region"
  let ?local = "lpp_positive_contexts ?contexts derivations"
  have local: "lpp_stopped_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region actions ?local"
    and descent: "lpp_check_guarded_region_descent OD roots root (region\<lparr>lppftr_contexts:=?local\<rparr>) connections (\<lambda>i. actions!i=None)"
    and count: "length ?contexts=length (lpcsc_nodes (lppftr_control region))"
    using checked by (auto simp: lpp_check_stopped_positive_region_def Let_def)
  have enrich: "lpp_stable_context_holds operation SP (?local!i) rho"
    if index: "i<length (lpcsc_nodes (lppftr_control region))"
      and observed': "lpp_stable_context_holds operation SP (?contexts!i) rho"
    for i rho
  proof -
    have derivation: "lpp_check_positive_derivation (snd (snd (?contexts!i))) (derivations!i)"
      using checked index count by (auto simp: lpp_check_stopped_positive_region_def Let_def list_all_iff)
    have consequence: "lpp_stable_context_holds operation SP
        (lpp_positive_context (?contexts!i) (derivations!i)) rho"
      by (rule lpp_positive_context_sound[OF compatible derivation observed'])
    show ?thesis using consequence index count by (simp add: lpp_positive_contexts_def)
  qed
  show ?thesis
    by (rule lpp_stopped_enriched_region_checked_lower[OF compatible local _ descent program transfer observed known free lower])
      (use enrich in blast)
qed

ML \<open>
val checked = [@{thm lpp_stopped_positive_region_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped positive region dependency" else ();
\<close>
end
