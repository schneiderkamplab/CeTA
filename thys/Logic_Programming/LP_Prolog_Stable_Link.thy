theory LP_Prolog_Stable_Link
 imports LP_Prolog_Stable_Transport
begin

lemma lpp_stable_link_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_stable_context_holds operation SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G K eqs e"
    and free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!?j) (lpcl_bindings e)"
    and free_bound: "?j<length Fs"
    using checked by (auto simp: lpp_check_evaluation_link_def)
  have link: "lpc_check_return_link fuel Q nds nd ss G K eqs (states!?j) e"
    and state_bound: "?j<length states"
    using base by (auto simp: lpc_check_return_table_link_def)
  have node_bound: "?j<length nds"
    using link by (auto simp: lpc_check_return_link_def lpc_check_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval ?nu (states!?j))"
    and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpc_return_link_sound[OF link equations old known] by blast+
  have child_free: "lpc_free_knowledge (set (Fs!?j)) ?nu"
    by (rule lpc_checked_link_free_normalized_sound[OF free_check equations free])
  let ?norm = "lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))"
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcl_vars e)) =
      Some (Some (map LPCAtom (lpcl_terms e)))"
    using base by (auto simp: lpc_check_return_table_link_def lpc_check_return_link_def
      lpc_check_link_def lp_cut_check_interface_def)
  have unchanged: "lp_ieval (?norm x) eta'=eta' x" for x
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have normalized: "lpp_stable_context_holds operation SP (lpp_source_context_subst source_context ?norm) eta'"
    using observed by (simp add: lpp_stable_context_substitute unchanged)
  have transport: "lpp_evaluation_context_transport T fs (lpp_source_context_subst source_context ?norm)
      (contexts!?j) (lpcl_bindings e)"
    and context_bound: "?j<length contexts"
    using checked by (auto simp: lpp_check_evaluation_link_def)
  have child_context: "lpp_stable_context_holds operation SP (contexts!?j) ?nu"
    by (rule lpp_stable_existing_transport_sound[OF compatible program transport normalized])
  show ?thesis using same child_known child_free child_context edge by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_link_witness}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable link dependency" else ();
\<close>
end
