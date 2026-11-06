theory LP_Prolog_Stable_Representation
 imports LP_Prolog_Stable_Arithmetic_Steps
begin

text \<open>The established node, state, context and free-variable tables are
unchanged. This representation strengthens their context interpretation; it
does not construct a separate graph or remove any incoming facts.\<close>

definition lpp_stable_rep where
  "lpp_stable_rep operation SP nds states contexts Fs ss t = (\<exists>i eta.
    i<length nds \<and> i<length states \<and> i<length contexts \<and> i<length Fs \<and>
    ss=lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    lpp_stable_context_holds operation SP (contexts!i) eta \<and>
    t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

lemma lpp_stable_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j="lpcl_target e"
  obtain nu where same: "lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!?j))"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child_free: "lpc_free_knowledge (set (Fs!?j)) nu"
    and context_holds: "lpp_stable_context_holds operation SP (contexts!?j) nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_stable_link_witness[OF compatible program checked equations old known free observed] by blast
  have bounds: "?j<length nds" "?j<length states" "?j<length contexts" "?j<length Fs"
    using checked by (auto simp: lpp_check_evaluation_link_def lpc_check_return_table_link_def
      lpc_check_return_link_def lpc_check_link_def)
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have rep: "lpp_stable_rep operation SP nds states contexts Fs
      (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
      [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_stable_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use bounds inverse knowledge child_free context_holds in auto)
  show ?thesis using edge rep by blast
qed


ML \<open>
val checked = [@{thm lpp_stable_link_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable representation dependency" else ();
\<close>
end
