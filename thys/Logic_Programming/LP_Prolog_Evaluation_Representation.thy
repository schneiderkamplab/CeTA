theory LP_Prolog_Evaluation_Representation
  imports LP_Prolog_Evaluation_Refresh
begin

definition lpp_evaluation_rep where
  "lpp_evaluation_rep E SP nds states contexts Fs ss t = (\<exists>i eta.
    i<length nds \<and> i<length states \<and> i<length contexts \<and> i<length Fs \<and>
    ss=lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    lpp_evaluation_context_holds E SP (contexts!i) eta \<and>
    t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

lemma lpp_evaluation_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_evaluation_context_holds E SP source_context eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j="lpcl_target e"
  obtain nu where same: "lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!?j))"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child_free: "lpc_free_knowledge (set (Fs!?j)) nu"
    and context_holds: "lpp_evaluation_context_holds E SP (contexts!?j) nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_evaluation_link_witness[OF contract evaluation program checked equations old known free observed] by blast
  have bounds: "?j<length nds" "?j<length states" "?j<length contexts" "?j<length Fs"
    using checked by (auto simp: lpp_check_evaluation_link_def lpc_check_return_table_link_def
      lpc_check_return_link_def lpc_check_link_def)
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have rep: "lpp_evaluation_rep E SP nds states contexts Fs
      (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
      [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_evaluation_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use bounds inverse knowledge child_free context_holds in auto)
  show ?thesis using edge rep by blast
qed

end
