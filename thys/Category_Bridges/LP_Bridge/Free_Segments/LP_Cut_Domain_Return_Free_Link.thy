theory LP_Cut_Domain_Return_Free_Link
 imports LP_Cut_Domain_Mixed_Free_Coverage
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

definition precise_return_free_rep where
  "precise_return_free_rep nds states Fs ss t = (\<exists>i eta.
    i < length nds \<and> i < length states \<and> i < length Fs \<and>
    ss = lpc_return_eval eta (states!i) \<and>
    knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    t = [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"


lemma precise_return_free_table_link_sound:
  assumes checked: "lpc_check_return_free_table_link fuel Q nds states Fs nd ss G K eqs F e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_free_rep nds states Fs (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G K eqs e"
    and free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!?j) (lpcl_bindings e)"
    and free_bound: "?j<length Fs"
    using checked by (auto simp: lpc_check_return_free_table_link_def)
  have link: "lpc_check_return_link fuel Q nds nd ss G K eqs (states!?j) e"
    and state_bound: "?j<length states"
    using base by (auto simp: lpc_check_return_table_link_def)
  have node_bound: "?j<length nds"
    using link by (auto simp: lpc_check_return_link_def lpc_check_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval ?nu (states!?j))"
    and child_known: "knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using precise_return_link_sound[OF link equations old known] by blast+
  have child_free: "lpc_free_knowledge (set (Fs!?j)) ?nu"
    by (rule lpc_checked_link_free_normalized_sound[OF free_check equations free])
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss) = lpc_return_eval ?nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have represented: "precise_return_free_rep nds states Fs
    (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
    [(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))]"
    unfolding precise_return_free_rep_def
    by (rule exI[of _ ?j], rule exI[of _ ?nu])
      (use node_bound state_bound free_bound inverse child_known child_free in auto)
  show ?thesis using edge represented by blast
qed


end
end
