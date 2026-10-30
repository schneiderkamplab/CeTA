theory LP_Prolog_Context_Free_Link
  imports LP_Cut_Return_Free_Link LP_Prolog_Context_Table
begin

definition lpp_context_free_rep where
  "lpp_context_free_rep SP nds states contexts Fs ss t = (\<exists>i eta.
    i < length nds \<and> i < length states \<and> i < length contexts \<and> i < length Fs \<and>
    ss = lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    lpp_source_context_holds SP (contexts!i) eta \<and>
    t = [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

definition lpp_check_context_free_link where
  "lpp_check_context_free_link fuel Q nds states contexts Fs nd ss G K eqs F source_context e =
    (lpp_check_context_table_link fuel Q nds states contexts nd ss G K eqs source_context e \<and>
     lpcl_target e < length Fs \<and>
     lpc_check_link_free_normalized fuel eqs F (Fs!lpcl_target e) (lpcl_bindings e))"

lemma lpp_context_free_link_sound:
  assumes checked: "lpp_check_context_free_link fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_source_context_holds SP source_context eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G K eqs e"
    and free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!?j) (lpcl_bindings e)"
    and free_bound: "?j<length Fs"
    using checked by (auto simp: lpp_check_context_free_link_def lpp_check_context_table_link_def)
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
  have normalized: "lpp_source_context_holds SP (lpp_source_context_subst source_context ?norm) eta'"
    using observed by (simp add: lpp_context_subst_eval unchanged)
  have transport: "lpp_source_context_transport (lpp_source_context_subst source_context ?norm)
      (contexts!?j) (lpcl_bindings e)"
    and context_bound: "?j<length contexts"
    using checked by (auto simp: lpp_check_context_free_link_def lpp_check_context_table_link_def)
  have child_context: "lpp_source_context_holds SP (contexts!?j) ?nu"
    using lpp_context_transport_sound transport normalized
    by (cases "lpp_source_context_subst source_context ?norm"; cases "contexts!?j") auto
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss) = lpc_return_eval ?nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have represented: "lpp_context_free_rep SP nds states contexts Fs
    (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
    [(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_context_free_rep_def
    by (rule exI[of _ ?j], rule exI[of _ ?nu])
      (use node_bound state_bound context_bound free_bound inverse child_known child_free child_context in auto)
  show ?thesis using edge represented by blast
qed

lemma lpp_context_free_link_witness:
  assumes checked: "lpp_check_context_free_link fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_source_context_holds SP source_context eta'"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_source_context_holds SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G K eqs e"
    and free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!?j) (lpcl_bindings e)"
    and free_bound: "?j<length Fs"
    using checked by (auto simp: lpp_check_context_free_link_def lpp_check_context_table_link_def)
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
  have normalized: "lpp_source_context_holds SP (lpp_source_context_subst source_context ?norm) eta'"
    using observed by (simp add: lpp_context_subst_eval unchanged)
  have transport: "lpp_source_context_transport (lpp_source_context_subst source_context ?norm)
      (contexts!?j) (lpcl_bindings e)"
    and context_bound: "?j<length contexts"
    using checked by (auto simp: lpp_check_context_free_link_def lpp_check_context_table_link_def)
  have child_context: "lpp_source_context_holds SP (contexts!?j) ?nu"
    using lpp_context_transport_sound transport normalized
    by (cases "lpp_source_context_subst source_context ?norm"; cases "contexts!?j") auto
  show ?thesis using same child_known child_free child_context edge by blast
qed

end
