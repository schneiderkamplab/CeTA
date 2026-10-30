theory LP_Prolog_Context_Table
  imports LP_Prolog_Context_Link LP_Prolog_Integer_Legacy
begin

type_synonym 'v lpp_source_context =
  "'v lpp_success_atom list * 'v lpp_success_guard list * 'v lpp_numeric_observation list"

fun lpp_source_context_holds where
  "lpp_source_context_holds P (facts,guards,observations) eta =
    lpp_path_context_holds P facts guards observations eta"

fun lpp_source_context_transport where
  "lpp_source_context_transport (facts,guards,observations) (child_facts,child_guards,child_observations) bindings =
    lpp_check_context_transport facts guards observations child_facts child_guards child_observations bindings"

definition lpp_context_return_rep where
  "lpp_context_return_rep P nds states contexts ss t = (\<exists>i eta.
    i<length nds \<and> i<length states \<and> i<length contexts \<and>
    ss=lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpp_source_context_holds P (contexts!i) eta \<and>
    t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

definition lpp_check_context_table_link where
  "lpp_check_context_table_link fuel Q nds states contexts nd ss G guards eqs source_context link =
    (lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link \<and>
     lpcl_target link<length contexts \<and>
     lpp_source_context_transport source_context (contexts!lpcl_target link) (lpcl_bindings link))"

lemma lpp_context_table_link_sound:
  assumes checked: "lpp_check_context_table_link fuel Q nds states contexts nd ss G guards eqs source_context link"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) guards eta'"
    and source: "lpp_source_context_holds P source_context eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep P nds states contexts (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j = "lpcl_target link"
  obtain facts tests observations where source_context: "source_context=(facts,tests,observations)"
    by (cases source_context) auto
  obtain child_facts child_tests child_observations where target_context:
    "contexts!?j=(child_facts,child_tests,child_observations)" by (cases "contexts!?j") auto
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link"
    and bound: "?j<length contexts"
    and transport: "lpp_check_context_transport facts tests observations child_facts child_tests child_observations (lpcl_bindings link)"
    using checked by (auto simp: lpp_check_context_table_link_def source_context target_context)
  have source': "lpp_path_context_holds P facts tests observations eta'" using source source_context by simp
  obtain nu where same: "lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    and known': "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child: "lpp_path_context_holds P child_facts child_tests child_observations nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_return_context_link_sound[OF base equations old known transport source'] by blast
  have nb: "?j<length nds" and sb: "?j<length states"
    using base by (auto simp: lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  have represented: "lpp_context_return_rep P nds states contexts
    (lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss))
    [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_context_return_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu])
      (use nb sb bound same known' child in \<open>simp add: target_context\<close>)
  show ?thesis using represented edge by blast
qed

ML \<open>
val checked = [@{thm lpp_context_table_link_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted context table dependency" else ();
\<close>
end
