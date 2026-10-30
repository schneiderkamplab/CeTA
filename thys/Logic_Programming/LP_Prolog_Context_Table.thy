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

fun lpp_source_context_subst where
  "lpp_source_context_subst (facts,guards,observations) mu =
    (map (\<lambda>a. lpp_success_atom_subst a mu) facts,
     map (\<lambda>g. lpp_success_guard_subst g mu) guards,
     map (\<lambda>observation. lpp_numeric_observation_substitute observation mu) observations)"

lemma lpp_context_subst_eval:
  "lpp_source_context_holds P (lpp_source_context_subst source_context mu) eta =
    lpp_source_context_holds P source_context (\<lambda>x. lp_ieval (mu x) eta)"
  by (cases source_context) (auto simp: lpp_path_context_holds_def list_all_iff
    lpp_success_atom_subst_eval lpp_success_guard_subst_eval lpp_numeric_observation_substitute_eval)

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
     lpp_source_context_transport
       (lpp_source_context_subst source_context (lp_cut_instance_subst (zip (lpcl_vars link) (lpcl_terms link))))
       (contexts!lpcl_target link) (lpcl_bindings link))"

lemma lpp_context_table_link_witness:
  assumes checked: "lpp_check_context_table_link fuel Q nds states contexts nd ss G guards eqs source_context link"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) guards eta'"
    and source: "lpp_source_context_holds P source_context eta'"
  shows "\<exists>nu. lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!lpcl_target link) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
    lpp_source_context_holds P (contexts!lpcl_target link) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
proof -
  let ?j = "lpcl_target link"
  let ?mu = "lp_cut_instance_subst (zip (lpcl_vars link) (lpcl_terms link))"
  let ?normalized = "lpp_source_context_subst source_context ?mu"
  obtain facts tests observations where source_context: "?normalized=(facts,tests,observations)"
    by (cases ?normalized) auto
  obtain child_facts child_tests child_observations where target_context:
    "contexts!?j=(child_facts,child_tests,child_observations)" by (cases "contexts!?j") auto
  have base: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link"
    and transport: "lpp_check_context_transport facts tests observations child_facts child_tests child_observations (lpcl_bindings link)"
    using checked by (auto simp: lpp_check_context_table_link_def source_context target_context)
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcl_vars link)) =
    Some (Some (map LPCAtom (lpcl_terms link)))"
    using base by (auto simp: lpc_check_return_table_link_def lpc_check_return_link_def
      lpc_check_link_def lp_cut_check_interface_def)
  have unchanged: "lp_ieval (?mu x) eta'=eta' x" for x
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have normalized: "lpp_source_context_holds P ?normalized eta'"
    using source by (simp add: lpp_context_subst_eval unchanged)
  have source': "lpp_path_context_holds P facts tests observations eta'"
    using normalized by (simp add: source_context)
  show ?thesis using lpp_return_context_link_sound[OF base equations old known transport source']
    by (simp add: target_context)
qed

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
  obtain nu where same: "lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child: "lpp_source_context_holds P (contexts!?j) nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_context_table_link_witness[OF checked equations old known source] by blast
  have nb: "?j<length nds" and sb: "?j<length states" and cb: "?j<length contexts"
    using checked by (auto simp: lpp_check_context_table_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  have represented: "lpp_context_return_rep P nds states contexts
    (lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss))
    [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_context_return_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use nb sb cb same child_known child in auto)
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
