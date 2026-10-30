theory LP_Prolog_Context_Link
  imports LP_Prolog_Observed_Calls LP_Cut_Return_Table
begin

definition lpp_path_context_holds where
  "lpp_path_context_holds P facts guards observations eta =
    (list_all (\<lambda>b. lpp_guarded_success P lpp_integer_result (lpp_success_atom_eval b eta)) facts \<and>
     list_all (lpp_success_guard_holds lpp_integer_result eta) guards \<and>
     list_all (lpp_numeric_observation_holds eta) observations)"

definition lpp_check_context_transport where
  "lpp_check_context_transport facts guards observations child_facts child_guards child_observations bindings =
    (let mu=lp_cut_instance_subst bindings in
      list_all (\<lambda>b. lpp_success_atom_subst b mu\<in>set facts) child_facts \<and>
      list_all (\<lambda>g. lpp_success_guard_subst g mu\<in>set guards) child_guards \<and>
      list_all (\<lambda>observation. lpp_numeric_observation_substitute observation mu\<in>set observations) child_observations)"

lemma lpp_context_transport_sound:
  assumes checked: "lpp_check_context_transport facts guards observations child_facts child_guards child_observations bindings"
    and source: "lpp_path_context_holds P facts guards observations eta"
  shows "lpp_path_context_holds P child_facts child_guards child_observations
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
  using checked source by (auto simp: lpp_check_context_transport_def lpp_path_context_holds_def
    Let_def list_all_iff lpp_success_atom_subst_eval[symmetric]
    lpp_success_guard_subst_eval[symmetric] lpp_numeric_observation_substitute_eval[symmetric])

text \<open>The target context uses exactly the substitution already checked
by the shared return link. It cannot be attached to a different environment,
or supply later observations to an earlier source operation.\<close>

lemma lpp_return_context_link_sound:
  assumes checked: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) guards eta'"
    and transport: "lpp_check_context_transport facts tests observations
      child_facts child_tests child_observations (lpcl_bindings link)"
    and source: "lpp_path_context_holds P facts tests observations eta'"
  shows "\<exists>nu. lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss) =
      lpc_return_eval nu (states!lpcl_target link) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
    lpp_path_context_holds P child_facts child_tests child_observations nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
proof -
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings link) x) eta'"
  have base: "lpc_check_return_link fuel Q nds nd ss G guards eqs (states!lpcl_target link) link"
    using checked by (simp add: lpc_check_return_table_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps link)
      (lpc_return_eval ?nu (states!lpcl_target link))"
    and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target link),map ?nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
    using lpc_return_link_sound[OF base equations old known] by blast+
  have child: "lpp_path_context_holds P child_facts child_tests child_observations ?nu"
    by (rule lpp_context_transport_sound[OF transport source])
  show ?thesis by (rule exI[of _ ?nu])
    (use same child_known edge child in \<open>simp add: lpc_return_scope_word_inverse\<close>)
qed

ML \<open>
val checked = [@{thm lpp_context_transport_sound}, @{thm lpp_return_context_link_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted observed-context link dependency" else ();
\<close>
end
