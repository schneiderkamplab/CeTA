theory LP_Prolog_NO_Renamed_Ordinary
 imports LP_Cut_NO_Renamed_Trace LP_Prolog_NO_Return_Trace
begin

lemma lpc_no_rename_rows_active:
 "lpc_prefix_active (lpc_no_rename_rows p extra ss) = lpc_prefix_active ss"
 by (cases ss rule: lpc_prefix_active.cases) (simp_all add: lpc_no_rename_rows_def)

lemma lpp_no_clear_rename:
 "lpp_no_clear P (lp_cut_state_map (\<lambda>t. t\<cdot>(Var \<circ> p)) ss) = lpp_no_clear P ss"
 by (induct P ss rule: lpp_no_clear.induct)
   (simp_all add: lp_cut_state_map_def)

lemma lpp_no_rename_rows_clear:
 "lpp_no_clear P (map fst (lpc_no_rename_rows p extra ss)) = lpp_no_clear P (map fst ss)"
 by (simp add: lpc_no_rename_rows_erases lpp_no_clear_rename)

lemma lpp_no_return_ordinary_renamed_sound:
 assumes checked: "lpp_no_return_ordinary_step fuel P reserved ss action tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "lpc_no_return_rename_safe P p extra action"
   and scopes: "lpc_no_action_scope_safe rest action"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>lpp_builtin_source P U"
proof -
 have active: "lpc_prefix_active ss" and clear: "lpp_no_clear P (map fst ss)"
   and step: "lpc_no_return_step fuel P reserved ss action tt"
   using checked by (auto simp: lpp_no_return_ordinary_step_def)
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_renamed_sound[OF step inverse safe scopes]]
   by (simp add: lpc_attach_answers_erases)
 have renamed_active: "lpc_prefix_active (lpc_no_rename_rows p extra ss)"
   using active by (simp add: lpc_no_rename_rows_active)
 have renamed_clear: "lpp_no_clear P (map fst (lpc_no_rename_rows p extra ss))"
   using clear by (simp add: lpp_no_rename_rows_clear)
 show ?thesis using actual lpp_no_return_clear_attach[OF renamed_active renamed_clear, of rest]
   by (simp add: lp_prolog_source_def)
qed

ML \<open>
val checked = [@{thm lpc_no_rename_rows_active}, @{thm lpp_no_rename_rows_clear},
 @{thm lpp_no_return_ordinary_renamed_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed Prolog source dispatch" else ();
\<close>
end
