theory LP_Cut_NO_Renamed_Trace
 imports LP_Cut_NO_Renamed_Actions
begin

lemma lpc_no_backtrack_rows_renamed:
 assumes index: "c<length P" and clash: "lp_cut_check_clash fuel k a (fst (P!c))"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCClause (LPCAtom a#gs) c m,payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra saved)))"
 using lpc_no_return_backtrack_renamed_ambient[where p=p and rest=rest and gs=gs
   and payload="map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra"
   and saved="lpc_no_rename_rows p extra saved", OF index clash]
 by (simp add: lpc_no_rename_rows_def)

lemma lpc_no_unify_fail_rows_renamed:
 assumes failure: "lp_cut_check_equality fuel a b LPCAlwaysFailure"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals (LPCUnify a b#gs),payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra saved)))"
 using lpc_no_return_unify_fail_renamed_ambient[where p=p and rest=rest and gs=gs and P=P
   and payload="map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra"
   and saved="lpc_no_rename_rows p extra saved", OF failure]
 by (simp add: lpc_no_rename_rows_def)

fun lpc_no_action_scope_safe where
 "lpc_no_action_scope_safe rest (LPCNOCase m) = (m\<notin>lpc_rest_scopes rest)"
| "lpc_no_action_scope_safe rest action = True"

lemma lpc_no_return_step_renamed_sound:
 assumes checked: "lpc_no_return_step fuel P reserved ss action tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "lpc_no_return_rename_safe P p extra action"
   and scopes: "lpc_no_action_scope_safe rest action"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))"
 using checked safe scopes
 by (induct fuel P reserved ss action tt rule: lpc_no_return_step.induct)
   (auto simp: Let_def intro: lpc_no_return_admin_renamed_ambient lpc_no_case_rows_renamed
     lpc_no_resolve_rows_renamed[OF _ inverse] lpc_no_swap_rows_renamed[OF _ inverse]
     lpc_no_unify_rows_renamed[OF _ inverse] lpc_no_backtrack_rows_renamed lpc_no_unify_fail_rows_renamed)

lemma lpc_no_return_trace_renamed_sound:
 assumes checked: "lpc_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "\<forall>action\<in>set (map fst steps). lpc_no_return_rename_safe P p extra action"
   and scopes: "\<forall>action\<in>set (map fst steps). lpc_no_action_scope_safe rest action"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>(lp_cut_mgu_source P)\<^sup>*"
 using checked safe scopes
proof (induct steps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons entry steps)
 obtain action uu where entry: "entry=(action,uu)" by (cases entry) auto
 have local_step: "lpc_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpc_no_return_trace fuel P reserved uu steps tt"
   and local_safe: "lpc_no_return_rename_safe P p extra action"
   and tail_safe: "\<forall>action\<in>set (map fst steps). lpc_no_return_rename_safe P p extra action"
   and local_scopes: "lpc_no_action_scope_safe rest action"
   and tail_scopes: "\<forall>action\<in>set (map fst steps). lpc_no_action_scope_safe rest action"
   using Cons.prems entry by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
     lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_renamed_sound[OF local_step inverse local_safe local_scopes]]
   by (simp add: lpc_attach_answers_erases)
 show ?case using actual Cons.hyps[OF local_tail tail_safe tail_scopes] by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpc_no_return_trace_renamed_progress:
 assumes checked: "lpc_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "\<forall>action\<in>set (map fst steps). lpc_no_return_rename_safe P p extra action"
   and scopes: "\<forall>action\<in>set (map fst steps). lpc_no_action_scope_safe rest action"
   and nonempty: "steps\<noteq>[]"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>(lp_cut_mgu_source P)\<^sup>+"
proof -
 obtain action uu tail where shape: "steps=(action,uu)#tail"
   using nonempty by (cases steps) auto
 have local_step: "lpc_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpc_no_return_trace fuel P reserved uu tail tt"
   and local_safe: "lpc_no_return_rename_safe P p extra action"
   and tail_safe: "\<forall>action\<in>set (map fst tail). lpc_no_return_rename_safe P p extra action"
   and local_scopes: "lpc_no_action_scope_safe rest action"
   and tail_scopes: "\<forall>action\<in>set (map fst tail). lpc_no_action_scope_safe rest action"
   using checked safe scopes shape by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
     lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_renamed_sound[OF local_step inverse local_safe local_scopes]]
   by (simp add: lpc_attach_answers_erases)
 show ?thesis using actual lpc_no_return_trace_renamed_sound[OF local_tail inverse tail_safe tail_scopes]
   by (rule rtrancl_into_trancl2)
qed

ML \<open>
val checked = [@{thm lpc_no_backtrack_rows_renamed}, @{thm lpc_no_unify_fail_rows_renamed},
 @{thm lpc_no_return_step_renamed_sound}, @{thm lpc_no_return_trace_renamed_sound},
 @{thm lpc_no_return_trace_renamed_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted uniform renamed NO trace" else ();
\<close>
end
