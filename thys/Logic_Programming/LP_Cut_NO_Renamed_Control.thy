theory LP_Cut_NO_Renamed_Control
 imports LP_Cut_NO_Renamed_Unify LP_Cut_NO_Return_Control
begin

definition lpc_no_rename_rows where
 "lpc_no_rename_rows p extra ss = map
   (map_prod (lp_cut_entry_map (\<lambda>t. t\<cdot>(Var \<circ> p)))
     (\<lambda>payload. map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra)) ss"

lemma lpc_no_rename_rows_erases:
 "map fst (lpc_no_rename_rows p extra ss) =
   lp_cut_state_map (\<lambda>t. t\<cdot>(Var \<circ> p)) (map fst ss)"
 by (simp add: lpc_no_rename_rows_def lp_cut_state_map_def map_map o_def split_def)

lemma lpc_no_rename_rows_fresh:
 "lp_cut_fresh m (map fst (lpc_no_rename_rows p extra ss)) = lp_cut_fresh m (map fst ss)"
 by (simp add: lpc_no_rename_rows_erases)

lemma lpc_no_return_admin_renamed_ambient:
 assumes checked: "lpc_return_admin ss=Some (None,tt)"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))"
proof -
 have renamed: "lpc_return_admin (lpc_no_rename_rows p extra ss)=
   Some (None,lpc_no_rename_rows p extra tt)"
   by (simp add: lpc_no_rename_rows_def lpc_return_admin_map checked)
 show ?thesis by (rule lpc_no_return_admin_attach_sound[OF renamed])
qed

lemma lpc_no_return_backtrack_renamed_ambient:
 assumes index: "c<length P" and clash: "lp_cut_check_clash fuel k a (fst (P!c))"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom (a\<cdot>(Var \<circ> p))#map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs) c m,payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar saved))"
 using lpc_answer_transition.backtrack[OF index lp_cut_check_clash_sound[OF clash, where \<eta>="LPIVar \<circ> p"]]
 by (auto simp: lpc_return_eval_def lpc_attach_answers_def lp_ieval_finite_subst o_def)

lemma lpc_no_return_unify_fail_renamed_ambient:
 assumes failure: "lp_cut_check_equality fuel a b LPCAlwaysFailure"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCUnify (a\<cdot>(Var \<circ> p)) (b\<cdot>(Var \<circ> p))#
       map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs),payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar saved))"
 using lpc_answer_transition.unify_fail[OF lp_cut_equality_failure[OF failure, where \<eta>="LPIVar \<circ> p"]]
 by (auto simp: lpc_return_eval_def lpc_attach_answers_def lp_ieval_finite_subst o_def)

ML \<open>
val checked = [@{thm lpc_no_rename_rows_fresh}, @{thm lpc_no_return_admin_renamed_ambient},
 @{thm lpc_no_return_backtrack_renamed_ambient}, @{thm lpc_no_return_unify_fail_renamed_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed return controls" else ();
\<close>
end
