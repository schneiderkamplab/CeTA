theory LP_Cut_NO_Return_Control
 imports LP_Cut_NO_Return_Check
begin

lemma lpc_attach_fresh_extension:
 assumes fresh: "lp_cut_fresh m (map fst ss)"
   and separated: "m\<notin>lpc_rest_scopes rest"
 shows "lp_cut_fresh m (lpc_attach rest ss)"
proof -
 have frame: "lp_cut_entry_scopes (lpc_attach_frame rest x) \<subseteq>
   lp_cut_entry_scopes (fst x) \<union> lpc_rest_scopes rest" for x
   by (cases x; cases "fst x") auto
 have each: "m\<notin>lp_cut_entry_scopes (lpc_attach_frame rest x)" if member: "x\<in>set ss" for x
 proof -
   have old: "m\<notin>lp_cut_entry_scopes (fst x)"
     using fresh member by (auto simp: lp_cut_fresh_def)
   show ?thesis using frame[of x] old separated by auto
 qed
 show ?thesis using each by (auto simp: lp_cut_fresh_def)
qed

lemma lpc_no_return_admin_attach_sound:
 assumes checked: "lpc_return_admin ss=Some (None,tt)"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar ss)) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar tt))"
proof -
 have evaluated: "lpc_return_admin (lpc_return_eval LPIVar ss)=
   Some (None,lpc_return_eval LPIVar tt)"
   using lpc_return_admin_map[of "\<lambda>t. lp_ieval t LPIVar" "\<lambda>ts. lpc_return_env ts LPIVar" ss]
     checked by (simp add: lpc_return_eval_def map_prod_def split_def)
 show ?thesis by (rule lpc_return_admin_attach_source[OF evaluated])
qed

lemma lpc_no_return_case_attach_sound:
 assumes fresh: "lp_cut_fresh m (LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs)#map fst saved)"
   and separated: "m\<notin>lpc_rest_scopes rest"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs),payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (map (\<lambda>c. (LPCClause (LPCAtom (Fun (LPCUser f) call_args)#gs) c m,payload))
       (lp_cut_slice P (LPCUser f) (length call_args)) @ (LPCBarrier m,payload)#saved)))"
proof -
 let ?ss = "lpc_return_eval LPIVar ((LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs),payload)#saved)"
 have evaluated: "lp_cut_fresh m (map fst ?ss)"
   using fresh by (simp add: lpc_return_eval_erases)
 have extended: "lp_cut_fresh m (lpc_attach rest ?ss)"
   by (rule lpc_attach_fresh_extension[OF evaluated separated])
 have premise: "lp_cut_fresh m (lpc_attach rest
   ((LPCGoals (LPCAtom (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t LPIVar) call_args))#
     map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs),lpc_return_env payload LPIVar)#
     lpc_return_eval LPIVar saved))"
   using extended by (simp add: lpc_return_eval_def)
 note step = lpc_return_case_attach[OF premise, of P]
 show ?thesis using step by (simp add: lpc_return_eval_def map_map o_def)
qed

lemma lpc_no_return_backtrack_attach_sound:
 assumes index: "c<length P" and clash: "lp_cut_check_clash fuel k a (fst (P!c))"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom a#gs) c m,payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar saved))"
 using lpc_answer_transition.backtrack[OF index lp_cut_check_clash_sound[OF clash, where \<eta>=LPIVar]]
 by (auto simp: lpc_return_eval_def lpc_attach_answers_def)

lemma lpc_no_return_unify_fail_attach_sound:
 assumes failure: "lp_cut_check_equality fuel a b LPCAlwaysFailure"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCUnify a b#gs),payload)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar saved))"
 using lpc_answer_transition.unify_fail[OF lp_cut_equality_failure[OF failure, where \<eta>=LPIVar]]
 by (auto simp: lpc_return_eval_def lpc_attach_answers_def)

ML \<open>
val checked = [@{thm lpc_attach_fresh_extension}, @{thm lpc_no_return_admin_attach_sound},
 @{thm lpc_no_return_case_attach_sound}, @{thm lpc_no_return_backtrack_attach_sound},
 @{thm lpc_no_return_unify_fail_attach_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware control dependency" else ();
\<close>
end
