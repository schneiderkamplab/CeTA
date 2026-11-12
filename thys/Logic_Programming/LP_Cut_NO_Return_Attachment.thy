theory LP_Cut_NO_Return_Attachment
 imports LP_Cut_MGU_Return_Interface
begin

text \<open>Forward attachment uses a stronger, observed MGU than prefix
projection. These are steps of the existing answer-instrumented source; no
replacement operational semantics or accepting cycle rule is introduced.\<close>

lemma lpc_return_resolve_attach:
 fixes P :: "('f,string) lp_cut_program"
 assumes index: "c < length P"
   and mgu: "lpc_mgu_resolve a
     (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload)
     (fst (P!c)) (snd (P!c)) sigma rho"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,lpc_return_env payload eta)#es)) None
   (lpc_attach_answers rest
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
       (\<lambda>n. lp_isubst (lpc_return_env payload eta n) sigma))#es))"
proof -
 have full: "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
   by (rule lpc_mgu_resolve_return_continuation[OF mgu])
 note step = lpc_answer_transition.resolve[OF index full,
   of m "lpc_return_env payload eta" "lpc_attach_answers rest es"]
 show ?thesis using step
   by (simp add: lpc_attach_answers_def map_map o_def lp_cut_map_comp
     lp_ieval_subst append_assoc)
qed

lemma lpc_return_unify_attach:
 assumes mgu: "lpc_mgu_unify a b
   (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) sigma"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),lpc_return_env payload eta)#es)) None
   (lpc_attach_answers rest
     ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
       (\<lambda>n. lp_isubst (lpc_return_env payload eta n) sigma))#es))"
proof -
 have full: "lpc_mgu_unify a b
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) sigma"
   by (rule lpc_mgu_unify_return_continuation[OF mgu])
 note step = lpc_answer_transition.unify[OF full,
   of P "lpc_return_env payload eta" "lpc_attach_answers rest es"]
 show ?thesis using step
   by (simp add: lpc_attach_answers_def map_map o_def lp_cut_map_comp lp_ieval_subst)
qed

lemma lpc_return_admin_attach:
 assumes checked: "lpc_return_admin ss = Some (None,tt)"
 shows "lpc_return_admin (lpc_attach_answers rest ss) =
   Some (None,lpc_attach_answers rest tt)"
 using checked
 by (induct ss rule: lpc_return_admin.induct)
   (auto simp: lpc_attach_answers_def lpc_attach_answers_prune[unfolded lpc_attach_answers_def, symmetric]
     split: lp_cut_goal.splits)

lemma lpc_return_admin_attach_source:
 assumes checked: "lpc_return_admin ss = Some (None,tt)"
 shows "lpc_answer_transition P (lpc_attach_answers rest ss) None
   (lpc_attach_answers rest tt)"
 by (rule lpc_return_admin_sound[OF lpc_return_admin_attach[OF checked]])


lemma lpc_return_case_attach:
 assumes fresh: "lp_cut_fresh m
   (lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) call_args)#gs),eta)#es))"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) call_args)#gs),eta)#es)) None
   (lpc_attach_answers rest
     (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) call_args)#gs) c m,eta))
       (lp_cut_slice P (LPCUser f) (length call_args)) @ (LPCBarrier m,eta)#es))"
proof -
 have allocated: "lp_cut_fresh m
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) call_args)#
     gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)#
     map fst (lpc_attach_answers rest es))"
   using fresh by (simp add: lpc_attach_answers_erases)
 note step = lpc_answer_transition.case_call[OF allocated, of P eta]
 show ?thesis using step by (simp add: lpc_attach_answers_def map_map o_def)
qed

lemma lpc_return_success_not_nonreturning:
 "lpc_return_admin ((LPCGoals [],eta)#es) \<noteq> Some (None,tt)"
 by simp

lemma lpc_attached_path_source:
 assumes steps: "list_all (\<lambda>(u,v). lpc_answer_transition P
   (lpc_attach_answers rest u) None (lpc_attach_answers rest v)) (zip (s#ts) ts)"
 shows "(lpc_attach rest s,lpc_attach rest (last (s#ts))) \<in> (lp_cut_mgu_source P)\<^sup>*"
 using steps
proof (induct ts arbitrary: s)
 case Nil then show ?case by simp
next
 case (Cons t ts)
 have first: "lpc_answer_transition P (lpc_attach_answers rest s) None (lpc_attach_answers rest t)"
   using Cons.prems by simp
 have step: "(lpc_attach rest s,lpc_attach rest t) \<in> lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF first] by (simp add: lpc_attach_answers_erases)
 have tail: "(lpc_attach rest t,lpc_attach rest (last (t#ts))) \<in> (lp_cut_mgu_source P)\<^sup>*"
   by (rule Cons.hyps) (use Cons.prems in simp)
 show ?case using step tail by (auto intro: rtrancl_trans r_into_rtrancl)
qed

lemma lpc_attached_path_source_progress:
 assumes steps: "list_all (\<lambda>(u,v). lpc_answer_transition P
   (lpc_attach_answers rest u) None (lpc_attach_answers rest v)) (zip (s#t#ts) (t#ts))"
 shows "(lpc_attach rest s,lpc_attach rest (last (t#ts))) \<in> (lp_cut_mgu_source P)\<^sup>+"
proof -
 have first: "lpc_answer_transition P (lpc_attach_answers rest s) None (lpc_attach_answers rest t)"
   using steps by simp
 have step: "(lpc_attach rest s,lpc_attach rest t) \<in> lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF first] by (simp add: lpc_attach_answers_erases)
 have tail: "(lpc_attach rest t,lpc_attach rest (last (t#ts))) \<in> (lp_cut_mgu_source P)\<^sup>*"
   by (rule lpc_attached_path_source) (use steps in simp)
 show ?thesis using step tail by (rule rtrancl_into_trancl2)
qed

ML \<open>
val checked = [@{thm lpc_return_resolve_attach}, @{thm lpc_return_unify_attach}, @{thm lpc_return_admin_attach_source},
 @{thm lpc_return_case_attach}, @{thm lpc_return_success_not_nonreturning},
 @{thm lpc_attached_path_source_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted source forward attachment dependency" else ();
\<close>
end
